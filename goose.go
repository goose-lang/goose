// Package goose implements conversion from Go source to Perennial definitions.
//
// The exposed interface allows converting individual files as well as whole
// packages to a single Coq Ast with all the converted definitions, which
// include user-defined structs in Go as Coq records and a Perennial procedure
// for each Go function.
//
// See the Goose README at https://github.com/goose-lang/goose for a high-level
// overview. The source also has some design documentation at
// https://github.com/goose-lang/goose/tree/master/docs.
package goose

import (
	"fmt"
	"go/ast"
	"go/constant"
	"go/token"
	"go/types"
	"log"
	"math/big"
	"path/filepath"
	"strconv"
	"strings"

	"github.com/goose-lang/goose/declfilter"
	"github.com/goose-lang/goose/glang"
	"golang.org/x/tools/go/packages"
)

// Ctx is a context for resolving Go code's types and source code
type Ctx struct {
	namesToTranslate map[string]bool
	info             *types.Info
	pkgPath          string
	errorReporter

	// XXX: this is so we can determine the expected return type when handling a
	// `returnStmt` so the appropriate conversion is inserted
	curFuncType   *types.Signature
	defaultReturn glang.Expr // this handles

	// Should be set to true when encountering a defer statement in the body of
	// a function to communicate to its top-level funcDecl that it should
	// include a defer prelude+prologue.
	usesDefer bool

	dep *depTracker

	globalVars []*ast.Ident
	functions  []string
	namedTypes []*types.Named

	importNames        map[string]struct{}
	importNamesOrdered []string

	inits []glang.Expr

	filter declfilter.DeclFilter
}

func getFfi(pkg *packages.Package) string {
	seenFfis := make(map[string]struct{})
	packages.Visit([]*packages.Package{pkg},
		func(pkg *packages.Package) bool {
			// the dependencies of an FFI are not considered as being used; this
			// allows one FFI to be built on top of another
			if _, ok := ffiMapping[pkg.PkgPath]; ok {
				return false
			}
			return true
		},
		func(pkg *packages.Package) {
			if ffi, ok := ffiMapping[pkg.PkgPath]; ok {
				seenFfis[ffi] = struct{}{}
			}
		},
	)

	if len(seenFfis) > 1 {
		panic(fmt.Sprintf("multiple ffis used %v", seenFfis))
	}
	for ffi := range seenFfis {
		return ffi
	}
	return "none"
}

// NewPkgCtx initializes a context based on a properly loaded package
func NewPkgCtx(pkg *packages.Package, filter declfilter.DeclFilter) Ctx {
	return Ctx{
		info:          pkg.TypesInfo,
		pkgPath:       pkg.PkgPath,
		errorReporter: newErrorReporter(pkg.Fset),
		dep:           newDepTracker(),
		importNames:   make(map[string]struct{}),
		filter:        filter,
	}
}

func (ctx *Ctx) field(f *ast.Field) glang.FieldDecl {
	if len(f.Names) > 1 {
		ctx.futureWork(f, "multiple fields for same type (split them up)")
		return glang.FieldDecl{}
	}
	if len(f.Names) == 0 {
		return glang.FieldDecl{
			Name: "_",
			Type: ctx.glangTypeFromExpr(f.Type),
		}
	}
	return glang.FieldDecl{
		Name: f.Names[0].Name,
		Type: ctx.glangTypeFromExpr(f.Type),
	}
}

func (ctx *Ctx) paramList(fs *ast.FieldList) []glang.FieldDecl {
	var decls []glang.FieldDecl
	for _, f := range fs.List {
		ty := ctx.glangTypeFromExpr(f.Type)
		for _, name := range f.Names {
			decls = append(decls, glang.FieldDecl{
				Name: name.Name,
				Type: ty,
			})
		}
		if len(f.Names) == 0 { // Unnamed parameter
			decls = append(decls, glang.FieldDecl{
				Name: "",
				Type: ty,
			})
		}
	}
	return decls
}

func isAnyConstraint(expr ast.Expr) bool {
	ident, ok := expr.(*ast.Ident)
	return ok && ident.Name == "any"
}

func (ctx *Ctx) typeParamList(fs *ast.FieldList) []glang.TypeIdent {
	var typeParams []glang.TypeIdent
	if fs == nil {
		return nil
	}
	for _, f := range fs.List {
		for _, name := range f.Names {
			typeParams = append(typeParams, glang.TypeIdent(name.Name))
		}

		if !isAnyConstraint(f.Type) {
			ctx.futureWork(fs, "generic non any type")
		}

		if len(f.Names) == 0 { // Unnamed parameter
			ctx.unsupported(fs, "unnamed type parameters")
		}
	}
	return typeParams
}

func addSourceDoc(doc *ast.CommentGroup, comment *string) {
	if doc == nil {
		return
	}
	if *comment != "" {
		*comment += "\n\n"
	}
	*comment += strings.TrimSuffix(doc.Text(), "\n")
}

func (ctx *Ctx) addSourceFile(d *ast.FuncDecl, comment *string) {
	if *comment != "" {
		*comment += "\n\n"
	}
	f := ctx.fset.Position(d.Name.Pos())
	f.Filename = filepath.Base(f.Filename)
	*comment += "go: " + f.String()
}

// returns the mset for `t` followed by the mset for `ptr to t`
func (ctx *Ctx) methodSet(t *types.Named) (glang.Expr, glang.Expr) {
	typeName := t.Obj().Name()

	// Don't try to generate msets for interfaces, since Goosed code will never
	// have to call `interface.make` on it.
	if _, ok := t.Underlying().(*types.Interface); ok {
		ctx.nope(t.Obj(), "Should not generate method set for interface type")
	}

	directMethods := make(map[string]bool)
	// construct method set for T
	goMset := types.NewMethodSet(t)
	var mset glang.ListExpr
	for i := range goMset.Len() {
		selection := goMset.At(i)
		switch ctx.filter.GetAction(typeName + "." + selection.Obj().Name()) {
		case declfilter.Skip:
			continue
		}

		var expr glang.Expr
		if len(selection.Index()) > 1 {
			expr = glang.IdentExpr("$recv")
			expr = ctx.selectionMethod(false, expr, selection, t.Obj())
			expr = glang.ValueScoped{
				Value: glang.FuncLit{Args: []glang.FieldDecl{{Name: "$recv"}}, Body: expr},
			}
		} else {
			n := glang.TypeMethod(typeName, t.Method(selection.Index()[0]).Name())
			expr = glang.GallinaIdent(n)
			ctx.dep.addDep(n)
		}

		name := selection.Obj().Name()
		directMethods[name] = true
		mset = append(mset, glang.TupleExpr{glang.StringLiteral{Value: name}, expr})
	}

	// construct method set for *T
	goMsetPtr := types.NewMethodSet(types.NewPointer(t))
	var msetPtr glang.ListExpr
	for i := range goMsetPtr.Len() {
		selection := goMsetPtr.At(i)
		switch ctx.filter.GetAction(typeName + "." + selection.Obj().Name()) {
		case declfilter.Skip:
			continue
		}

		var expr glang.Expr
		if len(selection.Index()) == 1 && !directMethods[selection.Obj().Name()] {
			// FIXME: probably want expr to use `method_call` to allow proof for
			// the ptr-receiver method to use the spec for the direct method
			// call.
			n := glang.TypeMethod(typeName, t.Method(selection.Index()[0]).Name())
			expr = glang.GallinaIdent(n)
			ctx.dep.addDep(n)
		} else {
			expr = glang.IdentExpr("$recvAddr")
			expr = ctx.selectionMethod(false, expr, selection, t.Obj())
			expr = glang.ValueScoped{
				Value: glang.FuncLit{Args: []glang.FieldDecl{{Name: "$recvAddr"}}, Body: expr},
			}
		}

		name := goMsetPtr.At(i).Obj().Name()
		msetPtr = append(msetPtr, glang.TupleExpr{glang.StringLiteral{Value: name}, expr})
	}

	return mset, msetPtr
}

func (ctx *Ctx) typeDecl(spec *ast.TypeSpec) []glang.Decl {
	switch ctx.filter.GetAction(spec.Name.Name) {
	case declfilter.Axiomatize:
		return []glang.Decl{glang.AxiomDecl{
			DeclName: spec.Name.Name,
			Type:     glang.GallinaIdent("go_type"),
		}}
	case declfilter.Trust:
		if t, ok := ctx.typeOf(spec.Name).(*types.Named); ok {
			if _, ok := t.Underlying().(*types.Interface); !ok {
				ctx.namedTypes = append(ctx.namedTypes, t)
			}
		}
		return nil
	case declfilter.Translate:
		ctx.dep.setCurrentName(spec.Name.Name)
		defer ctx.dep.unsetCurrentName()
		if t, ok := ctx.typeOf(spec.Name).(*types.Named); ok {
			if _, ok := t.Underlying().(*types.Interface); !ok {
				ctx.namedTypes = append(ctx.namedTypes, t)
			}
		}
		return []glang.Decl{glang.TypeDecl{
			Name:       spec.Name.Name,
			Body:       ctx.glangTypeFromExpr(spec.Type),
			TypeParams: ctx.typeParamList(spec.TypeParams),
		}}
	default:
		return nil
	}
}

// TODO: make this the input to handleImplicitConversion?
type exprWithInfo struct {
	e glang.Expr
	t types.Type // for conversions
	n ast.Node   // for printing a location in error messages
}

func (ctx *Ctx) sliceLiteralAux(es []exprWithInfo, expectedType types.Type) glang.Expr {
	var expr glang.Expr = glang.GallinaIdent("#slice.nil")

	if len(es) > 0 {
		var sliceLitArgs []glang.Expr
		for i := 0; i < len(es); i++ {
			sliceLitArgs = append(sliceLitArgs, glang.IdentExpr(fmt.Sprintf("$sl%d", i)))
		}
		expr = glang.NewCallExpr(glang.GallinaIdent("slice.literal"),
			ctx.glangType(es[0].n, expectedType),
			glang.ListExpr(sliceLitArgs))

		for i := len(es); i > 0; i-- {
			expr = glang.LetExpr{
				Names:   []string{fmt.Sprintf("$sl%d", i-1)},
				ValExpr: ctx.handleImplicitConversion(es[i-1].n, es[i-1].t, expectedType, es[i-1].e),
				Cont:    expr,
			}
		}
		expr = glang.ParenExpr{Inner: expr}
	}
	return expr
}

func (ctx *Ctx) sliceLiteral(es []ast.Expr, expectedType types.Type) glang.Expr {
	var exprs []exprWithInfo
	for i := range len(es) {
		exprs = append(exprs, exprWithInfo{e: ctx.expr(es[i]), t: ctx.typeOf(es[i]), n: es[i]})
	}
	return ctx.sliceLiteralAux(exprs, expectedType)
}

func (ctx *Ctx) arrayLiteral(e *ast.CompositeLit, expectedType types.Type) glang.Expr {
	var arrayElements []glang.Expr

	var index int64 = 0
	for i := 0; i < len(e.Elts); i++ {
		if kve, ok := e.Elts[i].(*ast.KeyValueExpr); ok {
			elt := ctx.handleImplicitConversion(kve.Value, ctx.typeOf(kve.Value), expectedType, ctx.expr(kve.Value))
			tv := ctx.info.Types[kve.Key]
			if !tv.IsValue() {
				ctx.nope(kve.Key, "expected const as key in array literal")

			}
			switch v := constant.Val(tv.Value).(type) {
			case *big.Int:
				ctx.unsupported(kve.Key, "array literal key is probably too big")
			case int64:
				index = v
			default:
				ctx.nope(kve.Key, "array literal key with unexpected type")
			}
			if index < int64(len(arrayElements)) {
				arrayElements[index] = elt
			} else {
				for int64(len(arrayElements)) < index {
					arrayElements = append(arrayElements,
						glang.NewCallExpr(glang.GallinaIdent("zero_val"), ctx.glangType(e, expectedType)),
					)
				}
				arrayElements = append(arrayElements, elt)
			}
		} else {
			elt := ctx.handleImplicitConversion(e.Elts[i], ctx.typeOf(e.Elts[i]), expectedType, ctx.expr(e.Elts[i]))
			if index < int64(len(arrayElements)) {
				arrayElements[index] = elt
			} else {
				arrayElements = append(arrayElements, elt)
			}
		}
		index += 1
	}

	var arrayLitArgs []glang.Expr
	for i := 0; i < len(arrayElements); i++ {
		arrayLitArgs = append(arrayLitArgs, glang.IdentExpr(fmt.Sprintf("$ar%d", i)))
	}
	var expr glang.Expr = glang.NewCallExpr(glang.GallinaIdent("array.literal"),
		glang.ListExpr(arrayLitArgs))

	for i := len(arrayElements); i > 0; i-- {
		expr = glang.LetExpr{
			Names:   []string{fmt.Sprintf("$ar%d", i-1)},
			ValExpr: arrayElements[i-1],
			Cont:    expr,
		}
	}
	expr = glang.ParenExpr{Inner: expr}
	return expr
}

func (ctx *Ctx) mapLiteral(e *ast.CompositeLit, keyType, valueType types.Type) glang.Expr {
	var mapLitArgs []glang.Expr
	for i := 0; i < len(e.Elts); i++ {
		mapLitArgs = append(mapLitArgs,
			glang.TupleExpr{
				glang.IdentExpr(fmt.Sprintf("$k%d", i)),
				glang.IdentExpr(fmt.Sprintf("$v%d", i)),
			},
		)
	}
	var expr glang.Expr = glang.NewCallExpr(glang.GallinaIdent("map.literal"),
		ctx.glangType(e.Type, valueType),
		glang.ListExpr(mapLitArgs))

	for i := len(e.Elts); i > 0; i-- {
		kv := e.Elts[i-1].(*ast.KeyValueExpr)
		key := ctx.expr(kv.Key)
		value := ctx.expr(kv.Value)
		expr = glang.LetExpr{
			Names:   []string{fmt.Sprintf("$k%d", i-1)},
			ValExpr: ctx.handleImplicitConversion(kv.Key, ctx.typeOf(kv.Key), keyType, key),
			Cont:    expr,
		}
		expr = glang.LetExpr{
			Names:   []string{fmt.Sprintf("$v%d", i-1)},
			ValExpr: ctx.handleImplicitConversion(kv.Value, ctx.typeOf(kv.Value), valueType, value),
			Cont:    expr,
		}
	}
	return glang.ParenExpr{Inner: expr}
}

// Deals with the arguments, but does not actually invoke the function. That
// should be done in the continuation. The continuation can assume the arguments
// are bound to "a0", "$a1", ....
func (ctx *Ctx) callExprPrelude(call *ast.CallExpr, cont glang.Expr) (expr glang.Expr) {
	funcSig, ok := ctx.typeOf(call.Fun).Underlying().(*types.Signature)
	if !ok {
		ctx.nope(call.Fun, "function should have signature type, got %T", types.Unalias(ctx.typeOf(call.Fun)))
	}

	expr = cont

	var intermediates []exprWithInfo
	intermediatesDone := false
	// look for special case of multi-return pass through
	if len(call.Args) == 1 {
		if tupleType, ok := ctx.typeOf(call.Args[0]).(*types.Tuple); ok {
			intermediatesDone = true
			for i := range tupleType.Len() {
				intermediates = append(intermediates,
					exprWithInfo{
						e: glang.IdentExpr(fmt.Sprintf("$ret%d", i)),
						t: tupleType.At(i).Type(),
						n: call.Args[0],
					})
			}
			// destructure the inner call at the end
			defer func() {
				var names []string
				for i := range tupleType.Len() {
					names = append(names, fmt.Sprintf("$ret%d", i))
				}
				expr = glang.LetExpr{
					Names:   names,
					ValExpr: glang.ParenExpr{Inner: ctx.expr(call.Args[0])},
					Cont:    expr,
				}
			}()
		}
	}
	if !intermediatesDone {
		for i := range len(call.Args) {
			intermediates = append(intermediates,
				exprWithInfo{
					e: ctx.expr(call.Args[i]),
					t: ctx.typeOf(call.Args[i]),
					n: call.Args[i],
				})
		}
	}

	var i int = funcSig.Params().Len()
	if funcSig.Variadic() && call.Ellipsis == token.NoPos {
		// construct a slice literal for all the arguments including and after
		// the last one listed in funcSig.
		expr = glang.LetExpr{
			Names: []string{fmt.Sprintf("$a%d", i-1)},
			ValExpr: ctx.sliceLiteralAux(intermediates[i-1:],
				funcSig.Params().At(i-1).Type().(*types.Slice).Elem()),
			Cont: expr,
		}
		i--
	}
	for ; i > 0; i-- {
		expr = glang.LetExpr{
			Names: []string{fmt.Sprintf("$a%d", i-1)},
			ValExpr: ctx.handleImplicitConversion(intermediates[i-1].n,
				intermediates[i-1].t, funcSig.Params().At(i-1).Type(), intermediates[i-1].e),
			Cont: expr,
		}
	}
	return
}

// integerConversion generates an expression for converting x to an integer
// of a specific width
//
// s is only used for error reporting
func (ctx *Ctx) integerConversion(s ast.Node, x ast.Expr, width int) glang.Expr {
	if info, ok := getIntegerType(ctx.typeOf(x)); ok {
		if info.isUntyped {
			ctx.todo(s, "integer conversion from untyped int to uint64")
		}
		if info.width == width {
			return ctx.expr(x)
		}
		return glang.NewCallExpr(glang.GallinaIdent(fmt.Sprintf("to_u%d", width)),
			ctx.expr(x))
	}
	ctx.unsupported(s, "casts from unsupported type %v to uint%d",
		ctx.typeOf(x), width)
	return nil
}

func (ctx *Ctx) conversionExpr(s *ast.CallExpr) glang.Expr {
	if len(s.Args) != 1 {
		ctx.nope(s, "expect exactly one argument in a conversion")
	}
	toType := ctx.info.TypeOf(s.Fun).Underlying()
	fromType := ctx.info.TypeOf(s.Args[0]).Underlying()
	if types.Identical(toType, fromType) {
		return ctx.expr(s.Args[0])
	}
	switch toType := toType.(type) {
	case *types.Basic:
		// handle conversions between integer types
		if fromType, ok := fromType.(*types.Basic); ok {
			if (fromType.Info()&types.IsInteger) != 0 &&
				toType.Info()&types.IsInteger == 0 {
				ctx.unsupported(s, "converting from integer type to non-integer type")
			}
			switch toType.Kind() {
			// XXX: int is treated as a 64 bit word
			case types.Uint, types.Int, types.Uint64, types.Int64:
				return ctx.integerConversion(s, s.Args[0], 64)
			case types.Int32, types.Uint32:
				return ctx.integerConversion(s, s.Args[0], 32)
			case types.Int8, types.Uint8:
				return ctx.integerConversion(s, s.Args[0], 8)
			}
		}

		// handle `string(b)`, where b : []byte
		if toType.Kind() == types.String && isByteSlice(fromType) {
			return glang.NewCallExpr(glang.GallinaIdent("string.from_bytes"), ctx.expr(s.Args[0]))
		}
	case *types.Slice:
		// handle `[]byte(s)`, where s : string
		if eltType, ok := toType.Elem().Underlying().(*types.Basic); ok &&
			eltType.Kind() == types.Byte && isString(fromType) {
			return glang.NewCallExpr(glang.GallinaIdent("string.to_bytes"), ctx.expr(s.Args[0]))
		}
	}

	return ctx.handleImplicitConversion(s, fromType, toType, ctx.expr(s.Args[0]))
	// ctx.unsupported(s, "explicit conversion from %s to %s", fromType, toType)
	// return nil
}

// This handles:
// - make() and new() because they uniquely take a type as a normal parameter.
// - array len() and cap() because they are untyped functions
func (ctx *Ctx) maybeHandleSpecialBuiltin(s *ast.CallExpr) (glang.Expr, bool) {
	if !ctx.info.Types[s.Fun].IsBuiltin() {
		return nil, false
	}

	f, ok := s.Fun.(*ast.Ident)
	if !ok {
		ctx.unsupported(s.Fun, "builtin that isn't an ident")
	}

	switch f.Name {
	case "make":
		sig := ctx.typeOf(s.Fun).(*types.Signature)
		switch ty := sig.Params().At(0).Type().Underlying().(type) {
		case *types.Slice:
			elt := ctx.glangType(s.Fun, ty.Elem())
			switch sig.Params().Len() {
			case 2:
				return glang.NewCallExpr(glang.GallinaIdent("slice.make2"), elt,
					ctx.expr(s.Args[1])), true
			case 3:
				return glang.NewCallExpr(glang.GallinaIdent("slice.make3"), elt,
					ctx.expr(s.Args[1]), ctx.expr(s.Args[2])), true
			default:
				ctx.nope(s, "Too many or too few arguments in slice construction")
				return glang.CallExpr{}, true
			}
		case *types.Map:
			return glang.NewCallExpr(glang.GallinaIdent("map.make"),
				ctx.glangType(s.Args[0], ty.Key()),
				ctx.glangType(s.Args[0], ty.Elem()),
				glang.UnitLiteral{}), true
		case *types.Chan:
			return glang.NewCallExpr(glang.GallinaIdent("chan.make"),
				ctx.glangType(s.Args[0], ty.Elem()),
				glang.UnitLiteral{}), true
		default:
			ctx.unsupported(s, "make should be slice or map, got %v", ty)
		}
	case "new":
		sig := ctx.typeOf(s.Fun).(*types.Signature)
		ty := ctx.glangType(s.Args[0], sig.Params().At(0).Type())
		return glang.RefExpr{
			X:  glang.NewCallExpr(glang.GallinaIdent("zero_val"), ty),
			Ty: ty,
		}, true
	case "len", "cap":
		if _, ok := ctx.typeOf(s.Fun).(*types.Signature); ok {
			return nil, false
		}
		name := s.Fun.(*ast.Ident).Name
		return glang.NewCallExpr(glang.GallinaIdent(fmt.Sprintf("array.%s", name)),
			ctx.glangType(s, ctx.typeOf(s.Args[0]))), true
	}

	return nil, false
}

func (ctx *Ctx) getNumParams(e ast.Expr) int {
	funcSig, ok := ctx.typeOf(e).Underlying().(*types.Signature)
	if !ok {
		ctx.nope(e, "function should have signature type, got %T", types.Unalias(ctx.typeOf(e)))
	}
	return funcSig.Params().Len()
}

func (ctx *Ctx) callExpr(s *ast.CallExpr) glang.Expr {
	if ctx.info.Types[s.Fun].IsType() {
		return ctx.conversionExpr(s)
	} else if e, ok := ctx.maybeHandleSpecialBuiltin(s); ok {
		return e
	} else {
		var args []glang.Expr
		for i := range ctx.getNumParams(s.Fun) {
			args = append(args, glang.IdentExpr(fmt.Sprintf("$a%d", i)))
		}
		return ctx.callExprPrelude(s, glang.NewCallExpr(ctx.expr(s.Fun), args...))
	}
}

func (ctx *Ctx) qualifiedName(obj types.Object) string {
	name := obj.Name()
	if obj.Pkg() == nil {
		return name
	} else if ctx.pkgPath == obj.Pkg().Path() {
		// no module name needed
		return name
	}
	return fmt.Sprintf("%s.%s", obj.Pkg().Name(), name)
}

func (ctx *Ctx) getPkgAndName(obj types.Object) (pkg string, name string) {
	name = obj.Name()
	pkg = "pkg_name'"
	if obj.Pkg() == nil || ctx.pkgPath == obj.Pkg().Path() {
		return
	}
	pkg = obj.Pkg().Name() + "." + pkg
	return
}

func (ctx *Ctx) selectorExprAddr(e *ast.SelectorExpr) glang.Expr {
	selection := ctx.info.Selections[e]
	if selection == nil {
		pkg, ok := getIdent(e.X)
		if !ok {
			ctx.unsupported(e, "expected package selector with idtent, got %T", e.X)
		}
		if _, ok := ctx.info.ObjectOf(e.Sel).(*types.Var); ok {
			ctx.dep.addDep("pkg_name'")
			return glang.NewCallExpr(glang.GallinaIdent("globals.get"),
				glang.StringVal{Value: glang.GallinaIdent(pkg + ".pkg_name'")},
				glang.StringVal{Value: glang.StringLiteral{Value: e.Sel.Name}},
			)
		} else {
			ctx.unsupported(e, "address of external package selection that is not a variable")
		}
	}

	switch selection.Kind() {
	case types.FieldVal:
		if ctx.info.Types[e.X].Addressable() {
			expr, curType, index := ctx.exprAddr(e.X), selection.Recv(), selection.Index()
			ctx.fieldAddrSelection(e, index, &curType, &expr)
			return expr
		} else {
			expr, curType, index := ctx.expr(e.X), selection.Recv(), selection.Index()
			ctx.fieldSelection(e.X, &index, &curType, &expr)
			if len(index) == 0 {
				ctx.nope(e, "expected addressable expression")
			}
			ctx.fieldAddrSelection(e.X, index, &curType, &expr)
			return expr
		}
	case types.MethodVal:
		ctx.nope(e, "method val is not addressable")
	case types.MethodExpr:
		ctx.nope(e, "method expr is not addressable")
	}
	ctx.nope(e, "unexpected kinf of selection")
	panic("unreachable")
}

// Requires that `old(expr) : old(curType)` and that `old(curType)` be a struct
// type. This walks down the selection specified by `index` up until it sees a
// pointer field, then returns. Its intent is to be combined with
// fieldAddrSelection to go the rest of the way.
//
// If len(index) > 0, then `expr : ptr<curType>`.
// If len(index) == 0, then `expr : curType`.
func (ctx *Ctx) fieldSelection(n locatable, index *[]int, curType *types.Type, expr *glang.Expr) {
	for ; len(*index) > 0; *index = (*index)[1:] {
		i := (*index)[0]
		info, ok := ctx.getStructInfo(*curType)
		if !ok {
			ctx.nope(n, "expected (pointer to) struct type for base of selector, got %s", *curType)
		}

		if info.throughPointer {
			// XXX: this is to feed into fieldAddrSelection (see comment above this func).
			*curType = (*curType).(*types.Pointer).Elem()
			return
		}
		v := info.structType.Field(i)
		*expr = glang.NewCallExpr(glang.GallinaIdent("struct.field_get"),
			ctx.structInfoToGlangType(info), glang.GallinaString(v.Name()), *expr)
		*curType = v.Type()
	}
	return
}

// Requires `old(expr) : ptr<old(curType)>`.
// This walks down the selection specified by `index` all the way to the end,
// returning an expression representing the address of that selected field.
func (ctx *Ctx) fieldAddrSelection(n locatable, index []int, curType *types.Type, expr *glang.Expr) {
	for _, i := range index {
		info, ok := ctx.getStructInfo(*curType)
		if !ok {
			if _, ok := (*curType).(*types.Struct); ok {
				ctx.unsupported(n, "anonymous struct")
			}
			ctx.nope(n, "expected (pointer to) struct type for base of selector, got %s", *curType)
		}
		if info.throughPointer {
			*expr = glang.DerefExpr{X: *expr, Ty: ctx.glangType(n, *curType)}
		}
		v := info.structType.Field(i)

		*expr = glang.NewCallExpr(glang.GallinaIdent("struct.field_ref"),
			ctx.structInfoToGlangType(info), glang.GallinaString(v.Name()), *expr)
		*curType = v.Type()
	}
	return
}

// requires `!addressable -> (expr : selection.Recv())`
// requires `addressable -> (expr : ptr<selection.Recv()>)`
func (ctx *Ctx) selectionMethod(addressable bool, expr glang.Expr,
	selection *types.Selection, l locatable) glang.Expr {

	index, curType := selection.Index(), selection.Recv()
	fnIndex, index := index[len(index)-1], index[:len(index)-1]

	if !addressable {
		ctx.fieldSelection(l, &index, &curType, &expr)
	}
	if addressable || len(index) > 0 {
		ctx.fieldAddrSelection(l, index, &curType, &expr)
		// expr : ptrT<curType>
		if _, ok := types.Unalias(curType).(*types.Pointer); ok {
			expr = glang.DerefExpr{X: expr, Ty: ctx.glangType(l, curType)}
		} else {
			curType = types.NewPointer(curType)
		}
	}
	// now, (expr : curType), and there's no deref unless it's unavoidale.

	// At this point, (expr : curType), and (curType = ptr<named>) if the
	// original expression is an address or is addressable, and (curType =
	// named) otherwise.
	if info, ok := ctx.getInterfaceInfo(curType); ok {
		if info.throughPointer {
			expr = glang.DerefExpr{X: expr, Ty: ctx.glangType(l, curType.(*types.Pointer).Elem())}
		}
		return glang.NewCallExpr(glang.GallinaIdent("interface.get"),
			glang.GallinaString(info.interfaceType.Method(fnIndex).Name()), expr,
		)
	}

	if pointerT, ok := types.Unalias(curType).(*types.Pointer); ok {
		t, ok := types.Unalias(pointerT.Elem()).(*types.Named)
		if !ok {
			ctx.nope(l, "methods can only be called on a pointer if the base type is a defined type, not %s", pointerT.Elem())
		}

		funcSig, ok := t.Method(fnIndex).Type().(*types.Signature)
		if !ok {
			ctx.nope(l, "func should have signature type, got %s", t.Method(fnIndex).Type())
		}

		methodName := t.Method(fnIndex).Name()
		if _, ok := types.Unalias(funcSig.Recv().Type()).(*types.Pointer); ok {
			pkgName, typeName := ctx.getPkgAndName(t.Obj())
			ctx.dep.addDep(pkgName)
			ctx.dep.addDep(typeName)

			return glang.NewCallExpr(glang.GallinaIdent("method_call"),
				glang.StringVal{Value: glang.GallinaIdent(pkgName)},
				glang.StringVal{Value: glang.GallinaString(typeName + "'ptr")},
				glang.StringVal{Value: glang.GallinaString(methodName)},
				expr,
			)
		} else {
			pkgName, typeName := ctx.getPkgAndName(t.Obj())
			ctx.dep.addDep(pkgName)
			ctx.dep.addDep(typeName)

			return glang.NewCallExpr(glang.GallinaIdent("method_call"),
				glang.StringVal{Value: glang.GallinaIdent(pkgName)},
				glang.StringVal{Value: glang.GallinaString(typeName)},
				glang.StringVal{Value: glang.GallinaString(methodName)},
				glang.DerefExpr{X: expr, Ty: ctx.glangType(l, t)},
			)
		}
	} else if t, ok := types.Unalias(curType).(*types.Named); ok {
		methodName := t.Method(fnIndex).Name()

		funcSig, ok := t.Method(fnIndex).Type().(*types.Signature)
		if !ok {
			ctx.nope(l, "func should have signature type, got %s", t.Method(fnIndex).Type())
		}

		if _, ok := types.Unalias(funcSig.Recv().Type()).(*types.Pointer); ok {
			ctx.nope(l, "receiver of method must be pointer, but selectorExpr has non-addressable base")
		} else {
			pkgName, typeName := ctx.getPkgAndName(t.Obj())
			ctx.dep.addDep(pkgName)
			ctx.dep.addDep(typeName)
			return glang.NewCallExpr(glang.GallinaIdent("method_call"),
				glang.StringVal{Value: glang.GallinaIdent(pkgName)},
				glang.StringVal{Value: glang.GallinaString(typeName)},
				glang.StringVal{Value: glang.GallinaString(methodName)},
				glang.GallinaString(methodName),
				glang.Tt,
				expr,
			)
		}
	}
	ctx.nope(l, "methods can only be called on (pointers to) defined types, not %s", curType)
	return nil
}

func (ctx *Ctx) selectorExpr(e *ast.SelectorExpr) glang.Expr {
	selection := ctx.info.Selections[e]
	if selection == nil {
		if _, ok := ctx.info.ObjectOf(e.Sel).(*types.Var); ok {
			ctx.nope(e, "global variable from external package should be handled by exprAddr")
			// return glang.IdentExpr(fmt.Sprintf("global:%s", e.Sel.Name))
		} else if f, ok := ctx.info.ObjectOf(e.Sel).(*types.Func); ok {
			return ctx.handleImplicitConversion(e,
				ctx.info.TypeOf(e.Sel),
				ctx.info.TypeOf(e),
				glang.NewCallExpr(
					glang.GallinaIdent("func_call"),
					glang.StringVal{Value: glang.GallinaIdent(f.Pkg().Name() + ".pkg_name'")},
					glang.StringVal{Value: glang.StringLiteral{Value: e.Sel.Name}},
				),
			)
		} else {
			return ctx.handleImplicitConversion(e,
				ctx.info.TypeOf(e.Sel),
				ctx.info.TypeOf(e),
				glang.PackageIdent{
					Package: ctx.info.ObjectOf(e.Sel).Pkg().Name(),
					Ident:   e.Sel.Name,
				},
			)
		}
	}

	switch selection.Kind() {
	case types.MethodExpr:
		ctx.unsupported(e, "method expr")
	case types.FieldVal:
		var expr glang.Expr
		index, curType := selection.Index(), selection.Recv()

		if ctx.info.Types[e.X].Addressable() {
			expr = ctx.exprAddr(e.X)
		} else {
			expr = ctx.expr(e.X)
			ctx.fieldSelection(e.X, &index, &curType, &expr)
		}
		if len(index) > 0 {
			ctx.fieldAddrSelection(e.X, index, &curType, &expr)
			expr = glang.DerefExpr{X: expr, Ty: ctx.glangType(e.Sel, curType)}
		}
		return expr

	case types.MethodVal:
		// 2*2 cases: receiver type could be (T) or (*T), and e.X type
		// (including embedded fields) could be (T) or (*T).

		if ctx.info.Types[e.X].Addressable() {
			return ctx.selectionMethod(true, ctx.exprAddr(e.X), selection, e)
		} else {
			return ctx.selectionMethod(false, ctx.expr(e.X), selection, e)
		}
	}

	panic("unreachable")
}

func (ctx *Ctx) compositeLiteral(e *ast.CompositeLit) glang.Expr {
	if t, ok := ctx.typeOf(e).Underlying().(*types.Slice); ok {
		return ctx.sliceLiteral(e.Elts, t.Elem())
	} else if t, ok := ctx.typeOf(e).Underlying().(*types.Array); ok {
		return ctx.arrayLiteral(e, t.Elem())
	} else if t, ok := ctx.typeOf(e).Underlying().(*types.Map); ok {
		return ctx.mapLiteral(e, t.Key(), t.Elem())
	}
	if structType, ok := ctx.typeOf(e).Underlying().(*types.Struct); ok {
		return ctx.structLiteral(ctx.typeOf(e), structType, e)
	}
	ctx.unsupported(e, "composite literal of type %v", ctx.typeOf(e))
	return nil
}

func (ctx *Ctx) structLiteral(t types.Type, structType *types.Struct, e *ast.CompositeLit) glang.Expr {
	lit := glang.StructLiteral{StructType: ctx.glangType(e.Type, t)}
	isUnkeyedStruct := false

	for _, el := range e.Elts {
		switch el.(type) {
		case *ast.KeyValueExpr:
		default:
			isUnkeyedStruct = true
			break
		}
	}
	if isUnkeyedStruct {
		if len(e.Elts) != structType.NumFields() {
			ctx.nope(e, "expected as many elements are there are struct fields in unkeyed literal")
		}
		for i := range structType.NumFields() {
			lit.AddField(structType.Field(i).Name(),
				ctx.handleImplicitConversion(e.Elts[i],
					ctx.typeOf(e.Elts[i]),
					structType.Field(i).Type(),
					ctx.expr(e.Elts[i]),
				))
		}
		return lit
	}

	for i := 0; i < structType.NumFields(); i++ {
		fieldName := structType.Field(i).Name()
		fieldType := structType.Field(i).Type()

		fieldIsZero := true
		for _, el := range e.Elts {
			switch el := el.(type) {
			case *ast.KeyValueExpr:
				ident, ok := getIdent(el.Key)
				if !ok {
					ctx.noExample(el.Key, "struct field keyed by non-identifier %+v", el.Key)
				}
				if ident == fieldName {
					fieldIsZero = false
					lit.AddField(fieldName, glang.IdentExpr("$"+fieldName))
				}
			default:
			}
		}
		if fieldIsZero {
			lit.AddField(fieldName, glang.NewCallExpr(glang.GallinaIdent("zero_val"), ctx.glangType(e, fieldType)))
		}
	}

	getFieldType := func(fieldName string) types.Type {
		for i := range structType.NumFields() {
			if structType.Field(i).Name() == fieldName {
				return structType.Field(i).Type()
			}
		}
		ctx.nope(e, "field is not a part of the struct")
		return types.NewTuple()
	}

	var expr glang.Expr = lit
	for i := range e.Elts {
		el := e.Elts[len(e.Elts)-1-i].(*ast.KeyValueExpr)
		fieldName, _ := getIdent(el.Key)
		expr = glang.LetExpr{
			Names: []string{"$" + fieldName},
			// convert from the original value type
			ValExpr: ctx.handleImplicitConversion(el.Value,
				ctx.typeOf(el.Value),
				getFieldType(fieldName),
				ctx.expr(el.Value)),
			Cont: expr,
		}
	}
	return expr
}

func (ctx *Ctx) basicLiteral(e *ast.BasicLit) glang.Expr {
	tv := ctx.info.Types[e]
	if tv.Value == nil {
		ctx.nope(e, "basic literal should have a const val")
	}
	t, v := ctx.constantLiteral(e, tv.Value)
	return ctx.handleImplicitConversion(e, t, tv.Type, v)
}

func (ctx *Ctx) isNilCompareExpr(e *ast.BinaryExpr) bool {
	if !(e.Op == token.EQL || e.Op == token.NEQ) {
		return false
	}
	return ctx.info.Types[e.Y].IsNil()
}

func (ctx *Ctx) typeJoin(n ast.Node, t1, t2 types.Type) types.Type {
	if types.AssignableTo(t1, t2) {
		return t2
	} else if types.AssignableTo(t2, t1) {
		return t1
	} else {
		ctx.nope(n, "comparison between non-assignable types")
		return nil
	}
}

func (ctx *Ctx) binExpr(e *ast.BinaryExpr) (expr glang.Expr) {
	// XXX: according to the Go spec, comparisons can occur between types that
	// are "assignable" to one another. This may require a conversion, so we
	// here convert to the appropriate type here.
	//
	// XXX: this also handles converting untyped constants to a typed constant
	xT, yT := ctx.typeOf(e.X), ctx.typeOf(e.Y)
	compType := ctx.typeJoin(e, xT, yT).Underlying()
	var op glang.BinOp = -1
	if t, ok := compType.(*types.Basic); ok {
		switch t.Kind() {
		case types.UntypedInt:
			op, ok = untypedIntOps[e.Op]
			if !ok {
				// use const
				tv := ctx.info.Types[e]
				if tv.Value == nil {
					ctx.nope(e, "untyped integer expression without constant value")
				}
				t, v := ctx.constantLiteral(e, tv.Value)
				return ctx.handleImplicitConversion(e, t, tv.Type, v)
			}
			switch op {
			case glang.OpEqualsZ, glang.OpLessThanZ, glang.OpLessEqZ, glang.OpGreaterThanZ, glang.OpGreaterEqZ:
				defer func() {
					expr = glang.BoolVal{Value: expr}
				}()
			case glang.OpNotEquals:
				op = glang.OpEqualsZ
				defer func() {
					expr = glang.BoolVal{Value: glang.GallinaNotExpr{X: expr}}
				}()
			}
		case types.Uint, types.Uint64, types.Uint32, types.Uint16, types.Uint8:
			op, ok = unsignedIntOps[e.Op]
			if !ok {
				ctx.unsupported(e, "unsupported binary operation on unsigned integers")
			}
		case types.Int, types.Int64, types.Int32, types.Int16, types.Int8:
			op, ok = signedIntOps[e.Op]
			if !ok {
				fn, ok := signedIntFns[e.Op]
				if !ok {
					ctx.unsupported(e, "unsupported binary operation on signed integers")
				}
				return glang.NewCallExpr(fn, ctx.handleImplicitConversion(e.X, xT, compType, ctx.expr(e.X)),
					ctx.handleImplicitConversion(e.Y, yT, compType, ctx.expr(e.Y)))
			}
		case types.UntypedBool, types.Bool:
			op, ok = boolOps[e.Op]
			if !ok {
				ctx.unsupported(e, "unsupported binary operation on booleans")
			}
		case types.String:
			op, ok = stringOps[e.Op]
			if !ok {
				ctx.unsupported(e, "unsupported binary operation on strings")
			}
		case types.UntypedString:
			op, ok = untypedStringOps[e.Op]
			switch op {
			case glang.OpGallinaAppend:
				defer func() {
					expr = ctx.handleImplicitConversion(e, compType, ctx.typeOf(e), expr)
				}()
			}
			if !ok {
				ctx.unsupported(e, "unsupported binary operation on strings")
			}
		}
		if (t.Info() & types.IsInteger) != 0 {
			switch op {
			case glang.OpMinus, glang.OpMul, glang.OpRem, glang.OpPlus, glang.OpQuot:
				defer func() {
					expr = ctx.handleImplicitConversion(e, compType, ctx.typeOf(e), expr)
				}()
			}
		}
	} else {
		op, ok = generalOps[e.Op]
		if !ok {
			ctx.unsupported(e, "binary operation on general type")
		}
	}
	if op == -1 {
		ctx.unsupported(e, "unknown op")
	}

	expr = glang.BinaryExpr{
		X:  ctx.handleImplicitConversion(e.X, xT, compType, ctx.expr(e.X)),
		Op: op,
		Y:  ctx.handleImplicitConversion(e.Y, yT, compType, ctx.expr(e.Y)),
	}

	return expr
}

func (ctx *Ctx) sliceExpr(e *ast.SliceExpr) glang.Expr {
	if t, ok := ctx.typeOf(e.X).Underlying().(*types.Slice); ok {
		var lowExpr glang.Expr = glang.Int64Val{Value: glang.ZLiteral{Value: big.NewInt(0)}}
		var highExpr glang.Expr = glang.NewCallExpr(glang.GallinaIdent("slice.len"), glang.IdentExpr("$s"))
		x := ctx.expr(e.X)

		if e.Low != nil {
			lowExpr = ctx.expr(e.Low)
		}
		if e.High != nil {
			highExpr = ctx.expr(e.High)
		}
		if e.Max != nil {
			highExpr = ctx.expr(e.High)
			return glang.LetExpr{
				Names:   []string{"$s"},
				ValExpr: x,
				Cont: glang.NewCallExpr(glang.GallinaIdent("slice.full_slice"),
					ctx.glangType(e, t.Elem()),
					glang.IdentExpr("$s"), lowExpr, highExpr, ctx.expr(e.Max)),
			}
		} else {
			return glang.LetExpr{
				Names:   []string{"$s"},
				ValExpr: x,
				Cont: glang.NewCallExpr(glang.GallinaIdent("slice.slice"),
					ctx.glangType(e, t.Elem()),
					glang.IdentExpr("$s"), lowExpr, highExpr),
			}
		}
	} else if _, ok := ctx.typeOf(e.X).Underlying().(*types.Array); ok {
		var lowExpr glang.Expr = glang.Int64Val{Value: glang.ZLiteral{Value: big.NewInt(0)}}
		var highExpr glang.Expr = glang.NewCallExpr(glang.GallinaIdent("array.len"), ctx.glangType(e.X, ctx.typeOf(e.X)))
		if e.Low != nil {
			lowExpr = ctx.expr(e.Low)
		}
		if e.High != nil {
			highExpr = ctx.expr(e.High)
		}
		if e.Max != nil {
			ctx.unsupported(e, "full slice of array")
		} else {
			return glang.LetExpr{
				Names:   []string{"$a"},
				ValExpr: ctx.exprAddr(e.X),
				Cont: glang.NewCallExpr(glang.GallinaIdent("array.slice"),
					glang.IdentExpr("$a"), lowExpr, highExpr),
			}
		}
	} else {
		ctx.unsupported(e, "taking a slice of an object with type %s", ctx.typeOf(e.X))
	}
	return nil
}

func (ctx *Ctx) nilExpr(e *ast.Ident) glang.Expr {
	t := ctx.typeOf(e)
	switch t.(type) {
	case *types.Basic:
		// TODO: this gets triggered for all of our unit tests because the
		//  nil identifier is mapped to an untyped nil object.
		//  This seems wrong; the runtime representation of each of these
		//  uses depends on the type, so Go must know how they're being used.
		return glang.GallinaIdent("BUG: this should get overwritten by handleImplicitConversion")
	default:
		ctx.unsupported(e, "nil of type %v (not pointer or slice)", t)
		return nil
	}
}

func (ctx *Ctx) unaryExpr(e *ast.UnaryExpr, isSpecial bool) glang.Expr {
	if e.Op == token.NOT {
		return glang.NotExpr{X: ctx.expr(e.X)}
	}
	if e.Op == token.XOR {
		return glang.NotExpr{X: ctx.expr(e.X)}
	}
	if e.Op == token.AND {
		if x, ok := e.X.(*ast.IndexExpr); ok {
			// e is &a[b] where x is a.b
			if xTy, ok := ctx.typeOf(x.X).(*types.Slice); ok {
				return glang.NewCallExpr(glang.GallinaIdent("slice.elem_ref"),
					ctx.glangType(e, xTy.Elem()),
					ctx.expr(x.X), ctx.expr(x.Index))
			}
		}
		if info, ok := ctx.getStructInfo(ctx.typeOf(e.X)); ok {
			structLit, ok := e.X.(*ast.CompositeLit)
			if ok {
				// e is &s{...} (a struct literal)
				sl := ctx.structLiteral(ctx.typeOf(e.X), info.structType, structLit)
				return glang.RefExpr{
					X:  sl,
					Ty: ctx.glangType(e.X, ctx.typeOf(e.X)),
				}
			}
		}
		// e is something else
		return ctx.exprAddr(e.X)
	}
	if e.Op == token.ARROW {
		var expr glang.Expr = glang.NewCallExpr(glang.GallinaIdent("chan.receive"), ctx.expr(e.X))
		if !isSpecial {
			expr = glang.NewCallExpr(glang.GallinaIdent("Fst"), expr)
		}
		return expr
	}
	if e.Op == token.SUB {
		return glang.NewCallExpr(glang.GallinaIdent("int_negative"), ctx.expr(e.X))
	}
	ctx.unsupported(e, "unary expression %s", e.Op)
	return nil
}

func (ctx *Ctx) variable(s *ast.Ident) glang.Expr {
	if _, ok := ctx.info.Uses[s].(*types.Const); ok {
		ctx.dep.addDep(s.Name)
		return glang.GallinaIdent(s.Name)
	}
	return glang.DerefExpr{X: glang.IdentExpr(s.Name), Ty: ctx.glangType(s, ctx.typeOf(s))}
}

func (ctx *Ctx) function(s *ast.Ident) glang.Expr {
	ctx.dep.addDep("pkg_name'")

	typeArgs := ctx.info.Instances[s].TypeArgs
	if typeArgs.Len() == 0 {
		return glang.NewCallExpr(glang.GallinaIdent("func_call"),
			glang.StringVal{Value: glang.GallinaIdent("pkg_name'")},
			glang.StringVal{Value: glang.StringLiteral{Value: s.Name}},
		)
	}
	return glang.CallExpr{
		MethodName: glang.GallinaIdent(s.Name),
		Args:       ctx.convertTypeArgsToGlang(nil, typeArgs),
	}
}

func (ctx *Ctx) goBuiltin(e *ast.Ident) bool {
	s, ok := ctx.info.Uses[e]
	if !ok {
		return false
	}
	return s.Parent() == types.Universe
}

func (ctx *Ctx) builtinIdent(e *ast.Ident) glang.Expr {
	switch e.Name {
	case "nil":
		return ctx.nilExpr(e)
	case "true":
		return glang.True
	case "false":
		return glang.False
	case "append":
		sig := ctx.typeOf(e).(*types.Signature)
		t := sig.Params().At(1).Type()
		return glang.NewCallExpr(glang.GallinaIdent("slice.append"),
			ctx.glangType(e, t),
		)
	case "new":
		sig := ctx.typeOf(e).(*types.Signature)
		ctx.todo(e, "new might be better as its own function")
		t := ctx.glangType(e, sig.Params().At(0).Type())
		return glang.RefExpr{
			X:  glang.NewCallExpr(glang.GallinaIdent("zero_val"), t),
			Ty: t,
		}
	case "len":
		sig := ctx.typeOf(e).(*types.Signature)
		switch ty := sig.Params().At(0).Type().Underlying().(type) {
		case *types.Slice:
			return glang.GallinaIdent("slice.len")
		case *types.Map:
			return glang.GallinaIdent("map.len")
		case *types.Basic:
			if ty.Kind() == types.String {
				return glang.GallinaIdent("StringLength")
			}
		case *types.Chan:
			return glang.GallinaIdent("chan.len")
		default:
			ctx.unsupported(e, "length of object of type %v", ty)
		}
	case "cap":
		sig := ctx.typeOf(e).(*types.Signature)
		switch ty := sig.Params().At(0).Type().Underlying().(type) {
		case *types.Slice:
			return glang.GallinaIdent("slice.cap")
		case *types.Chan:
			return glang.GallinaIdent("chan.cap")
		default:
			ctx.unsupported(e, "capacity of object of type %v", ty)
		}
	case "copy":
		sig := ctx.typeOf(e).(*types.Signature)
		switch ty := sig.Params().At(0).Type().Underlying().(type) {
		case *types.Slice:
			fromTy := sig.Params().At(1).Type().Underlying()
			if types.Identical(ty, fromTy) {
				return glang.NewCallExpr(
					glang.GallinaIdent("slice.copy"),
					ctx.glangType(e, ty.Elem()),
				)
			}
			ctx.unsupported(e, "copy to %v from %v", ty, fromTy)
		default:
			ctx.nope(e, "copy of object of type %v", ty)
		}
	case "delete":
		sig := ctx.typeOf(e).(*types.Signature)
		if _, ok := sig.Params().At(0).Type().Underlying().(*types.Map); !ok {
			ctx.nope(e, "delete on non-map")
		}
		return glang.GallinaIdent("map.delete")
	case "panic":
		return glang.GallinaIdent("Panic")
	case "min", "max":
		sig := ctx.typeOf(e).(*types.Signature)
		if sig.Params().Len() == 0 {
			ctx.nope(e, "min/max with no params")
		}
		// figure out the desired type by taking a type join of everything.
		// XXX: the signature might always be (T, T, T, T, T).
		var t types.Type = sig.Params().At(0).Type().Underlying()
		for i := 0; i < sig.Params().Len(); i++ {
			t = ctx.typeJoin(e, t, sig.Params().At(i).Type())
		}
		if types.Identical(t, types.Typ[types.Uint64]) {
			return glang.NewCallExpr(glang.GallinaIdent(fmt.Sprintf("%sUint64", e.Name)),
				glang.GallinaIdent(fmt.Sprintf("%d", sig.Params().Len())))
		}
		ctx.unsupported(e, "%s with final type %v", e.Name, t)
	case "close":
		return glang.GallinaIdent("chan.close")
	case "iota":
		o := ctx.info.ObjectOf(e)
		t, v := ctx.constantLiteral(e, o.(*types.Const).Val())
		return ctx.handleImplicitConversion(e, t, ctx.typeOf(e), v)
	default:
		ctx.unsupported(e, "builtin identifier of type %v", ctx.typeOf(e))
	}
	return nil
}

func (ctx *Ctx) identExpr(e *ast.Ident, isSpecial bool) glang.Expr {
	// XXX: special case for a manually constructed Ident from select recv clause
	if len(e.Name) > 0 && e.Name[0] == '$' {
		var expr glang.Expr = glang.IdentExpr(e.Name)
		if !isSpecial {
			expr = glang.NewCallExpr(glang.GallinaIdent("Fst"), expr)
		}
		return expr
	}

	if ctx.goBuiltin(e) {
		return ctx.builtinIdent(e)
	}

	// check if e refers to a variable,
	obj := ctx.info.ObjectOf(e)
	if constObj, ok := obj.(*types.Const); ok {
		// is a constant
		ctx.dep.addDep(e.Name)
		return ctx.handleImplicitConversion(e, constObj.Type(), ctx.typeOf(e), glang.GallinaIdent(e.Name))
	}
	if _, ok := obj.(*types.Var); ok {
		ctx.nope(e, "variable references should get translated via exprAddr")
	}
	if _, ok := obj.(*types.Func); ok {
		// is a function
		return ctx.function(e)
	}
	ctx.unsupported(e, "unrecognized kind of identifier; not local variable or global function")
	panic("")
}

func (ctx *Ctx) indexExpr(e *ast.IndexExpr, isSpecial bool) glang.Expr {
	xTy := ctx.typeOf(e.X).Underlying()
	switch xTy.(type) {
	case *types.Map:
		e := glang.NewCallExpr(glang.GallinaIdent("map.get"),
			ctx.expr(e.X),
			ctx.expr(e.Index))
		// FIXME: this is non-local. Should decide whether to do "Fst" based on
		// assign statement or parent expression.
		if !isSpecial {
			e = glang.NewCallExpr(glang.GallinaIdent("Fst"), e)
		}
		return e
	case *types.Slice:
		return glang.DerefExpr{
			X:  ctx.exprAddr(e),
			Ty: ctx.glangType(e, ctx.typeOf(e)),
		}
	case *types.Array:
		if ctx.info.Types[e].Addressable() {
			return glang.DerefExpr{
				X:  ctx.exprAddr(e),
				Ty: ctx.glangType(e, ctx.typeOf(e)),
			}
		} else {
			return glang.NewCallExpr(glang.GallinaIdent("array.elem_get"),
				ctx.glangType(e, ctx.typeOf(e)),
				ctx.expr(e.X), ctx.expr(e.Index))
		}
	case *types.Signature:
		// generic arguments are grabbed from go ast, ignore explicit type args
		return ctx.expr(e.X)
	}
	ctx.unsupported(e, "index into unknown type %v", xTy)
	return glang.CallExpr{}
}

func (ctx *Ctx) indexListExpr(e *ast.IndexListExpr) glang.Expr {
	// generic arguments are grabbed from go ast, ignore explicit type args
	return ctx.expr(e.X)
}

func (ctx *Ctx) derefExpr(e ast.Expr) glang.Expr {
	return glang.DerefExpr{
		X:  ctx.expr(e),
		Ty: ctx.glangType(e, ptrElem(ctx.typeOf(e))),
	}
}

func (ctx *Ctx) expr(e ast.Expr) glang.Expr {
	if ctx.info.Types[e].Addressable() {
		return glang.DerefExpr{X: ctx.exprAddr(e), Ty: ctx.glangType(e, ctx.typeOf(e))}
	} else {
		return ctx.exprSpecial(e, false)
	}
}

func (ctx *Ctx) funcLit(e *ast.FuncLit) glang.FuncLit {
	fl := glang.FuncLit{}

	// reset to original value after translating this FuncLit
	defer func(b bool) {
		ctx.usesDefer = b
	}(ctx.usesDefer)

	ctx.usesDefer = false

	defer func(oldFuncType *types.Signature) {
		ctx.curFuncType = oldFuncType
	}(ctx.curFuncType)

	ctx.curFuncType = ctx.typeOf(e.Type).(*types.Signature)
	fl.Args = ctx.paramList(e.Type.Params)
	fl.Body = ctx.blockStmt(e.Body, nil)

	for _, arg := range fl.Args {
		fl.Body = glang.LetExpr{
			Names:   []string{arg.Name},
			ValExpr: glang.RefExpr{Ty: arg.Type, X: glang.IdentExpr(arg.Name)},
			Cont:    fl.Body,
		}
	}

	if ctx.usesDefer {
		fl.Body = glang.NewCallExpr(glang.GallinaIdent("with_defer:"), fl.Body)
	} else {
		fl.Body = glang.NewCallExpr(glang.GallinaIdent("exception_do"), fl.Body)
	}

	return fl
}

func (ctx *Ctx) exprSpecial(e ast.Expr, isSpecial bool) glang.Expr {
	switch e := e.(type) {
	case *ast.CallExpr:
		return ctx.callExpr(e)
	case *ast.Ident:
		return ctx.identExpr(e, isSpecial)
	case *ast.SelectorExpr:
		return ctx.selectorExpr(e)
	case *ast.CompositeLit:
		return ctx.compositeLiteral(e)
	case *ast.BasicLit:
		// ctx.nope(e, "all basic literal should have a const value")
		return ctx.basicLiteral(e)
	case *ast.BinaryExpr:
		return ctx.binExpr(e)
	case *ast.SliceExpr:
		return ctx.sliceExpr(e)
	case *ast.IndexExpr:
		return ctx.indexExpr(e, isSpecial)
	case *ast.IndexListExpr:
		return ctx.indexListExpr(e)
	case *ast.UnaryExpr:
		return ctx.unaryExpr(e, isSpecial)
	case *ast.ParenExpr:
		return ctx.expr(e.X)
	case *ast.StarExpr:
		return ctx.derefExpr(e.X)
	case *ast.TypeAssertExpr:
		// TODO: do something with the type
		return ctx.expr(e.X)
	case *ast.FuncLit:
		return ctx.funcLit(e)
	default:
		ctx.unsupported(e, "unexpected expr")
	}
	return nil
}

func (ctx *Ctx) stmtList(ss []ast.Stmt, cont glang.Expr) glang.Expr {
	if len(ss) == 0 {
		return glang.DoExpr{Expr: glang.Tt}
	}
	var e glang.Expr = nil
	for len(ss) > 0 {
		stmt := ss[len(ss)-1]
		ss = ss[:len(ss)-1]
		e = ctx.stmt(stmt, e)
	}
	return glang.SeqExpr{Expr: e, Cont: cont}
}

func (ctx *Ctx) blockStmt(s *ast.BlockStmt, cont glang.Expr) glang.Expr {
	return ctx.stmtList(s.List, cont)
}

func (ctx *Ctx) switchStmt(s *ast.SwitchStmt, cont glang.Expr) (e glang.Expr) {
	var tagExpr glang.Expr = glang.True

	var tagType types.Type = types.Typ[types.Bool]

	if s.Tag != nil {
		tagType = ctx.typeOf(s.Tag)
		tagExpr = ctx.expr(s.Tag)
	}

	// Get default handler
	e = glang.Tt
	for i := len(s.Body.List) - 1; i >= 0; i-- {
		c := s.Body.List[i].(*ast.CaseClause)
		if c.List == nil {
			e = ctx.stmtList(c.Body, nil)
		}
	}

	for i := len(s.Body.List) - 1; i >= 0; i-- {
		c := s.Body.List[i].(*ast.CaseClause)
		if c.List == nil {
			continue
		}

		t := ctx.typeOf(c.List[0])
		eqType := ctx.typeJoin(c.List[0], t, tagType)
		cond := glang.BinaryExpr{
			X:  ctx.handleImplicitConversion(c.List[0], tagType, eqType, glang.IdentExpr("$sw")),
			Op: glang.OpEquals,
			Y:  ctx.handleImplicitConversion(c.List[0], t, eqType, ctx.expr(c.List[0])),
		}

		for _, y := range c.List[1:] {
			t := ctx.typeOf(y)
			eqType := ctx.typeJoin(y, t, tagType)
			cond = glang.BinaryExpr{
				Op: glang.OpLOr,
				X: glang.BinaryExpr{
					X:  ctx.handleImplicitConversion(y, tagType, eqType, glang.IdentExpr("$sw")),
					Op: glang.OpEquals,
					Y:  ctx.handleImplicitConversion(y, t, eqType, ctx.expr(y)),
				},
				Y: cond,
			}
		}

		e = glang.IfExpr{
			Cond: cond,
			Then: ctx.stmtList(c.Body, nil),
			Else: e,
		}
	}

	e = glang.LetExpr{Names: []string{"$sw"}, ValExpr: tagExpr, Cont: e}

	if s.Init != nil {
		e = glang.ParenExpr{Inner: ctx.stmt(s.Init, e)}
	}

	e = glang.SeqExpr{Expr: e, Cont: cont}
	return
}

func (ctx *Ctx) ifStmt(s *ast.IfStmt, cont glang.Expr) glang.Expr {
	var elseExpr glang.Expr = glang.DoExpr{Expr: glang.Tt}
	if s.Else != nil {
		elseExpr = ctx.stmt(s.Else, nil)
	}
	var ife glang.Expr = glang.IfExpr{
		Cond: ctx.handleImplicitConversion(s.Cond, ctx.typeOf(s.Cond), types.Typ[types.Bool], ctx.expr(s.Cond)),
		Then: ctx.blockStmt(s.Body, nil),
		Else: elseExpr,
	}

	if s.Init != nil {
		ife = glang.ParenExpr{Inner: ctx.stmt(s.Init, ife)}
	}
	return glang.SeqExpr{Expr: ife, Cont: cont}
}

func (ctx *Ctx) forStmt(s *ast.ForStmt, cont glang.Expr) glang.Expr {
	var cond glang.Expr = glang.True
	if s.Cond != nil {
		cond = ctx.expr(s.Cond)
	}
	var post glang.Expr = glang.Skip
	if s.Post != nil {
		post = ctx.stmt(s.Post, nil)
	}

	body := ctx.blockStmt(s.Body, nil)
	var e glang.Expr = glang.ForLoopExpr{
		Cond: cond,
		Post: post,
		Body: body,
	}
	if s.Init != nil {
		e = glang.ParenExpr{Inner: ctx.stmt(s.Init, e)}
	}
	return glang.SeqExpr{Expr: e, Cont: cont}
}

func getIdentOrAnonymous(e ast.Expr) (ident string, ok bool) {
	if e == nil {
		return "_", true
	}
	return getIdent(e)
}

func (ctx *Ctx) mapRangeStmt(s *ast.RangeStmt) glang.Expr {
	key, ok := getIdentOrAnonymous(s.Key)
	if !ok {
		ctx.nope(s.Key, "range with non-ident key")
		return nil
	}
	val, ok := getIdentOrAnonymous(s.Value)
	if !ok {
		ctx.nope(s.Value, "range with non-ident value")
		return nil
	}
	return glang.ForRangeMapExpr{
		KeyIdent:   key,
		ValueIdent: val,
		Map:        ctx.expr(s.X),
		Body:       ctx.blockStmt(s.Body, nil),
	}
}

func (ctx *Ctx) identBinder(id *ast.Ident) glang.Binder {
	if id == nil {
		return glang.Binder(nil)
	}
	e := glang.IdentExpr(id.Name)
	return &e
}

func (ctx *Ctx) sliceRangeStmt(s *ast.RangeStmt) glang.Expr {
	if s.Tok != token.DEFINE {
		ctx.unsupported(s, "range with pre-existing variables")
	}
	key, ok := s.Key.(*ast.Ident)
	if !ok {
		ctx.todo(s.Key, "range with non-identifier as iteration variable")
	}
	valExpr := glang.Binder(nil)
	if s.Value != nil {
		val, ok := s.Value.(*ast.Ident)
		if !ok {
			ctx.todo(s.Value, "range with non-identifier as iteration variable")
		}
		valExpr = ctx.identBinder(val)
	}

	var e glang.Expr = glang.ForRangeSliceExpr{
		Key:   ctx.identBinder(key),
		Val:   valExpr,
		Slice: glang.IdentExpr("$range"),
		Ty:    ctx.glangType(s.X, sliceElem(ctx.typeOf(s.X))),
		Body:  ctx.blockStmt(s.Body, nil),
	}
	return glang.LetExpr{
		Names:   []string{"$range"},
		ValExpr: ctx.expr(s.X),
		Cont:    e,
	}
}

func (ctx *Ctx) rangeStmt(s *ast.RangeStmt) glang.Expr {
	switch ctx.typeOf(s.X).Underlying().(type) {
	case *types.Map:
		return ctx.mapRangeStmt(s)
	case *types.Slice:
		return ctx.sliceRangeStmt(s)
	default:
		ctx.unsupported(s,
			"range over %v (only maps and slices are supported)",
			ctx.typeOf(s.X).Underlying())
		return nil
	}
}

func (ctx *Ctx) defineStmt(s *ast.AssignStmt, cont glang.Expr) glang.Expr {
	e := ctx.assignStmt(s, cont)

	// Before the asignStmt "e", allocate everything that's new in this define stmt.
	for _, lhsExpr := range s.Lhs {
		if ident, ok := lhsExpr.(*ast.Ident); ok {
			if _, ok := ctx.info.Defs[ident]; ok { // if this identifier is defining something
				if ident.Name == "_" {
					continue
				}
				t := ctx.glangType(ident, ctx.info.TypeOf(ident))
				e = glang.LetExpr{
					Names: []string{ident.Name},
					ValExpr: glang.RefExpr{
						X:  glang.NewCallExpr(glang.GallinaIdent("zero_val"), t),
						Ty: t,
					},
					Cont: e,
				}
			}
		} else {
			ctx.nope(lhsExpr, "defining a non-identifier")
		}
	}

	return e
}

func (ctx *Ctx) varSpec(s *ast.ValueSpec, cont glang.Expr) glang.Expr {
	var lhs []ast.Expr
	for _, l := range s.Names {
		lhs = append(lhs, l)
	}
	return ctx.defineStmt(&ast.AssignStmt{Lhs: lhs, Rhs: s.Values}, cont)
}

// varDeclStmt translates declarations within functions
func (ctx *Ctx) varDeclStmt(s *ast.DeclStmt, cont glang.Expr) glang.Expr {
	decl, ok := s.Decl.(*ast.GenDecl)
	if !ok {
		ctx.noExample(s, "declaration that is not a GenDecl")
	}
	if decl.Tok != token.VAR {
		ctx.unsupported(s, "non-var declaration for %v", decl.Tok)
	}
	var expr glang.Expr = cont
	for _, spec := range decl.Specs {
		// guaranteed to be a *Ast.ValueSpec due to decl.Tok
		//
		// https://golang.org/pkg/go/ast/#GenDecl
		// TODO: handle TypeSpec
		expr = ctx.varSpec(spec.(*ast.ValueSpec), expr)
	}
	return expr
}

// Returns the address of the given expression.
// Requires that e is actually addressable
func (ctx *Ctx) exprAddr(e ast.Expr) glang.Expr {
	switch e := e.(type) {
	case *ast.ParenExpr:
		return ctx.exprAddr(e.X)
	case *ast.Ident:
		obj := ctx.info.ObjectOf(e)
		if _, ok := obj.(*types.Var); ok {
			if obj.Pkg().Scope() == obj.Parent() {
				ctx.dep.addDep("pkg_name'")
				return glang.NewCallExpr(glang.GallinaIdent("globals.get"),
					glang.StringVal{Value: glang.GallinaIdent("pkg_name'")},
					glang.StringVal{Value: glang.StringLiteral{Value: e.Name}},
				)
			} else {
				return glang.IdentExpr(e.Name)
			}
		} else {
			ctx.unsupported(e, "exprAddr of ident that is not a var")
		}
	case *ast.IndexExpr:
		targetTy := ctx.typeOf(e.X)
		switch targetTy := targetTy.Underlying().(type) {
		case *types.Slice:
			return glang.NewCallExpr(glang.GallinaIdent("slice.elem_ref"),
				ctx.glangType(e, targetTy.Elem()),
				ctx.expr(e.X),
				ctx.expr(e.Index))
		case *types.Map:
			ctx.nope(e, "map index expressions are not addressable")
		case *types.Array:
			return glang.NewCallExpr(glang.GallinaIdent("array.elem_ref"),
				ctx.glangType(e, targetTy.Elem()), ctx.expr(e.X), ctx.expr(e.Index))
		default:
			ctx.unsupported(e, "index addr to unexpected target of type %v", targetTy)
		}
	case *ast.StarExpr:
		return ctx.expr(e.X)
	case *ast.SelectorExpr:
		return ctx.selectorExprAddr(e)
	default:
		ctx.unsupported(e, "address of unknown expression")
	}
	return nil
}

func (ctx *Ctx) assignFromTo(lhs ast.Expr, rhs glang.Expr, cont glang.Expr) glang.Expr {
	// lhs should either be a map index expression, or is addressable
	switch lhs := lhs.(type) {
	case *ast.Ident:
		if lhs.Name == "_" {
			return glang.NewDoSeq(rhs, cont)
		}
	case *ast.IndexExpr:
		targetTy := ctx.typeOf(lhs.X).Underlying()
		switch targetTy.(type) {
		case *types.Map:
			return glang.NewDoSeq(glang.NewCallExpr(glang.GallinaIdent("map.insert"),
				ctx.expr(lhs.X),
				ctx.expr(lhs.Index),
				rhs), cont)
		}
	}

	return glang.NewDoSeq(glang.StoreStmt{
		Dst: ctx.exprAddr(lhs),
		X:   rhs,
		Ty:  ctx.glangType(lhs, ctx.typeOf(lhs)),
	}, cont)
}

// This handles conversions arising from the notion of "assignability" in the Go spec.
func (ctx *Ctx) handleImplicitConversion(n locatable, from, to types.Type, e glang.Expr) glang.Expr {
	if to == nil {
		// This happens when the LHS is `_`
		return e
	}
	if from == nil {
		ctx.unsupported(n, "implicit conversion: don't know from type")
	}
	fromUnder := from.Underlying()
	toUnder := to.Underlying()
	if types.Identical(fromUnder, toUnder) {
		return e
	}

	if fromPtr, ok := from.(*types.Pointer); ok {
		if toPtr, ok := to.(*types.Pointer); ok {
			fromBase := fromPtr.Elem().Underlying()
			toBase := toPtr.Elem().Underlying()
			if types.Identical(fromBase, toBase) {
				return e
			} else {
				ctx.nope(n, "Cannot convert between pointer types from base %s to %s",
					fromBase, toBase,
				)
			}
		}
	}

	if fromBasic, ok := fromUnder.(*types.Basic); ok && fromBasic.Kind() == types.UntypedNil {
		if _, ok := toUnder.(*types.Slice); ok {
			return glang.GallinaIdent("#slice.nil")
		} else if _, ok := toUnder.(*types.Interface); ok {
			return glang.GallinaIdent("#interface.nil")
		} else if _, ok := toUnder.(*types.Pointer); ok {
			return glang.GallinaIdent("#null")
		} else if _, ok := toUnder.(*types.Chan); ok {
			return glang.GallinaIdent("#null")
		} else if _, ok := toUnder.(*types.Map); ok {
			return glang.GallinaIdent("#null")
		} else if _, ok := toUnder.(*types.Signature); ok {
			return glang.GallinaIdent("#func.nil")
		}
	}
	if _, ok := toUnder.(*types.Interface); ok {
		if _, ok := fromUnder.(*types.Interface); ok {
			// if both are interface types, then no need to convert anything
			// because the GooseLang representation of interface values is
			// independent of the particular interface type.
			return e
		}

		maybePtrSuffix := ""
		if fromPointer, ok := from.(*types.Pointer); ok {
			from = fromPointer.Elem()
			maybePtrSuffix = "'ptr"
		}
		if fromNamed, ok := from.(*types.Named); ok {
			pkgName, typeName := ctx.getPkgAndName(fromNamed.Obj())
			ctx.dep.addDep(typeName)
			return glang.NewCallExpr(glang.GallinaIdent("interface.make"),
				glang.StringVal{Value: glang.GallinaIdent(pkgName)},
				glang.StringVal{Value: glang.GallinaString(typeName + maybePtrSuffix)},
				e)
		} else if fromBasic, ok := from.(*types.Basic); ok {
			typeName := fromBasic.Name() + maybePtrSuffix
			ctx.dep.addDep(typeName)
			return glang.NewCallExpr(glang.GallinaIdent("interface.make"),
				glang.StringVal{Value: glang.StringLiteral{Value: ""}},
				glang.StringVal{Value: glang.StringLiteral{Value: typeName}},
				e,
			)
		} else if _, ok := from.(*types.Slice); ok {
			typeName := "slice'" + maybePtrSuffix
			ctx.dep.addDep(typeName)
			return glang.NewCallExpr(glang.GallinaIdent("interface.make"), glang.StringVal{Value: glang.StringLiteral{Value: typeName}}, e)
		} else if _, ok := from.(*types.Map); ok {
			typeName := "map'" + maybePtrSuffix
			ctx.dep.addDep(typeName)
			return glang.NewCallExpr(glang.GallinaIdent("interface.make"), glang.StringVal{Value: glang.StringLiteral{Value: typeName}}, e)
		}
	}

	if fromBasic, ok := fromUnder.(*types.Basic); ok && fromBasic.Kind() == types.UntypedBool {
		if toBasic, ok := toUnder.(*types.Basic); ok && toBasic.Kind() == types.Bool {
			// XXX: not making a distinction between typed and untyped bool.
			// Untyped bool are the runtime result of comparison operators,
			// whereas other untyped types are only used in constants.
			return e
		}
	}

	if fromBasic, ok := fromUnder.(*types.Basic); ok && fromBasic.Kind() == types.UntypedString {
		if toBasic, ok := toUnder.(*types.Basic); ok && toBasic.Kind() == types.String {
			return glang.StringVal{Value: e}
		}
	}

	if fromBasic, ok := fromUnder.(*types.Basic); ok && fromBasic.Kind() == types.UntypedInt {
		if toBasic, ok := toUnder.(*types.Basic); ok {
			switch toBasic.Kind() {
			case types.Uint64, types.Int64, types.Int, types.Uint:
				// XXX: treat an `int` as a `int64` and `uint` as `uint64`
				return glang.Int64Val{Value: e}
			case types.Uint32, types.Int32:
				return glang.Int32Val{Value: e}
			case types.Uint8, types.Int8:
				return glang.Int8Val{Value: e}
			case types.Float64:
				// XXX: treat a `float64` as a `w64`
				return glang.Int64Val{Value: e}
			case types.Float32:
				// XXX: treat a `float64` as a `w64`
				return glang.Int32Val{Value: e}
			}
		}
	}

	fromChan, ok1 := fromUnder.(*types.Chan)
	toChan, ok2 := toUnder.(*types.Chan)
	if ok1 && ok2 {
		if types.Identical(fromChan.Elem(), toChan.Elem()) {
			return e
		}
	}

	ctx.unsupported(n, "(possibly implicit) conversion from %s to %s", from, to)
	panic("unreachable")
}

func (ctx *Ctx) assignStmt(s *ast.AssignStmt, cont glang.Expr) glang.Expr {
	e := cont
	if len(s.Rhs) == 0 {
		return e
	}

	// Execute assignments left-to-right
	for i := len(s.Lhs); i > 0; i-- {
		e = ctx.assignFromTo(s.Lhs[i-1], glang.IdentExpr(fmt.Sprintf("$r%d", i-1)), e)
	}

	// Determine RHS types, specially handling multiple returns from a function call.
	var rhsTypes []types.Type
	for i := 0; i < len(s.Rhs); i++ {
		t := ctx.typeOf(s.Rhs[i])
		if tuple, ok := t.(*types.Tuple); ok {
			for i := range tuple.Len() {
				rhsTypes = append(rhsTypes, tuple.At(i).Type())
			}
		} else {
			rhsTypes = append(rhsTypes, t)
		}
	}

	// collect the RHS expressions
	var rhsExprs []glang.Expr
	if len(s.Rhs) == len(s.Lhs) {
		for _, rhs := range s.Rhs {
			rhsExprs = append(rhsExprs, ctx.expr(rhs))
		}
	} else {
		// RHS is a function call returning multiple things. Will introduce
		// extra let bindings to destructure those multiple returns.
		for i := range s.Lhs {
			rhsExprs = append(rhsExprs, glang.IdentExpr(fmt.Sprintf("$ret%d", i)))
		}
	}

	// Let bindings for RHSs including conversions
	for i := len(s.Lhs); i > 0; i-- {
		e = glang.LetExpr{
			Names: []string{fmt.Sprintf("$r%d", i-1)},
			ValExpr: ctx.handleImplicitConversion(s.Lhs[i-1], rhsTypes[i-1],
				ctx.typeOf(s.Lhs[i-1]), rhsExprs[i-1]),
			Cont: e,
		}
	}

	// Extra let bindings in case RHS is a multiple-returning function
	if len(s.Rhs) != len(s.Lhs) && len(s.Lhs) > 0 {
		var n []string
		for i := range s.Lhs {
			n = append(n, fmt.Sprintf("$ret%d", i))
		}
		e = glang.LetExpr{
			Names:   n,
			ValExpr: ctx.exprSpecial(s.Rhs[0], true),
			Cont:    e,
		}
	}

	return e
}

func (ctx *Ctx) assignOpStmt(s *ast.AssignStmt, cont glang.Expr) glang.Expr {
	assignOps := map[token.Token]glang.BinOp{
		token.ADD_ASSIGN: glang.OpPlus,
		token.SUB_ASSIGN: glang.OpMinus,
	}
	op, ok := assignOps[s.Tok]
	if !ok {
		ctx.unsupported(s, "unsupported assign+update operation %v", s.Tok)
	}
	rhs := glang.BinaryExpr{
		X:  ctx.expr(s.Lhs[0]),
		Op: op,
		Y:  ctx.expr(s.Rhs[0]),
	}
	return ctx.assignFromTo(s.Lhs[0], rhs, cont)
}

func (ctx *Ctx) incDecStmt(stmt *ast.IncDecStmt, cont glang.Expr) glang.Expr {
	op := glang.OpPlus
	if stmt.Tok == token.DEC {
		op = glang.OpMinus
	}
	return ctx.assignFromTo(stmt.X, glang.BinaryExpr{
		X:  ctx.expr(stmt.X),
		Op: op,
		Y:  glang.Int64Val{Value: glang.ZLiteral{Value: big.NewInt(1)}},
	}, cont)
}

func (ctx *Ctx) branchStmt(s *ast.BranchStmt, cont glang.Expr) glang.Expr {
	if s.Tok == token.CONTINUE {
		return glang.SeqExpr{Expr: glang.ContinueExpr{}, Cont: cont}
	}
	if s.Tok == token.BREAK {
		return glang.SeqExpr{Expr: glang.BreakExpr{}, Cont: cont}
	}
	ctx.noExample(s, "unexpected control flow %v in loop", s.Tok)
	return nil
}

func (ctx *Ctx) goStmt(e *ast.GoStmt, cont glang.Expr) glang.Expr {
	args := make([]glang.Expr, 0, len(e.Call.Args))
	for i := range len(e.Call.Args) {
		args = append(args, glang.IdentExpr(fmt.Sprintf("a%d", i)))
	}
	var expr glang.Expr = glang.NewDoSeq(glang.SpawnExpr{Body: glang.NewCallExpr(
		glang.IdentExpr("$go"),
		args...,
	)}, cont)

	expr = glang.LetExpr{
		Names:   []string{"$go"},
		ValExpr: ctx.expr(e.Call.Fun),
		Cont:    expr,
	}

	expr = ctx.callExprPrelude(e.Call, expr)

	return expr
}

func (ctx *Ctx) returnStmt(s *ast.ReturnStmt, cont glang.Expr) glang.Expr {
	if len(s.Results) == 0 {
		return ctx.defaultReturn
	}

	exprs := make([]glang.Expr, 0, len(s.Results))
	var expectedReturnTypes []types.Type
	if ctx.curFuncType.Results() != nil {
		for i := range ctx.curFuncType.Results().Len() {
			expectedReturnTypes = append(expectedReturnTypes, ctx.curFuncType.Results().At(i).Type())
		}
	}

	var retExpr glang.Expr
	func() {
		var unconvertedReturnValues []exprWithInfo
		if len(s.Results) == 1 && len(expectedReturnTypes) > 1 {
			// special case
			tupleType, ok := ctx.typeOf(s.Results[0]).(*types.Tuple)
			if !ok {
				ctx.nope(s.Results[0], "the only way for the number of values in a returnStmt to mismatch "+
					"the function's signature is passing through a multiple-returning function")
			}
			for i := range tupleType.Len() {
				unconvertedReturnValues = append(unconvertedReturnValues, exprWithInfo{
					e: glang.IdentExpr(fmt.Sprintf("$ret%d", i)),
					t: tupleType.At(i).Type(),
					n: s.Results[0],
				})
			}
			defer func() {
				var names []string
				for i := range tupleType.Len() {
					names = append(names, fmt.Sprintf("$ret%d", i))
				}
				retExpr = glang.LetExpr{Names: names,
					ValExpr: glang.ParenExpr{Inner: ctx.expr(s.Results[0])},
					Cont:    retExpr,
				}
			}()
		} else {
			for _, result := range s.Results {
				unconvertedReturnValues = append(unconvertedReturnValues, exprWithInfo{
					e: ctx.expr(result),
					t: ctx.typeOf(result),
					n: result,
				})
			}
		}

		if len(unconvertedReturnValues) != len(expectedReturnTypes) {
			log.Print(len(unconvertedReturnValues), len(expectedReturnTypes))
			log.Print(ctx.curFuncType.Results())
			ctx.nope(s, "bug")
		}

		for i, e := range unconvertedReturnValues {
			exprs = append(exprs, ctx.handleImplicitConversion(e.n, e.t, expectedReturnTypes[i], e.e))
		}
		if len(exprs) == 0 { // return #()
			exprs = []glang.Expr{glang.Tt}
		}
		retExpr = glang.ReturnExpr{Value: glang.TupleExpr(exprs)}
	}()

	return glang.SeqExpr{Expr: retExpr, Cont: cont}
}

func (ctx *Ctx) deferStmt(s *ast.DeferStmt, cont glang.Expr) (expr glang.Expr) {
	ctx.usesDefer = true
	args := make([]glang.Expr, 0, len(s.Call.Args))
	for i := range len(s.Call.Args) {
		args = append(args, glang.IdentExpr(fmt.Sprintf("a%d", i)))
	}

	expr = glang.LetExpr{
		ValExpr: glang.NewCallExpr(glang.IdentExpr("$f"), args...),
		Cont:    glang.NewCallExpr(glang.IdentExpr("$oldf"), glang.Tt),
	}

	expr = glang.FuncLit{Body: expr}

	expr = glang.LetExpr{
		Names:   []string{"$oldf"},
		ValExpr: glang.DerefExpr{X: glang.IdentExpr("$defer"), Ty: glang.FuncType{}},
		Cont:    expr,
	}

	expr = glang.StoreStmt{
		Dst: glang.IdentExpr("$defer"),
		Ty:  glang.FuncType{},
		X:   expr,
	}

	expr = glang.LetExpr{
		Names:   []string{"$f"},
		ValExpr: ctx.expr(s.Call.Fun),
		Cont:    expr,
	}

	expr = ctx.callExprPrelude(s.Call, expr)
	expr = glang.NewDoSeq(expr, cont)
	return
}

func (ctx *Ctx) selectStmt(s *ast.SelectStmt, cont glang.Expr) (expr glang.Expr) {
	var sends glang.ListExpr
	var recvs glang.ListExpr
	var def glang.Expr = glang.NewCallExpr(glang.GallinaIdent("InjLV"), glang.Tt)

	// build up select statement itself
	for _, s := range s.Body.List {
		s := s.(*ast.CommClause)
		if s.Comm == nil {
			def = glang.NewCallExpr(glang.GallinaIdent("InjR"), glang.FuncLit{Body: ctx.stmtList(s.Body, nil)})
		} else if _, ok := s.Comm.(*ast.SendStmt); ok {
			sendIndex := len(sends)
			sends = append(sends, glang.TupleExpr{
				glang.IdentExpr(fmt.Sprintf("$sendVal%d", sendIndex)),
				glang.IdentExpr(fmt.Sprintf("$sendChan%d", sendIndex)),
				glang.FuncLit{Body: ctx.stmtList(s.Body, nil)},
			})
		} else { // must be a receive stmt
			recvIndex := len(recvs)
			body := ctx.stmtList(s.Body, nil)

			// want to figure out the first statment to run in the body
			switch comm := s.Comm.(type) {
			case *ast.ExprStmt:
				recvExpr := comm.X.(*ast.UnaryExpr)
				if recvExpr.Op != token.ARROW {
					ctx.nope(comm.X, "expected recv statement")
				}
				// nothing to run in the body
			case *ast.AssignStmt:
				// XXX: replace the RHS in the assignment statement with an
				// ident, so we can put this straight in the the body list
				if len(comm.Rhs) != 1 {
					ctx.unsupported(comm, "expected a single receive operation on RHS")
				}
				var rhs ast.Expr = comm.Rhs[0]
				for {
					if r, ok := rhs.(*ast.ParenExpr); ok {
						rhs = r.X
					} else {
						break
					}
				}
				recvExpr := rhs.(*ast.UnaryExpr)
				if recvExpr.Op != token.ARROW {
					ctx.nope(comm.Rhs[0], "expected recv statement")
				}

				// XXX: create a new AST node and enough typing information for
				// an assignStmt to translate.
				t := ctx.info.Types[recvExpr]
				comm.Rhs[0] = ast.NewIdent("$recvVal")
				ctx.info.Types[comm.Rhs[0]] = t

				if comm.Tok == token.DEFINE {
					body = ctx.defineStmt(comm, body)
				} else if comm.Tok == token.ASSIGN {
					body = ctx.assignStmt(comm, body)
				}
			default:
				ctx.unsupported(s.Comm, "unexpected statement in select clause")
			}

			recvs = append(recvs, glang.TupleExpr{
				glang.IdentExpr(fmt.Sprintf("$recvChan%d", recvIndex)),
				glang.FuncLit{Args: []glang.FieldDecl{{Name: "$recvVal"}}, Body: body},
			})
		}
	}

	expr = glang.NewCallExpr(glang.GallinaIdent("chan.select"), sends, recvs, def)
	expr = glang.NewDoSeq(expr, cont)
	return
}

func (ctx *Ctx) sendStmt(s *ast.SendStmt, cont glang.Expr) (expr glang.Expr) {
	expr = glang.NewCallExpr(glang.GallinaIdent("chan.send"), glang.IdentExpr("$chan"), glang.IdentExpr("$v"))
	// XXX: left-to-right evaluation, might not match Go
	expr = glang.LetExpr{Names: []string{"$v"}, ValExpr: ctx.expr(s.Value), Cont: expr}
	expr = glang.LetExpr{Names: []string{"$chan"}, ValExpr: ctx.expr(s.Chan), Cont: expr}
	expr = glang.NewDoSeq(expr, cont)
	return
}

func (ctx *Ctx) stmt(s ast.Stmt, cont glang.Expr) glang.Expr {
	switch s := s.(type) {
	case *ast.ReturnStmt:
		return ctx.returnStmt(s, cont)
	case *ast.BranchStmt:
		return ctx.branchStmt(s, cont)
	case *ast.IfStmt:
		return ctx.ifStmt(s, cont)
	case *ast.GoStmt:
		return ctx.goStmt(s, cont)
	case *ast.ExprStmt:
		return glang.NewDoSeq(ctx.expr(s.X), cont)
	case *ast.AssignStmt:
		if s.Tok == token.DEFINE {
			return ctx.defineStmt(s, cont)
		} else if s.Tok == token.ASSIGN {
			return ctx.assignStmt(s, cont)
		} else {
			return ctx.assignOpStmt(s, cont)
		}
	case *ast.DeclStmt:
		return ctx.varDeclStmt(s, cont)
	case *ast.IncDecStmt:
		return ctx.incDecStmt(s, cont)
	case *ast.ForStmt:
		// note that this might be a nested loop,
		// in which case the loop var gets replaced by the inner loop.
		return ctx.forStmt(s, cont)
	case *ast.RangeStmt:
		return glang.NewDoSeq(ctx.rangeStmt(s), cont)
	case *ast.BlockStmt:
		return ctx.blockStmt(s, cont)
	case *ast.SwitchStmt:
		return ctx.switchStmt(s, cont)
	case *ast.TypeSwitchStmt:
		ctx.todo(s, "type switch statement")
	case *ast.DeferStmt:
		return ctx.deferStmt(s, cont)
	case *ast.SelectStmt:
		return ctx.selectStmt(s, cont)
	case *ast.SendStmt:
		return ctx.sendStmt(s, cont)
	default:
		ctx.unsupported(s, "statement %T", s)
	}
	panic("unreachable")
}

func funcName(f *types.Func) string {
	maybeTypeName := ""
	if recv := f.Type().(*types.Signature).Recv(); recv != nil {
		recvType := recv.Type()
		if ptrType, ok := recvType.(*types.Pointer); ok {
			recvType = ptrType.Elem()
		}
		maybeTypeName = types.TypeString(recvType, func(_ *types.Package) string { return "" }) + "."
	}
	return maybeTypeName + f.Name()
}

// Returns a glang.FuncDecl and maybe also a glang.NameDecl. If the function is an `init`, this
// returns None.
func (ctx *Ctx) funcDecl(d *ast.FuncDecl) []glang.Decl {
	funcName := funcName(ctx.info.ObjectOf(d.Name).(*types.Func))
	ctx.usesDefer = false
	fd := glang.FuncDecl{Name: d.Name.Name}
	addSourceDoc(d.Doc, &fd.Comment)
	ctx.addSourceFile(d, &fd.Comment)

	if d.Recv != nil {
		if len(d.Recv.List) != 1 {
			ctx.nope(d, "function with multiple receivers")
		}
		receiver := d.Recv.List[0]
		recvType := types.Unalias(ctx.typeOf(receiver.Type))
		// recvType must be either a "named" type or a pointer type that points to a named type.
		if baseType, ok := recvType.(*types.Pointer); ok {
			recvType = baseType.Elem()
		}
		namedType, ok := recvType.(*types.Named)
		if !ok {
			ctx.nope(d.Recv, "expected named type as method receiver, got %T", recvType)
		}
		typeName := namedType.Obj().Name()

		fd.Name = glang.TypeMethod(typeName, d.Name.Name)

		switch ctx.filter.GetAction(funcName) {
		case declfilter.Skip:
			return nil
		case declfilter.Trust:
			return nil
		case declfilter.Axiomatize:
			ctx.functions = append(ctx.functions, d.Name.Name)
			return []glang.Decl{glang.AxiomDecl{DeclName: fd.Name, Type: glang.GallinaIdent("val")}}
		}

		ctx.dep.setCurrentName(fd.Name)
		f := ctx.field(receiver)
		fd.RecvArg = &f
	} else {
		switch ctx.filter.GetAction(funcName) {
		case declfilter.Skip:
			return nil
		case declfilter.Trust:
			ctx.functions = append(ctx.functions, d.Name.Name)
			return nil
		case declfilter.Axiomatize:
			ctx.functions = append(ctx.functions, d.Name.Name)
			return []glang.Decl{glang.AxiomDecl{DeclName: fd.Name, Type: glang.GallinaIdent("val")}}
		}

		ctx.dep.setCurrentName(fd.Name)
	}
	defer ctx.dep.unsetCurrentName()

	if d.Type.TypeParams != nil {
		// TODO(generics): a plan for supporting generics:
		// - embed `go_type` into GooseLang rather than just Gallina; this
		//   includes instantiated generic types which includes the type
		//   arguments.
		// - type parameters would be GooseLang arguments, and method lookups
		//   would look up based on the type name and then specialize the method.
		// - interface values need to remember if the type is generic, and the
		//   type arguments if yes, so the type arguments can be passed into the
		//   method from `interface.get`
		ctx.unsupported(d, "generic functions not supported")
	}

	if d.Body == nil {
		ctx.unsupported(d, "external function")
	}

	// Assemble the `defaultReturn` expr so the body's `return` statements can use it.
	if d.Type.Results != nil {
		var defaultRetExpr glang.TupleExpr
		for _, r := range d.Type.Results.List {
			for _, name := range r.Names {
				defaultRetExpr = append(defaultRetExpr,
					glang.DerefExpr{
						X:  glang.IdentExpr(name.Name),
						Ty: ctx.glangType(r.Type, ctx.typeOf(r.Type)),
					})
			}
		}
		ctx.defaultReturn = glang.ReturnExpr{
			Value: defaultRetExpr,
		}
	} else {
		ctx.defaultReturn = glang.ReturnExpr{Value: glang.Tt}
	}

	body := ctx.blockStmt(d.Body, nil)

	if d.Name.Name == "init" {
		if ctx.usesDefer {
			body = glang.NewCallExpr(glang.GallinaIdent("with_defer:"), body)
		} else {
			body = glang.NewCallExpr(glang.GallinaIdent("exception_do"), body)
		}
		f := glang.FuncLit{Args: nil, Body: body}
		ctx.inits = append(ctx.inits, f)
		return nil
	} else if d.Recv == nil {
		ctx.functions = append(ctx.functions, d.Name.Name)
	}

	fd.Body = body
	fd.Args = append(fd.Args, ctx.paramList(d.Type.Params)...)

	for _, arg := range fd.Args {
		fd.Body = glang.LetExpr{
			Names:   []string{arg.Name},
			ValExpr: glang.RefExpr{Ty: arg.Type, X: glang.IdentExpr(arg.Name)},
			Cont:    fd.Body,
		}
	}
	if fd.RecvArg != nil {
		fd.Body = glang.LetExpr{
			Names:   []string{fd.RecvArg.Name},
			ValExpr: glang.RefExpr{Ty: fd.RecvArg.Type, X: glang.IdentExpr(fd.RecvArg.Name)},
			Cont:    fd.Body,
		}
	}
	if d.Type.Results != nil {
		for _, r := range d.Type.Results.List {
			t := ctx.glangType(r.Type, ctx.typeOf(r.Type))
			for _, name := range r.Names {
				fd.Body = glang.LetExpr{
					Names:   []string{name.Name},
					ValExpr: glang.RefExpr{Ty: t, X: glang.NewCallExpr(glang.GallinaIdent("zero_val"), t)},
					Cont:    fd.Body,
				}
			}
		}
	}

	if ctx.usesDefer {
		fd.Body = glang.NewCallExpr(glang.GallinaIdent("with_defer:"), fd.Body)
	} else {
		fd.Body = glang.NewCallExpr(glang.GallinaIdent("exception_do"), fd.Body)
	}
	return []glang.Decl{fd}
}

// this should only be used for untyped constant literals
func (ctx *Ctx) constantLiteral(l locatable, v constant.Value) (types.Type, glang.Expr) {
	switch v.Kind() {
	case constant.Bool:
		return types.Typ[types.UntypedBool], glang.BoolLiteral(constant.Val(v).(bool))
	case constant.String:
		return types.Typ[types.UntypedString], glang.StringLiteral{Value: constant.Val(v).(string)}
	case constant.Int:
		switch v := constant.Val(v).(type) {
		case *big.Int:
			return types.Typ[types.UntypedInt], glang.ZLiteral{Value: v}
		case int64:
			return types.Typ[types.UntypedInt], glang.ZLiteral{Value: big.NewInt(v)}
		default:
			ctx.nope(l, "untyped int const with unexpected type")
		}
	}
	ctx.unsupported(l, "unsupported constant val")
	return nil, nil
}

func (ctx *Ctx) declType(t types.Type) glang.Expr {
	switch t := t.(type) {
	case *types.Basic:
		switch t.Kind() {
		case types.UntypedString:
			return glang.GallinaIdent("go_string")
		case types.UntypedInt:
			return glang.GallinaIdent("Z")
		}
	}
	return glang.GallinaIdent("expr")
}

func (ctx *Ctx) constSpec(spec *ast.ValueSpec) []glang.Decl {
	var cds []glang.Decl
	for i := range spec.Names {
		switch ctx.filter.GetAction(spec.Names[i].Name) {
		case declfilter.Axiomatize:
			cds = append(cds, glang.AxiomDecl{DeclName: spec.Names[i].Name,
				Type: ctx.declType(ctx.typeOf(spec.Names[i])),
			})
		case declfilter.Translate:
			cd := glang.ConstDecl{
				Name: spec.Names[i].Name,
			}
			ctx.dep.setCurrentName(cd.Name)
			defer ctx.dep.unsetCurrentName()

			addSourceDoc(spec.Comment, &cd.Comment)
			if len(spec.Values) > 0 {
				cd.Val =
					ctx.handleImplicitConversion(spec.Names[i],
						ctx.typeOf(spec.Values[i]), ctx.typeOf(spec.Names[i]),
						ctx.expr(spec.Values[i]))
			} else {
				fromT, v := ctx.constantLiteral(spec.Names[i], ctx.info.ObjectOf(spec.Names[i]).(*types.Const).Val())
				cd.Val = ctx.handleImplicitConversion(spec.Names[i], fromT, ctx.typeOf(spec.Names[i]), v)
			}
			cd.Type = ctx.declType(ctx.typeOf(spec.Names[i]))
			cds = append(cds, cd)
		}
	}
	return cds
}

func (ctx *Ctx) constDecl(d *ast.GenDecl) []glang.Decl {
	var specs []glang.Decl
	for _, spec := range d.Specs {
		spec := spec.(*ast.ValueSpec)
		specs = append(specs, ctx.constSpec(spec)...)
	}
	return specs
}

func (ctx *Ctx) globalVarDecl(d *ast.GenDecl) []glang.Decl {
	var decls []glang.Decl
	for _, spec := range d.Specs {
		s := spec.(*ast.ValueSpec)
		for _, name := range s.Names {
			if name.Name == "_" {
				continue
			}
			switch ctx.filter.GetAction(name.Name) {
			case declfilter.Translate:
				ctx.globalVars = append(ctx.globalVars, name)
			default:
				if s.Values != nil {
					decls = append(decls, glang.AxiomDecl{
						DeclName: name.Name + "'init",
						Type:     glang.GallinaIdent("val"),
					})
				}
			}
		}
	}
	return decls
}

func stringLitValue(lit *ast.BasicLit) string {
	if lit.Kind != token.STRING {
		panic("unexpected non-string literal")
	}
	s, err := strconv.Unquote(lit.Value)
	if err != nil {
		panic("unexpected string literal value: " + err.Error())
	}
	return s
}

var ffiMapping = map[string]string{
	"github.com/mit-pdos/gokv/grove_ffi":         "grove",
	"github.com/goose-lang/primitive/disk":       "disk",
	"github.com/goose-lang/primitive/async_disk": "async_disk",
}

func (ctx *Ctx) imports(d []ast.Spec) []glang.Decl {
	var decls []glang.Decl
	for _, s := range d {
		s := s.(*ast.ImportSpec)
		importPath := stringLitValue(s.Path)
		if !ctx.filter.ShouldImport(importPath) {
			continue
		}

		decls = append(decls, glang.ImportDecl{Path: importPath})
		n := ctx.info.PkgNameOf(s).Pkg().Name()
		if _, ok := ctx.importNames[n]; !ok {
			ctx.importNames[n] = struct{}{}
			ctx.importNamesOrdered = append(ctx.importNamesOrdered, n)
		}
	}
	return decls
}

func (ctx *Ctx) decl(d ast.Decl) []glang.Decl {
	switch d := d.(type) {
	case *ast.FuncDecl:
		ctx.curFuncType = ctx.typeOf(d.Name).(*types.Signature)
		fd := ctx.funcDecl(d)
		ctx.curFuncType = nil
		return fd
	case *ast.GenDecl:
		switch d.Tok {
		case token.IMPORT:
			return ctx.imports(d.Specs)
		case token.CONST:
			return ctx.constDecl(d)
		case token.VAR:
			return ctx.globalVarDecl(d)
		case token.TYPE:
			var decls []glang.Decl
			for _, spec := range d.Specs {
				spec := spec.(*ast.TypeSpec)
				decls = append(decls, ctx.typeDecl(spec)...)
			}
			return decls
		default:
			ctx.nope(d, "unknown token type in decl")
		}
	case *ast.BadDecl:
		ctx.nope(d, "bad declaration in type-checked code")
	default:
		ctx.nope(d, "top-level decl")
	}
	return nil
}

func (ctx *Ctx) initFunctions() []glang.Decl {
	var decls = []glang.Decl{}
	nameDecl := glang.ConstDecl{
		Name: "pkg_name'",
		Val:  glang.GallinaString(ctx.pkgPath),
		Type: glang.GallinaIdent("go_string"),
	}
	decls = append(decls, nameDecl)

	ctx.dep.setCurrentName("initialize'")
	initFunc := glang.FuncDecl{Name: "initialize'"}

	var globalVars glang.ListExpr
	for _, varIdent := range ctx.globalVars {
		t := ctx.glangType(varIdent, ctx.info.TypeOf(varIdent))
		globalVars = append(globalVars,
			glang.TupleExpr{
				glang.StringLiteral{Value: varIdent.Name},
				t,
			},
		)
	}

	varsDecl := glang.ConstDecl{
		Name: "vars'",
		Val:  globalVars,
		Type: glang.GallinaIdent("list (go_string * go_type)"),
	}
	decls = append(decls, varsDecl)

	var functions glang.ListExpr
	for _, functionName := range ctx.functions {
		functions = append(functions, glang.TupleExpr{glang.StringLiteral{Value: functionName}, glang.GallinaIdent(functionName)})
	}

	functionsDecl := glang.ConstDecl{
		Name: "functions'",
		Val:  functions,
		Type: glang.GallinaIdent("list (go_string * val)"),
	}
	decls = append(decls, functionsDecl)

	var msets glang.ListExpr
	for _, namedType := range ctx.namedTypes {
		mset, msetPtr := ctx.methodSet(namedType)
		typeName := namedType.Obj().Name()
		msets = append(msets, glang.TupleExpr{glang.StringLiteral{Value: typeName}, mset})
		msets = append(msets, glang.TupleExpr{glang.StringLiteral{Value: typeName + "'ptr"}, msetPtr})
	}

	msetsDecl := glang.ConstDecl{
		Name: "msets'",
		Val:  msets,
		Type: glang.GallinaIdent("list (go_string * (list (go_string * val)))"),
	}
	decls = append(decls, msetsDecl)

	var e glang.Expr

	// add all init() function bodies
	for i := range ctx.inits {
		init := ctx.inits[len(ctx.inits)-i-1]
		e = glang.NewDoSeq(glang.NewCallExpr(init, glang.Tt), e)
	}

	if ctx.filter.GetAction("_") != declfilter.Translate {
		decls = append(decls, glang.AxiomDecl{
			DeclName: "_'init",
			Type:     glang.GallinaIdent("val"),
		})
	}

	// initialize all local vars
InitLoop:
	for i := range ctx.info.InitOrder {
		init := ctx.info.InitOrder[len(ctx.info.InitOrder)-i-1]

		// Check if any of the LHS variables should be treated as axiomatized
		for i := 0; i < len(init.Lhs); i++ {
			varName := init.Lhs[i].Name()
			if ctx.filter.GetAction(varName) != declfilter.Translate {
				e = glang.NewDoSeq(
					glang.NewCallExpr(glang.GallinaIdent(varName+"'init"), glang.Tt),
					e)
				continue InitLoop
			}
		}

		// Execute assignments left-to-right
		for i := len(init.Lhs); i > 0; i-- {
			if init.Lhs[i-1].Name() != "_" {
				e = glang.NewDoSeq(
					glang.StoreStmt{
						Dst: glang.NewCallExpr(glang.GallinaIdent("globals.get"),
							glang.StringVal{Value: glang.GallinaIdent("pkg_name'")},
							glang.StringVal{Value: glang.StringLiteral{Value: init.Lhs[i-1].Name()}},
						),
						X:  glang.IdentExpr(fmt.Sprintf("$r%d", i-1)),
						Ty: ctx.glangType(init.Lhs[i-1], init.Lhs[i-1].Type()),
					}, e)
			}
		}
		if e == nil {
			e = glang.DoExpr{Expr: glang.Tt}
		}

		// Determine RHS types, specially handling multiple returns from a function call.
		var rhsTypes []types.Type
		t := ctx.typeOf(init.Rhs)
		if tuple, ok := t.(*types.Tuple); ok {
			for i := range tuple.Len() {
				rhsTypes = append(rhsTypes, tuple.At(i).Type())
			}
		} else {
			rhsTypes = append(rhsTypes, t)
		}

		// collect the RHS expressions
		var rhsExprs []glang.Expr
		if 1 == len(init.Lhs) {
			rhsExprs = append(rhsExprs, ctx.expr(init.Rhs))
		} else {
			// RHS is a function call returning multiple things. Will introduce
			// extra let bindings to destructure those multiple returns.
			for i := range init.Lhs {
				rhsExprs = append(rhsExprs, glang.IdentExpr(fmt.Sprintf("$ret%d", i)))
			}
		}

		// Let bindings for RHSs including conversions
		for i := len(init.Lhs); i > 0; i-- {
			e = glang.LetExpr{
				Names: []string{fmt.Sprintf("$r%d", i-1)},
				ValExpr: ctx.handleImplicitConversion(init.Lhs[i-1], rhsTypes[i-1],
					init.Lhs[i-1].Type(), rhsExprs[i-1]),
				Cont: e,
			}
		}

		// Extra let bindings in case RHS is a multiple-returning function
		if 1 != len(init.Lhs) {
			var n []string
			for i := range init.Lhs {
				n = append(n, fmt.Sprintf("$ret%d", i))
			}
			e = glang.LetExpr{
				Names:   n,
				ValExpr: ctx.exprSpecial(init.Rhs, true),
				Cont:    e,
			}
		}
	}

	for _, importName := range ctx.importNamesOrdered {
		e = glang.NewDoSeq(glang.GallinaIdent(importName+"."+"initialize'"), e)
	}

	if e == nil {
		e = glang.DoExpr{Expr: glang.Tt}
	}

	e = glang.NewCallExpr(glang.GallinaIdent("exception_do"), e)
	e = glang.NewCallExpr(glang.GallinaIdent("globals.package_init"),
		glang.GallinaIdent("pkg_name'"),
		glang.GallinaIdent("vars'"),
		glang.GallinaIdent("functions'"),
		glang.GallinaIdent("msets'"),
		glang.FuncLit{Args: nil, Body: e},
	)

	initFunc.Body = e
	decls = append(decls, initFunc)

	return decls
}
