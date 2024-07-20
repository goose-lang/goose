// Package goose implements conversion from Go source to Perennial definitions.
//
// The exposed interface allows converting individual files as well as whole
// packages to a single Coq Ast with all the converted definitions, which
// include user-defined structs in Go as Coq records and a Perennial procedure
// for each Go function.
//
// See the Goose README at https://github.com/tchajed/goose for a high-level
// overview. The source also has some design documentation at
// https://github.com/tchajed/goose/tree/master/docs.
package goose

import (
	"bytes"
	"fmt"
	"go/ast"
	"go/constant"
	"go/printer"
	"go/token"
	"go/types"
	"strconv"
	"strings"
	"unicode"

	"github.com/tchajed/goose/glang"
	"golang.org/x/tools/go/packages"
)

// Ctx is a context for resolving Go code's types and source code
type Ctx struct {
	info    *types.Info
	Fset    *token.FileSet
	pkgPath string
	errorReporter

	dep *depTracker
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
func NewPkgCtx(pkg *packages.Package) Ctx {
	return Ctx{
		info:          pkg.TypesInfo,
		Fset:          pkg.Fset,
		pkgPath:       pkg.PkgPath,
		errorReporter: newErrorReporter(pkg.Fset),
	}
}

func (ctx Ctx) where(node ast.Node) string {
	return ctx.Fset.Position(node.Pos()).String()
}

func (ctx Ctx) printGo(node ast.Node) string {
	var what bytes.Buffer
	err := printer.Fprint(&what, ctx.Fset, node)
	if err != nil {
		panic(err.Error())
	}
	return what.String()
}

func (ctx Ctx) field(f *ast.Field) glang.FieldDecl {
	if len(f.Names) > 1 {
		ctx.futureWork(f, "multiple fields for same type (split them up)")
		return glang.FieldDecl{}
	}
	if len(f.Names) == 0 {
		ctx.unsupported(f, "unnamed field/parameter")
		return glang.FieldDecl{}
	}
	return glang.FieldDecl{
		Name: f.Names[0].Name,
		Type: ctx.glangTypeFromExpr(f.Type),
	}
}

func (ctx Ctx) paramList(fs *ast.FieldList) []glang.FieldDecl {
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

func (ctx Ctx) typeParamList(fs *ast.FieldList) []glang.TypeIdent {
	var typeParams []glang.TypeIdent
	if fs == nil {
		return nil
	}
	for _, f := range fs.List {
		for _, name := range f.Names {
			typeParams = append(typeParams, glang.TypeIdent(name.Name))
		}
		if len(f.Names) == 0 { // Unnamed parameter
			ctx.unsupported(fs, "unnamed type parameters")
		}
	}
	return typeParams
}

func (ctx Ctx) structFields(fs *ast.FieldList) []glang.FieldDecl {
	var decls []glang.FieldDecl
	for _, f := range fs.List {
		if len(f.Names) > 1 {
			ctx.futureWork(f, "multiple fields for same type (split them up)")
			return nil
		}
		if len(f.Names) == 0 {
			ctx.unsupported(f, "unnamed (embedded) field")
			return nil
		}
		ty := ctx.glangTypeFromExpr(f.Type)
		decls = append(decls, glang.FieldDecl{
			Name: f.Names[0].Name,
			Type: ty,
		})
	}
	return decls
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

func (ctx Ctx) addSourceFile(node ast.Node, comment *string) {
	if *comment != "" {
		*comment += "\n\n   "
	}
	*comment += fmt.Sprintf("go: %s", ctx.where(node))
}

func (ctx Ctx) methodSet(t *types.Named) glang.Decl {
	typeName := t.Obj().Name()
	d := glang.MethodSetDecl{
		TypeName:    typeName,
		MethodNames: []string{},
	}
	for i := range t.NumMethods() {
		d.MethodNames = append(d.MethodNames, t.Method(i).Name())
	}
	return d
}

func (ctx Ctx) typeDecl(spec *ast.TypeSpec) []glang.Decl {
	if spec.TypeParams != nil {
		ctx.futureWork(spec, "generic named type (e.g. no generic structs)")
	}
	var r []glang.Decl

	r = append(r, glang.TypeDecl{
		Name: spec.Name.Name,
		Body: ctx.glangTypeFromExpr(spec.Type),
	})

	if t, ok := ctx.typeOf(spec.Name).(*types.Named); ok {
		r = append(r, ctx.methodSet(t))
	}

	return r
}

func toInitialLower(s string) string {
	pastFirstLetter := false
	return strings.Map(func(r rune) rune {
		if !pastFirstLetter {
			newR := unicode.ToLower(r)
			pastFirstLetter = true
			return newR
		}
		return r
	}, s)
}

func (ctx Ctx) lenExpr(e *ast.CallExpr) glang.CallExpr {
	x := e.Args[0]
	xTy := ctx.typeOf(x)
	switch ty := xTy.Underlying().(type) {
	case *types.Slice:
		return glang.NewCallExpr(glang.GallinaIdent("slice.len"), ctx.expr(x))
	case *types.Map:
		return glang.NewCallExpr(glang.GallinaIdent("MapLen"), ctx.expr(x))
	case *types.Basic:
		if ty.Kind() == types.String {
			return glang.NewCallExpr(glang.GallinaIdent("StringLength"), ctx.expr(x))
		}
	}
	ctx.unsupported(e, "length of object of type %v", xTy)
	return glang.CallExpr{}
}

func (ctx Ctx) capExpr(e *ast.CallExpr) glang.CallExpr {
	x := e.Args[0]
	xTy := ctx.typeOf(x)
	switch xTy.Underlying().(type) {
	case *types.Slice:
		return glang.NewCallExpr(glang.GallinaIdent("slice.cap"), ctx.expr(x))
	}
	ctx.unsupported(e, "capacity of object of type %v", xTy)
	return glang.CallExpr{}
}

func (ctx Ctx) prophIdMethod(f *ast.SelectorExpr, args []ast.Expr) glang.CallExpr {
	callArgs := append([]ast.Expr{f.X}, args...)
	switch f.Sel.Name {
	case "ResolveBool", "ResolveU64":
		return ctx.newCoqCall(glang.GallinaIdent("ResolveProph"), callArgs)
	default:
		ctx.unsupported(f, "method %s of machine.ProphId", f.Sel.Name)
		return glang.CallExpr{}
	}
}

func (ctx Ctx) packageMethod(f *ast.SelectorExpr,
	call *ast.CallExpr) glang.Expr {
	args := call.Args
	pkg := f.X.(*ast.Ident)
	return ctx.newCoqCall(glang.PackageIdent{Package: pkg.Name, Ident: f.Sel.Name}, args)
}

func (ctx Ctx) newCoqCall(method glang.Expr, es []ast.Expr) glang.CallExpr {
	var args []glang.Expr
	for _, e := range es {
		args = append(args, ctx.expr(e))
	}
	call := glang.NewCallExpr(method, args...)
	return call
}

func (ctx Ctx) methodExpr(call *ast.CallExpr) glang.Expr {
	if f, ok := call.Fun.(*ast.Ident); ok {
		if ctx.info.Instances[f].TypeArgs.Len() > 0 {
			ctx.unsupported(f, "generic function")
		}
	}

	return ctx.newCoqCall(ctx.expr(call.Fun), call.Args)
}

func (ctx Ctx) makeSliceExpr(elt glang.Type, args []ast.Expr) glang.CallExpr {
	if len(args) == 2 {
		return glang.NewCallExpr(glang.GallinaIdent("slice.make2"), elt, ctx.expr(args[1]))
	} else if len(args) == 3 {
		return glang.NewCallExpr(glang.GallinaIdent("slice.make3"), elt, ctx.expr(args[1]), ctx.expr(args[2]))
	} else {
		ctx.unsupported(args[0], "Too many or too few arguments in slice construction")
		return glang.CallExpr{}
	}
}

// makeExpr parses a call to make() into the appropriate data-structure Call
func (ctx Ctx) makeExpr(args []ast.Expr) glang.Expr {
	switch ty := ctx.typeOf(args[0]).Underlying().(type) {
	case *types.Slice:
		elt := ctx.glangType(args[0], ty.Elem())
		if len(args) == 2 {
			return glang.NewCallExpr(glang.GallinaIdent("slice.make2"), elt, ctx.expr(args[1]))
		} else if len(args) == 3 {
			return glang.NewCallExpr(glang.GallinaIdent("slice.make3"), elt, ctx.expr(args[1]), ctx.expr(args[2]))
		} else {
			ctx.nope(args[0], "Too many or too few arguments in slice construction")
			return glang.CallExpr{}
		}
	case *types.Map:
		return glang.NewCallExpr(glang.GallinaIdent("map.make"),
			ctx.glangType(args[0], ty.Key()),
			ctx.glangType(args[0], ty.Elem()),
			glang.UnitLiteral{})
	default:
		ctx.unsupported(args[0],
			"make of should be slice or map, got %v", ty)
	}
	return glang.CallExpr{}
}

// newExpr parses a call to new() into an appropriate allocation
func (ctx Ctx) newExpr(ty ast.Expr) glang.Expr {
	return glang.RefExpr{
		X:  glang.NewCallExpr(glang.GallinaIdent("zero_val"), ctx.glangTypeFromExpr(ty)),
		Ty: ctx.glangTypeFromExpr(ty),
	}
}

// integerConversion generates an expression for converting x to an integer
// of a specific width
//
// s is only used for error reporting
func (ctx Ctx) integerConversion(s ast.Node, x ast.Expr, width int) glang.Expr {
	if info, ok := getIntegerType(ctx.typeOf(x)); ok {
		if info.isUntyped {
			ctx.todo(s, "conversion from untyped int to uint64")
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

func (ctx Ctx) copyExpr(n ast.Node, dst ast.Expr, src ast.Expr) glang.Expr {
	e := sliceElem(ctx.typeOf(dst))
	return glang.NewCallExpr(glang.GallinaIdent("slice.copy"),
		ctx.glangType(n, e),
		ctx.expr(dst), ctx.expr(src))
}

func (ctx Ctx) conversionExpr(s *ast.CallExpr) glang.Expr {
	if len(s.Args) != 1 {
		ctx.nope(s, "expect exactly one argument in a conversion")
	}
	toType := ctx.info.TypeOf(s.Fun).Underlying()
	fromType := ctx.info.TypeOf(s.Args[0]).Underlying()
	if toType == fromType {
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
			case types.Uint64:
				return ctx.integerConversion(s, s.Args[0], 64)
			case types.Uint32:
				return ctx.integerConversion(s, s.Args[0], 32)
			case types.Uint8:
				return ctx.integerConversion(s, s.Args[0], 8)
			}
		}

		// handle `string(b)`, where b : []byte
		if toType.Kind() == types.String && isByteSlice(fromType) {
			return ctx.newCoqCall(glang.GallinaIdent("StringFromBytes"), s.Args)
		}
	case *types.Slice:
		// handle `[]byte(s)`, where s : string
		if eltType, ok := toType.Elem().Underlying().(*types.Basic); ok &&
			eltType.Kind() == types.Byte && isString(fromType) {
			return ctx.newCoqCall(glang.GallinaIdent("StringToBytes"), s.Args)
		}
	}

	ctx.unsupported(s, "conversion from %s to %s", fromType, toType)
	return nil
}

func (ctx Ctx) builtinCallExpr(s *ast.CallExpr) glang.Expr {
	funName := s.Fun.(*ast.Ident).Name
	switch funName {
	case "make":
		return ctx.makeExpr(s.Args)
	case "new":
		return ctx.newExpr(s.Args[0])
	case "len":
		return ctx.lenExpr(s)
	case "cap":
		return ctx.capExpr(s)
	case "append":
		elemTy := sliceElem(ctx.typeOf(s.Args[0]))
		var xExpr glang.Expr = glang.GallinaIdent("slice.nil")

		// append(s, x1, x2, xn)
		if s.Ellipsis == token.NoPos {
			if len(s.Args) > 0 {
				var exprs []glang.Expr
				for _, arg := range s.Args[1:] {
					exprs = append(exprs, ctx.expr(arg))
				}
				xExpr = glang.NewCallExpr(glang.GallinaIdent("slice.literal"),
					// FIXME: get the type of the vararg
					ctx.glangType(s.Args[1], ctx.typeOf(s.Args[1])),
					glang.ListExpr(exprs))
			}
		} else {
			// append(s1, s2...)
			xExpr = ctx.expr(s.Args[1])
		}
		return glang.NewCallExpr(glang.GallinaIdent("slice.append"),
			ctx.glangType(s, elemTy),
			ctx.expr(s.Args[0]),
			xExpr,
		)
	case "copy":
		return ctx.copyExpr(s, s.Args[0], s.Args[1])
	case "delete":
		if _, ok := ctx.typeOf(s.Args[0]).(*types.Map); !ok {
			ctx.nope(s, "delete on non-map")
		}
		return glang.NewCallExpr(glang.GallinaIdent("MapDelete"), ctx.expr(s.Args[0]), ctx.expr(s.Args[1]))
	case "panic":
		msg := "oops"
		if e, ok := s.Args[0].(*ast.BasicLit); ok {
			if e.Kind == token.STRING {
				v := ctx.info.Types[e].Value
				msg = constant.StringVal(v)
			}
		}
		return glang.NewCallExpr(glang.GallinaIdent("Panic"), glang.GallinaString(msg))
	default:
		ctx.unsupported(s, "builtin %s not supported", funName)
		return nil
	}
}

func (ctx Ctx) callExpr(s *ast.CallExpr) glang.Expr {
	if ctx.info.Types[s.Fun].IsType() {
		return ctx.conversionExpr(s)
	} else if ctx.info.Types[s.Fun].IsBuiltin() {
		return ctx.builtinCallExpr(s)
	} else {
		return ctx.methodExpr(s)
	}
}

func (ctx Ctx) qualifiedName(obj types.Object) string {
	name := obj.Name()
	if obj.Pkg() == nil {
		return name
	} else if ctx.pkgPath == obj.Pkg().Path() {
		// no module name needed
		return name
	}
	return fmt.Sprintf("%s.%s", obj.Pkg().Name(), name)
}

func (ctx Ctx) selectorExpr(e *ast.SelectorExpr) glang.Expr {
	selectorType, ok := ctx.getType(e.X)
	if !ok {
		if isIdent(e.X, "filesys") {
			return glang.GallinaIdent("FS." + e.Sel.Name)
		}
		if isIdent(e.X, "disk") {
			return glang.GallinaIdent("disk." + e.Sel.Name)
		}
		if pkg, ok := getIdent(e.X); ok {
			return glang.PackageIdent{
				Package: pkg,
				Ident:   e.Sel.Name,
			}
		}
	}
	structInfo, ok := ctx.getStructInfo(selectorType)

	if ok {
		// Check if select expression refers to a field of the struct
		isField := false
		for i := 0; i < structInfo.structType.NumFields(); i++ {
			if structInfo.structType.Field(i).Name() == e.Sel.Name {
				isField = true
				break
			}
		}
		if isField {
			return glang.DerefExpr{
				X:  ctx.exprAddr(e),
				Ty: ctx.glangType(e, ctx.typeOf(e)),
			}
		}
	}
	// must be method
	m := glang.TypeMethod(structInfo.name, e.Sel.Name)
	ctx.dep.addDep(m)
	return glang.NewCallExpr(glang.GallinaIdent(m), ctx.expr(e.X))
}

func (ctx Ctx) compositeLiteral(e *ast.CompositeLit) glang.Expr {
	if t, ok := ctx.typeOf(e).Underlying().(*types.Slice); ok {
		var args glang.ListExpr
		for _, e := range e.Elts {
			args = append(args, ctx.expr(e))
		}
		return glang.NewCallExpr(glang.GallinaIdent("slice.literal"),
			ctx.glangType(e, t.Elem()),
			args)
	}
	info, ok := ctx.getStructInfo(ctx.typeOf(e))
	if ok {
		return ctx.structLiteral(info, e)
	}
	ctx.unsupported(e, "composite literal of type %v", ctx.typeOf(e))
	return nil
}

func (ctx Ctx) structLiteral(info structTypeInfo, e *ast.CompositeLit) glang.StructLiteral {
	ctx.dep.addDep(info.name)
	lit := glang.NewStructLiteral(info.name)
	isUnkeyedStruct := false
	for _, el := range e.Elts {
		switch el := el.(type) {
		case *ast.KeyValueExpr:
			ident, ok := getIdent(el.Key)
			if !ok {
				ctx.noExample(el.Key, "struct field keyed by non-identifier %+v", el.Key)
				return glang.StructLiteral{}
			}
			lit.AddField(ident, ctx.expr(el.Value))
		default:
			isUnkeyedStruct = true
		}
	}
	if isUnkeyedStruct {
		if len(e.Elts) != info.structType.NumFields() {
			ctx.nope(e, "expected as many elements are there are struct fields in unkeyed literal")
		}
		for i := range info.structType.NumFields() {
			lit.AddField(info.structType.Field(i).Name(), ctx.expr(e.Elts[i]))
		}
	}
	return lit
}

// basicLiteral translates a basic literal
//
// (unsigned) ints, strings, and booleans are supported
func (ctx Ctx) basicLiteral(e *ast.BasicLit) glang.Expr {
	if e.Kind == token.STRING {
		v := ctx.info.Types[e].Value
		s := constant.StringVal(v)
		if strings.ContainsRune(s, '"') {
			ctx.unsupported(e, "string literals with quotes")
		}
		return glang.StringLiteral{Value: s}
	}
	if e.Kind == token.INT {
		tv := ctx.info.Types[e]
		switch t := tv.Type.Underlying().(type) {
		case *types.Basic:
			switch t.Name() {
			case "uint64":
				n, ok := constant.Uint64Val(tv.Value)
				if !ok {
					ctx.nope(e, "uint64 literal with failed constant.Uint64Val")
				}
				return glang.IntLiteral{Value: n}
			case "uint32":
				n, ok := constant.Uint64Val(tv.Value)
				if !ok {
					ctx.nope(e, "uint32 literal with failed constant.Uint64Val")
				}
				return glang.Int32Literal{Value: uint32(n)}
			case "uint8":
				fallthrough
			case "byte":
				n, ok := constant.Uint64Val(tv.Value)
				if !ok {
					ctx.nope(e, "uint8 literal with failed constant.Uint64Val")
				}
				return glang.ByteLiteral{Value: uint8(n)}
			case "int": // FIXME: this case is a temporary hack to support e.g. the int in `make([]byte, 20)`
				n, ok := constant.Uint64Val(tv.Value)
				if !ok {
					ctx.todo(e, "int literal with negative value")
				}
				return glang.IntLiteral{Value: n}
			case "untyped int": // FIXME: this case is a temporary hack to support e.g. the int in `make([]byte, 20)`
				n, ok := constant.Uint64Val(tv.Value)
				if !ok {
					ctx.todo(e, "int literal with negative value")
				}
				return glang.IntLiteral{Value: n}
			default:
				ctx.todo(e, "%s integer literal", t.Name())
				return glang.Tt
			}
		}
		ctx.nope(e, "integer literal with unexpected underlying type that's %T", tv.Type.Underlying())
	}
	ctx.unsupported(e, "literal with kind %s", e.Kind)
	return nil
}

func (ctx Ctx) isNilCompareExpr(e *ast.BinaryExpr) bool {
	if !(e.Op == token.EQL || e.Op == token.NEQ) {
		return false
	}
	return ctx.info.Types[e.Y].IsNil()
}

func (ctx Ctx) binExpr(e *ast.BinaryExpr) glang.Expr {
	op, ok := map[token.Token]glang.BinOp{
		token.LSS:  glang.OpLessThan,
		token.GTR:  glang.OpGreaterThan,
		token.SUB:  glang.OpMinus,
		token.EQL:  glang.OpEquals,
		token.NEQ:  glang.OpNotEquals,
		token.MUL:  glang.OpMul,
		token.QUO:  glang.OpQuot,
		token.REM:  glang.OpRem,
		token.LEQ:  glang.OpLessEq,
		token.GEQ:  glang.OpGreaterEq,
		token.AND:  glang.OpAnd,
		token.LAND: glang.OpLAnd,
		token.OR:   glang.OpOr,
		token.LOR:  glang.OpLOr,
		token.XOR:  glang.OpXor,
		token.SHL:  glang.OpShl,
		token.SHR:  glang.OpShr,
	}[e.Op]
	if e.Op == token.ADD {
		if isString(ctx.typeOf(e.X)) {
			op = glang.OpAppend
		} else {
			op = glang.OpPlus
		}
		ok = true
	}
	if ok {
		expr := glang.BinaryExpr{
			X:  ctx.expr(e.X),
			Op: op,
			Y:  ctx.expr(e.Y),
		}
		if ctx.isNilCompareExpr(e) {
			if _, ok := ctx.typeOf(e.X).(*types.Pointer); ok {
				expr.Y = glang.Null
			}
		}
		return expr
	}
	ctx.unsupported(e, "binary operator %v", e.Op)
	return nil
}

func (ctx Ctx) sliceExpr(e *ast.SliceExpr) glang.Expr {
	if e.Slice3 {
		ctx.unsupported(e, "3-index slice")
		return nil
	}
	if e.Max != nil {
		ctx.unsupported(e, "setting the max capacity in a slice expression is not supported")
		return nil
	}
	if e.Low == nil && e.High == nil {
		ctx.unsupported(e, "complete slice doesn't do anything")
	}

	x := ctx.expr(e.X)
	var lowExpr glang.Expr = glang.IntLiteral{Value: 0}
	var highExpr glang.Expr = glang.NewCallExpr(glang.GallinaIdent("slice.len"), glang.IdentExpr("$s"))
	if e.Low != nil {
		lowExpr = ctx.expr(e.Low)
	}
	if e.High != nil {
		highExpr = ctx.expr(e.High)
	}
	return glang.LetExpr{
		Names:   []string{"$s"},
		ValExpr: x,
		Cont: glang.NewCallExpr(glang.GallinaIdent("slice.slice"),
			ctx.glangType(e, sliceElem(ctx.typeOf(e.X))),
			glang.IdentExpr("$s"), lowExpr, highExpr),
	}
}

func (ctx Ctx) nilExpr(e *ast.Ident) glang.Expr {
	t := ctx.typeOf(e)
	switch t.(type) {
	case *types.Pointer:
		return glang.GallinaIdent("null")
	case *types.Slice:
		return glang.GallinaIdent("slice.nil")
	case *types.Basic:
		// TODO: this gets triggered for all of our unit tests because the
		//  nil identifier is mapped to an untyped nil object.
		//  This seems wrong; the runtime representation of each of these
		//  uses depends on the type, so Go must know how they're being used.
		return glang.GallinaIdent("slice.nil")
	default:
		ctx.unsupported(e, "nil of type %v (not pointer or slice)", t)
		return nil
	}
}

func (ctx Ctx) unaryExpr(e *ast.UnaryExpr) glang.Expr {
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
				return glang.NewCallExpr(glang.GallinaIdent("SliceRef"),
					ctx.glangType(e, xTy.Elem()),
					ctx.expr(x.X), ctx.expr(x.Index))
			}
		}
		if info, ok := ctx.getStructInfo(ctx.typeOf(e.X)); ok {
			structLit, ok := e.X.(*ast.CompositeLit)
			if ok {
				// e is &s{...} (a struct literal)
				sl := ctx.structLiteral(info, structLit)
				return glang.RefExpr{
					X:  sl,
					Ty: ctx.glangType(e.X, ctx.typeOf(e.X)),
				}
			}
		}
		// e is something else
		return ctx.exprAddr(e.X)
	}
	ctx.unsupported(e, "unary expression %s", e.Op)
	return nil
}

func (ctx Ctx) variable(s *ast.Ident) glang.Expr {
	if _, ok := ctx.info.Uses[s].(*types.Const); ok {
		ctx.dep.addDep(s.Name)
		return glang.GallinaIdent(s.Name)
	}
	return glang.DerefExpr{X: glang.IdentExpr(s.Name), Ty: ctx.glangType(s, ctx.typeOf(s))}
}

func (ctx Ctx) function(s *ast.Ident) glang.Expr {
	ctx.dep.addDep(s.Name)
	return glang.GallinaIdent(s.Name)
}

func (ctx Ctx) goBuiltin(e *ast.Ident) bool {
	s, ok := ctx.info.Uses[e]
	if !ok {
		return false
	}
	return s.Parent() == types.Universe
}

func (ctx Ctx) identExpr(e *ast.Ident) glang.Expr {
	if ctx.goBuiltin(e) {
		switch e.Name {
		case "nil":
			return ctx.nilExpr(e)
		case "true":
			return glang.True
		case "false":
			return glang.False
		}
		ctx.unsupported(e, "special identifier")
	}

	// check if e refers to a variable,
	obj := ctx.info.ObjectOf(e)
	if _, ok := obj.(*types.Const); ok {
		// is a variable
		return ctx.variable(e)
	}
	if _, ok := obj.(*types.Var); ok {
		// is a variable
		return ctx.variable(e)
	}
	if _, ok := obj.(*types.Func); ok {
		// is a function
		return ctx.function(e)
	}
	ctx.unsupported(e, "unrecognized kind of identifier; not local variable or global function")
	panic("")
}

func (ctx Ctx) indexExpr(e *ast.IndexExpr, isSpecial bool) glang.Expr {
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
	case *types.Signature:
		ctx.unsupported(e, "generic function %v", xTy)
	}
	ctx.unsupported(e, "index into unknown type %v", xTy)
	return glang.CallExpr{}
}

func (ctx Ctx) derefExpr(e ast.Expr) glang.Expr {
	return glang.DerefExpr{
		X:  ctx.expr(e),
		Ty: ctx.glangType(e, ptrElem(ctx.typeOf(e))),
	}
}

func (ctx Ctx) expr(e ast.Expr) glang.Expr {
	return ctx.exprSpecial(e, false)
}

func (ctx Ctx) funcLit(e *ast.FuncLit) glang.FuncLit {
	fl := glang.FuncLit{}

	fl.Args = ctx.paramList(e.Type.Params)
	// fl.ReturnType = ctx.returnType(d.Type.Results)
	fl.Body = ctx.blockStmt(e.Body)
	return fl
}

func (ctx Ctx) exprSpecial(e ast.Expr, isSpecial bool) glang.Expr {
	switch e := e.(type) {
	case *ast.CallExpr:
		return ctx.callExpr(e)
	case *ast.Ident:
		return ctx.identExpr(e)
	case *ast.SelectorExpr:
		return ctx.selectorExpr(e)
	case *ast.CompositeLit:
		return ctx.compositeLiteral(e)
	case *ast.BasicLit:
		return ctx.basicLiteral(e)
	case *ast.BinaryExpr:
		return ctx.binExpr(e)
	case *ast.SliceExpr:
		return ctx.sliceExpr(e)
	case *ast.IndexExpr:
		return ctx.indexExpr(e, isSpecial)
	case *ast.UnaryExpr:
		return ctx.unaryExpr(e)
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

func (ctx Ctx) blockStmt(s *ast.BlockStmt) glang.Expr {
	ss := s.List
	var e glang.Expr = glang.DoExpr{Expr: glang.Tt}
	for len(ss) > 0 {
		stmt := ss[len(ss)-1]
		ss = ss[:len(ss)-1]
		e = ctx.stmt(stmt, e)
	}
	return e
}

func (ctx Ctx) ifStmt(s *ast.IfStmt, cont glang.Expr) glang.Expr {
	var elseExpr glang.Expr = glang.DoExpr{Expr: glang.Tt}
	if s.Else != nil {
		elseExpr = ctx.stmt(s.Else, glang.Tt)
	}
	ife := glang.IfExpr{
		Cond: ctx.expr(s.Cond),
		Then: ctx.blockStmt(s.Body),
		Else: elseExpr,
	}

	if s.Init != nil {
		ctx.unsupported(s.Init, "if statement initializations")
	}
	return glang.LetExpr{ValExpr: ife, Cont: cont}
}

func (ctx Ctx) loopVar(s ast.Stmt) (ident *ast.Ident, init glang.Expr) {
	initAssign, ok := s.(*ast.AssignStmt)
	if !ok ||
		len(initAssign.Lhs) > 1 ||
		len(initAssign.Rhs) > 1 ||
		initAssign.Tok != token.DEFINE {
		ctx.unsupported(s, "loop initialization must be a single assignment")
		return nil, nil
	}
	lhs, ok := initAssign.Lhs[0].(*ast.Ident)
	if !ok {
		ctx.nope(s, "initialization must define an identifier")
	}
	rhs := initAssign.Rhs[0]
	return lhs, ctx.expr(rhs)
}

func (ctx Ctx) forStmt(s *ast.ForStmt, cont glang.Expr) glang.Expr {
	var cond glang.Expr = glang.True
	if s.Cond != nil {
		cond = ctx.expr(s.Cond)
	}
	var post glang.Expr = glang.Skip
	if s.Post != nil {
		post = ctx.stmt(s.Post, glang.Tt)
	}

	body := ctx.blockStmt(s.Body)
	var e glang.Expr = glang.ForLoopExpr{
		Cond: cond,
		Post: post,
		Body: body,
	}
	if s.Init != nil {
		e = glang.ParenExpr{Inner: ctx.stmt(s.Init, e)}
	}
	return glang.LetExpr{ValExpr: e, Cont: cont}
}

func getIdentOrAnonymous(e ast.Expr) (ident string, ok bool) {
	if e == nil {
		return "_", true
	}
	return getIdent(e)
}

func (ctx Ctx) mapRangeStmt(s *ast.RangeStmt) glang.Expr {
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
		Body:       ctx.blockStmt(s.Body),
	}
}

func getIdentOrNil(e ast.Expr) *ast.Ident {
	if id, ok := e.(*ast.Ident); ok {
		return id
	}
	return nil
}

func (ctx Ctx) identBinder(id *ast.Ident) glang.Binder {
	if id == nil {
		return glang.Binder(nil)
	}
	e := glang.IdentExpr(id.Name)
	return &e
}

func (ctx Ctx) sliceRangeStmt(s *ast.RangeStmt) glang.Expr {
	if s.Tok != token.DEFINE {
		ctx.unsupported(s.Key, "range with pre-existing variables")
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
		Body:  ctx.blockStmt(s.Body),
	}
	return glang.LetExpr{
		Names:   []string{"$range"},
		ValExpr: ctx.expr(s.X),
		Cont:    e,
	}
}

func (ctx Ctx) rangeStmt(s *ast.RangeStmt) glang.Expr {
	switch ctx.typeOf(s.X).(type) {
	case *types.Map:
		return ctx.mapRangeStmt(s)
	case *types.Slice:
		return ctx.sliceRangeStmt(s)
	default:
		ctx.unsupported(s,
			"range over %v (only maps and slices are supported)",
			ctx.typeOf(s.X))
		return nil
	}
}

func (ctx Ctx) referenceTo(rhs ast.Expr) glang.Expr {
	return glang.RefExpr{
		X:  ctx.expr(rhs),
		Ty: ctx.glangType(rhs, ctx.typeOf(rhs)),
	}
}

func (ctx Ctx) defineStmt(s *ast.AssignStmt, cont glang.Expr) glang.Expr {
	e := ctx.assignStmt(s, cont)

	// Before the asignStmt "e", allocate everything that's new in this define stmt.
	for _, lhsExpr := range s.Lhs {
		if ident, ok := lhsExpr.(*ast.Ident); ok {
			if _, ok := ctx.info.Defs[ident]; ok { // if this identifier is defining something
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

func (ctx Ctx) varSpec(s *ast.ValueSpec, cont glang.Expr) glang.Expr {
	if len(s.Names) > 1 {
		ctx.unsupported(s, "multiple declarations in one block")
	}
	lhs := s.Names[0]
	var rhs glang.Expr
	if len(s.Values) == 0 {
		ty := ctx.glangTypeFromExpr(lhs)
		rhs = glang.NewCallExpr(glang.GallinaIdent("ref_ty"), ty,
			glang.NewCallExpr(glang.GallinaIdent("zero_val"), ty))
	} else {
		rhs = ctx.referenceTo(s.Values[0])
	}
	return glang.LetExpr{
		Names:   []string{lhs.Name},
		ValExpr: rhs,
		Cont:    cont,
	}
}

// varDeclStmt translates declarations within functions
func (ctx Ctx) varDeclStmt(s *ast.DeclStmt, cont glang.Expr) glang.Expr {
	decl, ok := s.Decl.(*ast.GenDecl)
	if !ok {
		ctx.noExample(s, "declaration that is not a GenDecl")
	}
	if decl.Tok != token.VAR {
		ctx.unsupported(s, "non-var declaration for %v", decl.Tok)
	}
	if len(decl.Specs) > 1 {
		ctx.unsupported(s, "multiple declarations in one var statement")
	}
	// guaranteed to be a *Ast.ValueSpec due to decl.Tok
	//
	// https://golang.org/pkg/go/ast/#GenDecl
	// TODO: handle TypeSpec
	return ctx.varSpec(decl.Specs[0].(*ast.ValueSpec), cont)
}

// Returns the address of the given expression.
// Requires that e is actually addressable
func (ctx Ctx) exprAddr(e ast.Expr) glang.Expr {
	switch e := e.(type) {
	case *ast.ParenExpr:
		return ctx.exprAddr(e.X)
	case *ast.Ident:
		return glang.IdentExpr(e.Name)
	case *ast.IndexExpr:
		targetTy := ctx.typeOf(e.X)
		switch targetTy := targetTy.(type) {
		case *types.Slice:
			return glang.NewCallExpr(glang.GallinaIdent("slice.elem_ref"),
				ctx.glangType(e, targetTy.Elem()),
				ctx.expr(e.X),
				ctx.expr(e.Index))
		case *types.Map:
			ctx.nope(e, "map index expressions are not addressable")
		default:
			ctx.unsupported(e, "index update to unexpected target of type %v", targetTy)
		}
	case *ast.StarExpr:
		return ctx.expr(e.X)
	case *ast.SelectorExpr:
		// if it's the base of the SelectorExpr is a struct, then this is a struct.field_ref
		ty := ctx.typeOf(e.X)
		info, ok := ctx.getStructInfo(ty)
		if !ok {
			ctx.unsupported(e, "address of selector expression that's not a struct field %v", ty)
		}
		ctx.dep.addDep(info.name)

		var structExpr glang.Expr
		if info.throughPointer {
			structExpr = ctx.expr(e.X)
		} else {
			structExpr = ctx.exprAddr(e.X)
		}
		return glang.NewCallExpr(glang.GallinaIdent("struct.field_ref"),
			glang.StructDesc(info.name),
			glang.GallinaString(e.Sel.Name),
			structExpr)
	default:
		ctx.unsupported(e, "address of unknown expression")
	}
	return nil
}

func (ctx Ctx) assignFromTo(lhs ast.Expr, rhs glang.Expr, cont glang.Expr) glang.Expr {
	// lhs should either be a map index expression, or is addressable
	switch lhs := lhs.(type) {
	case *ast.Ident:
		if lhs.Name == "_" {
			return glang.NewDoSeq(rhs, cont)
		}
	case *ast.IndexExpr:
		targetTy := ctx.typeOf(lhs.X)
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

func (ctx Ctx) assignStmt(s *ast.AssignStmt, cont glang.Expr) glang.Expr {
	e := cont

	// do assignments left-to-right
	intermediates := make([]string, 0, len(s.Lhs))
	for i, lhs := range s.Lhs {
		intermediates = append(intermediates, fmt.Sprintf("$a%d", i))
		e = ctx.assignFromTo(lhs, glang.IdentExpr(intermediates[i]), e)
	}

	// FIXME:(evaluation order)
	// compute values left-to-right
	for i := len(s.Rhs); i > 0; i-- {
		// NOTE: this handles the case that RHS = multiple-return function call
		e = glang.LetExpr{
			Names:   intermediates[i-1:],
			ValExpr: ctx.expr(s.Rhs[i-1]),
			Cont:    e,
		}
		intermediates = intermediates[:i-1]
	}

	return e
}

func (ctx Ctx) assignOpStmt(s *ast.AssignStmt, cont glang.Expr) glang.Expr {
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

func (ctx Ctx) incDecStmt(stmt *ast.IncDecStmt, cont glang.Expr) glang.Expr {
	op := glang.OpPlus
	if stmt.Tok == token.DEC {
		op = glang.OpMinus
	}
	return ctx.assignFromTo(stmt.X, glang.BinaryExpr{
		X:  ctx.expr(stmt.X),
		Op: op,
		Y:  glang.IntLiteral{Value: 1},
	}, cont)
}

func (ctx Ctx) branchStmt(s *ast.BranchStmt, cont glang.Expr) glang.Expr {
	if s.Tok == token.CONTINUE {
		return glang.LetExpr{ValExpr: glang.ContinueExpr{}, Cont: cont}
	}
	if s.Tok == token.BREAK {
		return glang.LetExpr{ValExpr: glang.BreakExpr{}, Cont: cont}
	}
	ctx.noExample(s, "unexpected control flow %v in loop", s.Tok)
	return nil
}

// getSpawn returns a non-nil spawned thread if the expression is a go call
func (ctx Ctx) goStmt(e *ast.GoStmt, cont glang.Expr) glang.Expr {
	args := make([]glang.Expr, 0, len(e.Call.Args))
	for i := range len(e.Call.Args) {
		args = append(args, glang.IdentExpr(fmt.Sprintf("$arg%d", i)))
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

	// FIXME:(evaluation order)
	// compute values left-to-right
	for i := len(e.Call.Args); i > 0; i-- {
		expr = glang.LetExpr{
			Names:   []string{fmt.Sprintf("$arg%d", i-1)},
			ValExpr: ctx.expr(e.Call.Args[i-1]),
			Cont:    expr,
		}
	}

	return expr
}

func (ctx Ctx) returnStmt(s *ast.ReturnStmt, cont glang.Expr) glang.Expr {
	exprs := make([]glang.Expr, 0, len(s.Results))
	for _, result := range s.Results {
		exprs = append(exprs, ctx.expr(result))
	}
	if len(exprs) == 0 { // return #()
		exprs = []glang.Expr{glang.Tt}
	}
	r := glang.ReturnExpr{Value: glang.TupleExpr(exprs)}
	return glang.LetExpr{ValExpr: r, Cont: cont}
}

func (ctx Ctx) stmt(s ast.Stmt, cont glang.Expr) glang.Expr {
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
		return ctx.blockStmt(s)
	case *ast.SwitchStmt:
		ctx.todo(s, "switch statement")
	case *ast.TypeSwitchStmt:
		ctx.todo(s, "type switch statement")
	default:
		ctx.unsupported(s, "statement %T", s)
	}
	panic("unreachable")
}

func (ctx Ctx) returnExpr(es []ast.Expr) glang.Expr {
	if len(es) == 0 {
		// named returns are not supported, so this must return unit
		return glang.ReturnExpr{Value: glang.UnitLiteral{}}
	}
	var exprs glang.TupleExpr
	for _, r := range es {
		exprs = append(exprs, ctx.expr(r))
	}
	return glang.ReturnExpr{Value: glang.NewTuple(exprs)}
}

// returnType converts an Ast.FuncType's Results to a Coq return type
func (ctx Ctx) returnType(results *ast.FieldList) glang.Type {
	if results == nil {
		return glang.TypeIdent("unitT")
	}
	rs := results.List
	for _, r := range rs {
		if len(r.Names) > 0 {
			ctx.unsupported(r, "named returned value")
			return glang.TypeIdent("<invalid>")
		}
	}
	var ts []glang.Type
	for _, r := range rs {
		if len(r.Names) > 0 {
			ctx.unsupported(r, "named returned value")
			return glang.TypeIdent("<invalid>")
		}
		ts = append(ts, ctx.glangTypeFromExpr(r.Type))
	}
	return glang.NewTupleType(ts)
}

func (ctx Ctx) funcDecl(d *ast.FuncDecl) glang.FuncDecl {
	fd := glang.FuncDecl{Name: d.Name.Name}
	addSourceDoc(d.Doc, &fd.Comment)
	// ctx.addSourceFile(d, &fd.Comment)
	fd.TypeParams = ctx.typeParamList(d.Type.TypeParams)
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
		f := ctx.field(receiver)
		fd.RecvArg = &f
	}

	fd.Args = append(fd.Args, ctx.paramList(d.Type.Params)...)

	fd.ReturnType = ctx.returnType(d.Type.Results)
	fd.Body = ctx.blockStmt(d.Body)
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
	fd.Body = glang.NewCallExpr(glang.GallinaIdent("exception_do"), fd.Body)
	ctx.dep.addName(fd.Name)
	return fd
}

func (ctx Ctx) constSpec(spec *ast.ValueSpec) glang.ConstDecl {
	ident := spec.Names[0]
	cd := glang.ConstDecl{
		Name: ident.Name,
	}
	addSourceDoc(spec.Comment, &cd.Comment)
	if len(spec.Values) == 0 {
		ctx.todo(spec, "global var/const with no values")
	}
	val := spec.Values[0]
	cd.Val = ctx.expr(val)
	if spec.Type == nil {
		cd.Type = ctx.glangType(spec, ctx.typeOf(val))
	} else {
		cd.Type = ctx.glangTypeFromExpr(spec.Type)
	}
	cd.Val = ctx.expr(spec.Values[0])
	return cd
}

func (ctx Ctx) constDecl(d *ast.GenDecl) []glang.Decl {
	var specs []glang.Decl
	for _, spec := range d.Specs {
		vs := spec.(*ast.ValueSpec)
		ctx.dep.addName(vs.Names[0].Name)
		specs = append(specs, ctx.constSpec(vs))
	}
	return specs
}

func (ctx Ctx) globalVarDecl(d *ast.GenDecl) []glang.Decl {
	// FIXME: this treats globals as constants, which is unsound but used for a
	// configurable Debug level in goose-nfsd. Configuration variables should
	// instead be treated as a non-deterministic constant, assuming they aren't
	// changed after startup.
	var specs []glang.Decl
	for _, spec := range d.Specs {
		vs := spec.(*ast.ValueSpec)
		ctx.dep.addName(vs.Names[0].Name)
		specs = append(specs, ctx.constSpec(vs))
	}
	return specs
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
	"github.com/mit-pdos/gokv/grove_ffi":          "grove",
	"github.com/tchajed/goose/machine/disk":       "disk",
	"github.com/tchajed/goose/machine/async_disk": "async_disk",
}

func (ctx Ctx) imports(d []ast.Spec) []glang.Decl {
	var decls []glang.Decl
	for _, s := range d {
		s := s.(*ast.ImportSpec)
		if s.Name != nil {
			ctx.unsupported(s, "renaming imports")
		}
		importPath := stringLitValue(s.Path)
		// TODO: this uses the syntax of the Go import to determine the Coq
		// import, but Go packages can contain a different name than their
		// path. We can get this information by using the *types.Package
		// returned by Check (or the pkg.Types field from *packages.Package).
		decls = append(decls, glang.ImportDecl{Path: importPath})
	}
	return decls
}

// TODO: this is a hack, should have a better scheme for putting
// interface/implementation types into the conversion name
func unqualifyName(name string) string {
	components := strings.Split(name, ".")
	// return strings.Join(components[1:], "")
	return components[len(components)-1]
}

func (ctx Ctx) maybeDecls(d ast.Decl) []glang.Decl {
	switch d := d.(type) {
	case *ast.FuncDecl:
		fd := ctx.funcDecl(d)
		return []glang.Decl{fd}
	case *ast.GenDecl:
		switch d.Tok {
		case token.IMPORT:
			return ctx.imports(d.Specs)
		case token.CONST:
			return ctx.constDecl(d)
		case token.VAR:
			return ctx.globalVarDecl(d)
		case token.TYPE:
			if len(d.Specs) > 1 {
				ctx.noExample(d, "multiple specs in a type decl")
			}
			spec := d.Specs[0].(*ast.TypeSpec)
			ctx.dep.addName(spec.Name.Name)
			return ctx.typeDecl(spec)
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
