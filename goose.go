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
	"go/importer"
	"go/printer"
	"go/token"
	"go/types"
	"strconv"
	"strings"
	"unicode"

	"github.com/tchajed/goose/internal/glang"
	"golang.org/x/tools/go/packages"
)

// Ctx is a context for resolving Go code's types and source code
type Ctx struct {
	info    *types.Info
	Fset    *token.FileSet
	pkgPath string
	errorReporter
	Config

	dep *depTracker
}

// Says how the result of the currently generated expression will be used
type ExprValUsage int

const (
	// The result of this expression will only be used locally,
	// or entirely discarded
	ExprValLocal ExprValUsage = iota
	// The result of this expression will be returned from the current function
	// (i.e., the "early return" control effect is available here)
	ExprValReturned
	// The result of this expression will control the current loop
	// (i.e., the "break/continue" control effect is available here)
	ExprValLoop
)

// Config holds global configuration for Coq conversion
type Config struct {
	AddSourceFileComments bool
	TypeCheck             bool
	Ffi                   string
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
func NewPkgCtx(pkg *packages.Package, tr Translator) Ctx {
	// Figure out which FFI we're using
	var config Config
	// TODO: this duplication is bad, Config should probably embed Translator or
	//   some other cleanup is needed
	config.TypeCheck = tr.TypeCheck
	config.AddSourceFileComments = tr.AddSourceFileComments
	config.Ffi = getFfi(pkg)

	return Ctx{
		info:          pkg.TypesInfo,
		Fset:          pkg.Fset,
		pkgPath:       pkg.PkgPath,
		errorReporter: newErrorReporter(pkg.Fset),
		Config:        config,
	}
}

// NewCtx loads a context for files passed directly,
// rather than loaded from a packages.
func NewCtx(pkgPath string, conf Config) Ctx {
	info := &types.Info{
		Defs: make(map[*ast.Ident]types.Object),
		Uses: make(map[*ast.Ident]types.Object),
		// TODO: these instances give the generic arguments of function
		//  calls, use those
		Instances: make(map[*ast.Ident]types.Instance),
		Types:     make(map[ast.Expr]types.TypeAndValue),
		Scopes:    make(map[ast.Node]*types.Scope),
	}
	fset := token.NewFileSet()
	return Ctx{
		info:          info,
		Fset:          fset,
		pkgPath:       pkgPath,
		errorReporter: newErrorReporter(fset),
		Config:        conf,
	}
}

// FIXME: this is currently never called
// TypeCheck type-checks a set of files and stores the result in the Ctx
//
// This is needed before conversion to Coq to disambiguate some methods.
func (ctx Ctx) TypeCheck(files []*ast.File) error {
	imp := importer.ForCompiler(ctx.Fset, "source", nil)
	conf := types.Config{Importer: imp}
	_, err := conf.Check(ctx.pkgPath, ctx.Fset, files, ctx.info)
	return err
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
		Type: ctx.coqType(f.Type),
	}
}

func (ctx Ctx) paramList(fs *ast.FieldList) []glang.FieldDecl {
	var decls []glang.FieldDecl
	for _, f := range fs.List {
		ty := ctx.coqType(f.Type)
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
		ty := ctx.coqType(f.Type)
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
	if !ctx.AddSourceFileComments {
		return
	}
	if *comment != "" {
		*comment += "\n\n   "
	}
	*comment += fmt.Sprintf("go: %s", ctx.where(node))
}

func (ctx Ctx) typeDecl(spec *ast.TypeSpec) glang.Decl {
	if spec.TypeParams != nil {
		ctx.futureWork(spec, "generic named type (e.g. no generic structs)")
	}
	switch goTy := spec.Type.(type) {
	case *ast.StructType:
		// FIXME: why was this needed?
		// ctx.addDef(spec.Name, identInfo{
		// 	IsPtrWrapped: false,
		// 	IsMacro:      false,
		// })

		decl := glang.StructDecl{
			Name: spec.Name.Name,
		}
		addSourceDoc(spec.Doc, &decl.Comment)
		ctx.addSourceFile(spec, &decl.Comment)
		decl.Fields = ctx.structFields(goTy.Fields)
		return decl
	case *ast.InterfaceType:
		ctx.futureWork(spec, "interface type declaration")
		panic("unreachable")
	default:
		return glang.TypeDecl{
			Name: spec.Name.Name,
			Body: ctx.coqType(spec.Type),
		}
	}
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
		return ctx.newCoqCall("ResolveProph", callArgs)
	default:
		ctx.unsupported(f, "method %s of machine.ProphId", f.Sel.Name)
		return glang.CallExpr{}
	}
}

func (ctx Ctx) packageMethod(f *ast.SelectorExpr,
	call *ast.CallExpr) glang.Expr {
	args := call.Args
	pkg := f.X.(*ast.Ident)
	return ctx.newCoqCallTypeArgs(
		glang.PackageIdent{Package: pkg.Name, Ident: f.Sel.Name},
		ctx.typeList(call, ctx.info.Instances[f.Sel].TypeArgs),
		args)
}

func (ctx Ctx) selectorMethod(f *ast.SelectorExpr,
	call *ast.CallExpr) glang.Expr {
	args := call.Args
	selectorType, ok := ctx.getType(f.X)
	if !ok {
		return ctx.packageMethod(f, call)
	}
	if isProphId(selectorType) {
		return ctx.prophIdMethod(f, args)
	}
	if isDisk(selectorType) {
		method := fmt.Sprintf("disk.%s", f.Sel)
		// skip disk argument (f.X) and just pass the method arguments
		return ctx.newCoqCall(method, call.Args)
	}
	switch selectorType.Underlying().(type) {
	case *types.Interface:
		interfaceInfo, ok := ctx.getInterfaceInfo(selectorType)
		if ok {
			callArgs := append([]ast.Expr{f.X}, args...)
			return ctx.newCoqCall(
				glang.InterfaceMethod(interfaceInfo.name, f.Sel.Name),
				callArgs)
		}
	default:
		structInfo, ok := ctx.getStructInfo(selectorType)

		// see if f.Sel.Name is a struct field, and translate accordingly if so
		for _, name := range structInfo.fields() {
			if f.Sel.Name == name {
				return ctx.newCoqCallWithExpr(
					ctx.structSelector(structInfo, f),
					args)
			}
		}

		if ok {
			callArgs := append([]ast.Expr{f.X}, args...)
			m := glang.StructMethod(structInfo.name, f.Sel.Name)
			ctx.dep.addDep(m)
			return ctx.newCoqCall(m, callArgs)
		}
	}
	ctx.unsupported(f, "unexpected select on type "+selectorType.String())
	return nil
}

func (ctx Ctx) newCoqCallTypeArgs(method glang.Expr, typeArgs []glang.Expr,
	es []ast.Expr) glang.CallExpr {
	var args []glang.Expr
	for _, e := range es {
		args = append(args, ctx.expr(e))
	}
	call := glang.NewCallExpr(method, args...)
	call.TypeArgs = typeArgs
	return call
}

func (ctx Ctx) newCoqCall(method string, es []ast.Expr) glang.CallExpr {
	return ctx.newCoqCallTypeArgs(glang.GallinaIdent(method), nil, es)
}

func (ctx Ctx) newCoqCallWithExpr(method glang.Expr, es []ast.Expr) glang.CallExpr {
	return ctx.newCoqCallTypeArgs(method, nil, es)
}

// FIXME: this handles more than "method" calls. It e.g. also handles function
// calls and string <-> []byte conversions.
func (ctx Ctx) methodExpr(call *ast.CallExpr) glang.Expr {
	args := call.Args
	// discovered this API via
	// https://go.googlesource.com/example/+/HEAD/gotypes#named-types
	if ctx.info.Types[call.Fun].IsType() {
		ctx.todo(call, "Types.IsType() == true and ")
		// string -> []byte conversions are handled specially
		if f, ok := call.Fun.(*ast.ArrayType); ok {
			if f.Len == nil && isIdent(f.Elt, "byte") {
				arg := args[0]
				if isString(ctx.typeOf(arg)) {
					return ctx.newCoqCall("StringToBytes", args)
				}
			}
		}
		// []byte -> string are handled specially
		if f, ok := call.Fun.(*ast.Ident); ok && f.Name == "string" {
			arg := args[0]
			if isString(ctx.typeOf(arg).Underlying()) {
				return ctx.expr(args[0])
			}
			if !isByteSlice(ctx.typeOf(arg)) {
				ctx.unsupported(call,
					"conversion from type %v to string", ctx.typeOf(arg))
				return glang.CallExpr{}
			}
			return ctx.newCoqCall("StringFromBytes", args)
		}
		ctx.unsupported(call, "type conversion via that's not []byte <-> string")
		//  https://github.com/tchajed/goose/issues/14
		// return ctx.expr(args[0])
	}

	var retExpr glang.Expr

	f := call.Fun

	// IndexExpr and IndexListExpr represent calls like `f[T](x)`;
	// we get rid of the `[T]` since we can figure that out from the
	// ctx.info.Instances thing like we would need to for implicit type
	// arguments
	switch indexF := f.(type) {
	case *ast.IndexExpr:
		f = indexF.X
	case *ast.IndexListExpr:
		f = indexF.X
	}

	switch f := f.(type) {
	case *ast.Ident:
		typeArgs := ctx.typeList(call, ctx.info.Instances[f].TypeArgs)

		// XXX: this could be a struct field of type `func()`; right now we
		// don't support generic structs, so code with a generic function field
		// will be rejected. But, in the future, that might change.
		retExpr = ctx.newCoqCallTypeArgs(ctx.identExpr(f), typeArgs, args)
	case *ast.SelectorExpr:
		retExpr = ctx.selectorMethod(f, call)
	case *ast.IndexExpr:
		// generic type instantiation f[T]
		ctx.nope(call, "double explicit generic type instantiation")
	case *ast.IndexListExpr:
		// generic type instantiation f[T, V]
		ctx.nope(call, "double explicit generic type instantiation with multiple arguments")
	default:
		ctx.unsupported(call, "call to unexpected function (of type %T)", call.Fun)
	}

	return retExpr
}

func (ctx Ctx) makeSliceExpr(elt glang.Type, args []ast.Expr) glang.CallExpr {
	if len(args) == 2 {
		return glang.NewCallExpr(glang.GallinaIdent("NewSlice"), elt, ctx.expr(args[1]))
	} else if len(args) == 3 {
		return glang.NewCallExpr(glang.GallinaIdent("NewSliceWithCap"), elt, ctx.expr(args[1]), ctx.expr(args[2]))
	} else {
		ctx.unsupported(args[0], "Too many or too few arguments in slice construction")
		return glang.CallExpr{}
	}
}

// makeExpr parses a call to make() into the appropriate data-structure Call
func (ctx Ctx) makeExpr(args []ast.Expr) glang.CallExpr {
	switch typeArg := args[0].(type) {
	case *ast.MapType:
		mapTy := ctx.mapType(typeArg)
		return glang.NewCallExpr(glang.GallinaIdent("NewMap"), mapTy.Key, mapTy.Value, glang.UnitLiteral{})
	case *ast.ArrayType:
		if typeArg.Len != nil {
			ctx.nope(typeArg, "can't make() arrays (only slices)")
		}
		elt := ctx.coqType(typeArg.Elt)
		return ctx.makeSliceExpr(elt, args)
	}
	switch ty := ctx.typeOf(args[0]).Underlying().(type) {
	case *types.Slice:
		elt := ctx.coqTypeOfType(args[0], ty.Elem())
		return ctx.makeSliceExpr(elt, args)
	case *types.Map:
		return glang.NewCallExpr(glang.GallinaIdent("NewMap"),
			ctx.coqTypeOfType(args[0], ty.Key()),
			ctx.coqTypeOfType(args[0], ty.Elem()),
			glang.UnitLiteral{})
	default:
		ctx.unsupported(args[0],
			"make of should be slice or map, got %v", ty)
	}
	return glang.CallExpr{}
}

// newExpr parses a call to new() into an appropriate allocation
func (ctx Ctx) newExpr(s ast.Node, ty ast.Expr) glang.CallExpr {
	if t, ok := ctx.typeOf(ty).(*types.Array); ok {
		return glang.NewCallExpr(glang.GallinaIdent("zero_array"),
			ctx.coqTypeOfType(ty, t.Elem()),
			glang.IntLiteral{uint64(t.Len())})
	}
	e := glang.NewCallExpr(glang.GallinaIdent("zero_val"), ctx.coqType(ty))
	// check for new(T) where T is a struct, but not a pointer to a struct
	// (new(*T) should be translated to ref (zero_val ptrT) as usual,
	// a pointer to a nil pointer)
	if info, ok := ctx.getStructInfo(ctx.typeOf(ty)); ok && !info.throughPointer {
		return glang.NewCallExpr(glang.GallinaIdent("struct.alloc"), glang.StructDesc(info.name), e)
	}
	return glang.NewCallExpr(glang.GallinaIdent("ref"), e)
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
	return glang.NewCallExpr(glang.GallinaIdent("SliceCopy"),
		ctx.coqTypeOfType(n, e),
		ctx.expr(dst), ctx.expr(src))
}

func (ctx Ctx) callExpr(s *ast.CallExpr) glang.Expr {
	if isIdent(s.Fun, "make") {
		return ctx.makeExpr(s.Args)
	}
	if isIdent(s.Fun, "new") {
		return ctx.newExpr(s, s.Args[0])
	}
	if isIdent(s.Fun, "len") {
		return ctx.lenExpr(s)
	}
	if isIdent(s.Fun, "cap") {
		return ctx.capExpr(s)
	}
	if isIdent(s.Fun, "append") {
		elemTy := sliceElem(ctx.typeOf(s.Args[0]))
		if s.Ellipsis == token.NoPos {
			return glang.NewCallExpr(glang.GallinaIdent("SliceAppend"),
				ctx.coqTypeOfType(s, elemTy),
				ctx.expr(s.Args[0]),
				ctx.expr(s.Args[1]))
		}
		// append(s1, s2...)
		return glang.NewCallExpr(glang.GallinaIdent("SliceAppendSlice"),
			ctx.coqTypeOfType(s, elemTy),
			ctx.expr(s.Args[0]),
			ctx.expr(s.Args[1]))
	}
	if isIdent(s.Fun, "copy") {
		return ctx.copyExpr(s, s.Args[0], s.Args[1])
	}
	if isIdent(s.Fun, "delete") {
		if _, ok := ctx.typeOf(s.Args[0]).(*types.Map); !ok {
			ctx.unsupported(s, "delete on non-map")
		}
		return glang.NewCallExpr(glang.GallinaIdent("MapDelete"), ctx.expr(s.Args[0]), ctx.expr(s.Args[1]))
	}
	if isIdent(s.Fun, "uint64") {
		return ctx.integerConversion(s, s.Args[0], 64)
	}
	if isIdent(s.Fun, "uint32") {
		return ctx.integerConversion(s, s.Args[0], 32)
	}
	if isIdent(s.Fun, "uint8") {
		return ctx.integerConversion(s, s.Args[0], 8)
	}
	if isIdent(s.Fun, "panic") {
		msg := "oops"
		if e, ok := s.Args[0].(*ast.BasicLit); ok {
			if e.Kind == token.STRING {
				v := ctx.info.Types[e].Value
				msg = constant.StringVal(v)
			}
		}
		return glang.NewCallExpr(glang.GallinaIdent("Panic"), glang.GallinaString(msg))
	}
	// FIXME: obviate this code
	/*
		// Special case for *sync.NewCond
		if _, ok := s.Fun.(*ast.SelectorExpr); ok {
		} else {
			if signature, ok := ctx.typeOf(s.Fun).(*types.Signature); ok {
				for j := 0; j < signature.Params().Len(); j++ {
					if _, ok := signature.Params().At(j).Type().Underlying().(*types.Interface); ok {
						interfaceName := signature.Params().At(j).Type().String()
						structName := ctx.typeOf(s.Args[0]).String()
						interfaceName = unqualifyName(interfaceName)
						structName = unqualifyName(structName)
						if interfaceName != structName && interfaceName != "" && structName != "" {
							conversion := glang.StructToInterfaceDecl{
								Fun:       ctx.expr(s.Fun).Coq(true),
								Struct:    structName,
								Interface: interfaceName,
								Arg:       ctx.expr(s.Args[0]).Coq(true),
							}.Coq(true)
							for i, arg := range s.Args {
								if i > 0 {
									conversion += " " + ctx.expr(arg).Coq(true)
								}
							}
							return glang.CallExpr{MethodName: glang.GallinaIdent(conversion)}
						}
					}
				}
			}
		}
	*/
	return ctx.methodExpr(s)
}

func (ctx Ctx) qualifiedName(obj types.Object) string {
	name := obj.Name()
	if ctx.pkgPath == obj.Pkg().Path() {
		// no module name needed
		return name
	}
	return fmt.Sprintf("%s.%s", obj.Pkg().Name(), name)
}

func (ctx Ctx) selectExpr(e *ast.SelectorExpr) glang.Expr {
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

	// Check if the select expression is actually referring to a function object
	// If it is, we need to translate to 'StructName__FuncName varName' instead
	// of a struct access
	_, isFuncType := (ctx.typeOf(e)).(*types.Signature)
	if isFuncType {
		m := glang.StructMethod(structInfo.name, e.Sel.Name)
		ctx.dep.addDep(m)
		return glang.NewCallExpr(glang.GallinaIdent(m), ctx.expr(e.X))
	}
	if ok {
		return ctx.structSelector(structInfo, e)
	}
	ctx.unsupported(e, "unexpected select expression")
	return nil
}

func (ctx Ctx) structSelector(info structTypeInfo, e *ast.SelectorExpr) glang.StructFieldAccessExpr {
	ctx.dep.addDep(info.name)
	return glang.StructFieldAccessExpr{
		Struct:         info.name,
		Field:          e.Sel.Name,
		X:              ctx.expr(e.X),
		ThroughPointer: info.throughPointer,
	}
}

func (ctx Ctx) compositeLiteral(e *ast.CompositeLit) glang.Expr {
	if _, ok := ctx.typeOf(e).Underlying().(*types.Slice); ok {
		if len(e.Elts) == 0 {
			return glang.NewCallExpr(glang.GallinaIdent("nil"))
		}
		if len(e.Elts) == 1 {
			return ctx.newCoqCall("SliceSingleton", []ast.Expr{e.Elts[0]})
		}
		ctx.unsupported(e, "slice literal with multiple elements")
		return nil
	}
	info, ok := ctx.getStructInfo(ctx.typeOf(e))
	if ok {
		return ctx.structLiteral(info, e)
	}
	ctx.unsupported(e, "composite literal of type %v", ctx.typeOf(e))
	return nil
}

func (ctx Ctx) structLiteral(info structTypeInfo,
	e *ast.CompositeLit) glang.StructLiteral {
	ctx.dep.addDep(info.name)
	lit := glang.NewStructLiteral(info.name)
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
			ctx.unsupported(e,
				"un-keyed struct literal field %v", ctx.printGo(el))
		}
	}
	return lit
}

// basicLiteral parses a basic literal
//
// (unsigned) ints, strings, and booleans are supported
func (ctx Ctx) basicLiteral(e *ast.BasicLit) glang.Expr {
	if e.Kind == token.STRING {
		v := ctx.info.Types[e].Value
		s := constant.StringVal(v)
		if strings.ContainsRune(s, '"') {
			ctx.unsupported(e, "string literals with quotes")
		}
		return glang.StringLiteral{s}
	}
	if e.Kind == token.INT {
		info, ok := getIntegerType(ctx.typeOf(e))
		v := ctx.info.Types[e].Value
		n, ok := constant.Uint64Val(v)
		if !ok {
			ctx.unsupported(e,
				"int literals must be positive numbers")
			return nil
		}
		if info.isUint64() {
			return glang.IntLiteral{n}
		} else if info.isUint32() {
			return glang.Int32Literal{uint32(n)}
		} else if info.isUint8() {
			return glang.ByteLiteral{uint8(n)}
		}
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
	x := ctx.expr(e.X)
	if e.Low != nil && e.High == nil {
		return glang.NewCallExpr(glang.GallinaIdent("SliceSkip"),
			ctx.coqTypeOfType(e, sliceElem(ctx.typeOf(e.X))),
			x, ctx.expr(e.Low))
	}
	if e.Low == nil && e.High != nil {
		return glang.NewCallExpr(glang.GallinaIdent("SliceTake"),
			x, ctx.expr(e.High))
	}
	if e.Low != nil && e.High != nil {
		return glang.NewCallExpr(glang.GallinaIdent("SliceSubslice"),
			ctx.coqTypeOfType(e, sliceElem(ctx.typeOf(e.X))),
			x, ctx.expr(e.Low), ctx.expr(e.High))
	}
	if e.Low == nil && e.High == nil {
		ctx.unsupported(e, "complete slice doesn't do anything")
	}
	return nil
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
		return glang.NotExpr{ctx.expr(e.X)}
	}
	if e.Op == token.XOR {
		return glang.NotExpr{ctx.expr(e.X)}
	}
	if e.Op == token.AND {
		if x, ok := e.X.(*ast.IndexExpr); ok {
			// e is &a[b] where x is a.b
			if xTy, ok := ctx.typeOf(x.X).(*types.Slice); ok {
				return glang.NewCallExpr(glang.GallinaIdent("SliceRef"),
					ctx.coqTypeOfType(e, xTy.Elem()),
					ctx.expr(x.X), ctx.expr(x.Index))
			}
		}
		if info, ok := ctx.getStructInfo(ctx.typeOf(e.X)); ok {
			structLit, ok := e.X.(*ast.CompositeLit)
			if ok {
				// e is &s{...} (a struct literal)
				sl := ctx.structLiteral(info, structLit)
				sl.Allocation = true
				return sl
			}
		}
		// e is something else
		return ctx.refExpr(e.X)
	}
	ctx.unsupported(e, "unary expression %s", e.Op)
	return nil
}

// XXX: should distinguish between vars on LHS and RHS of assign statements. Not
// sure if this is being used in both places.
func (ctx Ctx) variable(s *ast.Ident) glang.Expr {
	if _, ok := ctx.info.Uses[s].(*types.Const); ok {
		ctx.dep.addDep(s.Name)
		return glang.GallinaIdent(s.Name)
	}
	return glang.DerefExpr{X: glang.IdentExpr(s.Name), Ty: ctx.coqTypeOfType(s, ctx.typeOf(s))}
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

func (ctx Ctx) indexExpr(e *ast.IndexExpr, isSpecial bool) glang.CallExpr {
	xTy := ctx.typeOf(e.X).Underlying()
	switch xTy := xTy.(type) {
	case *types.Map:
		e := glang.NewCallExpr(glang.GallinaIdent("MapGet"), ctx.expr(e.X), ctx.expr(e.Index))
		// FIXME: this is non-local. Should decide whether to do "Fst" based on
		// assign statement or parent expression.
		if !isSpecial {
			e = glang.NewCallExpr(glang.GallinaIdent("Fst"), e)
		}
		return e
	case *types.Slice:
		return glang.NewCallExpr(glang.GallinaIdent("SliceGet"),
			ctx.coqTypeOfType(e, xTy.Elem()),
			ctx.expr(e.X), ctx.expr(e.Index))
	}
	ctx.unsupported(e, "index into unknown type %v", xTy)
	return glang.CallExpr{}
}

func (ctx Ctx) derefExpr(e ast.Expr) glang.Expr {
	info, ok := ctx.getStructInfo(ctx.typeOf(e))
	if ok && info.throughPointer {
		return glang.NewCallExpr(glang.GallinaIdent("struct.load"),
			glang.StructDesc(info.name),
			ctx.expr(e))
	}
	return glang.DerefExpr{
		X:  ctx.expr(e),
		Ty: ctx.coqTypeOfType(e, ptrElem(ctx.typeOf(e))),
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
	case *ast.MapType:
		return ctx.mapType(e)
	case *ast.Ident:
		return ctx.identExpr(e)
	case *ast.SelectorExpr:
		return ctx.selectExpr(e)
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
	var e glang.Expr = glang.Tt
	for len(ss) > 0 {
		stmt := ss[len(ss)-1]
		ss = ss[:len(ss)-1]
		e = ctx.stmt(stmt, e)
	}
	return e
}

func (ctx Ctx) ifStmt(s *ast.IfStmt, cont glang.Expr) glang.Expr {
	var elseExpr glang.Expr = glang.Tt
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
	return glang.NewAnonLet(ife, cont)
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
	return e
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
		ctx.unsupported(s.Key, "range with non-identifier as iteration variable")
	}
	val, ok := s.Value.(*ast.Ident)
	if !ok {
		ctx.unsupported(s.Value, "range with non-identifier as iteration variable")
	}

	return glang.ForRangeSliceExpr{
		Key:   ctx.identBinder(key),
		Val:   ctx.identBinder(val),
		Slice: ctx.expr(s.X),
		Ty:    ctx.coqTypeOfType(s.X, sliceElem(ctx.typeOf(s.X))),
		Body:  ctx.blockStmt(s.Body, ExprValLocal),
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
		Ty: ctx.coqTypeOfType(rhs, ctx.typeOf(rhs)),
	}
}

func (ctx Ctx) defineStmt(s *ast.AssignStmt, cont glang.Expr) glang.Expr {
	if len(s.Rhs) > 1 {
		ctx.futureWork(s, "multiple defines (split them up)")
	}
	e := cont
	rhs := s.Rhs[0]
	// TODO: go only requires one of the variables being defined to be fresh;
	//  the rest are assigned. We should probably support re-assignment
	//  generally. The problem is re-assigning variables in a loop that were
	//  defined outside the loop, which in Go propagates to subsequent
	//  iterations, so we can just conservatively disallow assignments within
	//  loop bodies.

	var idents []*ast.Ident
	for _, lhsExpr := range s.Lhs {
		if ident, ok := lhsExpr.(*ast.Ident); ok {
			idents = append(idents, ident)
		} else {
			ctx.nope(lhsExpr, "defining a non-identifier")
		}
	}
	var names []string
	for _, ident := range idents {
		names = append(names, ident.Name)
		if _, ok := ctx.info.Defs[ident]; !ok {
			ctx.futureWork(ident, "should update and not shadow variables that were already in context at a define statement")
		}
	}

	// FIXME: one step for computing, more steps for heap allocation
	return e
}

func (ctx Ctx) varSpec(s *ast.ValueSpec) glang.Binding {
	if len(s.Names) > 1 {
		ctx.unsupported(s, "multiple declarations in one block")
	}
	lhs := s.Names[0]
	var rhs glang.Expr
	if len(s.Values) == 0 {
		ty := ctx.typeOf(lhs)
		rhs = glang.NewCallExpr(glang.GallinaIdent("ref"),
			glang.NewCallExpr(glang.GallinaIdent("zero_val"), ctx.coqTypeOfType(s, ty)))
	} else {
		rhs = ctx.referenceTo(s.Values[0])
	}
	return glang.Binding{
		Names: []string{lhs.Name},
		Expr:  rhs,
	}
}

// varDeclStmt translates declarations within functions
func (ctx Ctx) varDeclStmt(s *ast.DeclStmt) glang.Binding {
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
	return ctx.varSpec(decl.Specs[0].(*ast.ValueSpec))
}

// refExpr translates an expression which is a pointer in Go to a GooseLang
// expr for the pointer itself (whereas ordinarily it would be implicitly loaded)
//
// TODO: integrate this into the reference-of, store, and load code
//
//	note that we will no longer special-case when the reference is to a
//	basic value and will use generic type-based support in Coq,
//	hence on the Coq side we'll always have to reduce type-based loads and
//	stores when they end up loading single-word values.
func (ctx Ctx) refExpr(s ast.Expr) glang.Expr {
	switch s := s.(type) {
	case *ast.Ident:
		// this is the intended translation even if s is pointer-wrapped
		return glang.IdentExpr(s.Name)
	case *ast.SelectorExpr:
		ty := ctx.typeOf(s.X)
		info, ok := ctx.getStructInfo(ty)
		if !ok {
			ctx.unsupported(s,
				"reference to selector from non-struct type %v", ty)
		}
		fieldName := s.Sel.Name

		var structExpr glang.Expr
		if info.throughPointer {
			structExpr = ctx.expr(s.X)
		} else {
			structExpr = ctx.refExpr(s.X)
		}
		return glang.NewCallExpr(glang.GallinaIdent("struct.fieldRef"), glang.StructDesc(info.name),
			glang.GallinaString(fieldName), structExpr)
	// TODO: should move support for slice indexing here as well
	default:
		ctx.futureWork(s, "reference to other types of expressions")
		return nil
	}
}

func (ctx Ctx) pointerAssign(dst *ast.Ident, x glang.Expr) glang.Binding {
	ty := ctx.typeOf(dst)
	return glang.NewAnonLet(glang.StoreStmt{
		Dst: glang.IdentExpr(dst.Name),
		X:   x,
		Ty:  ctx.coqTypeOfType(dst, ty),
	})
}

func (ctx Ctx) assignFromTo(s ast.Node, lhs ast.Expr, rhs glang.Expr) glang.Binding {
	// assignments can mean various things
	switch lhs := lhs.(type) {
	case *ast.Ident:
		if lhs.Name == "_" {
			return glang.NewAnonLet(rhs)
		}
		return ctx.pointerAssign(lhs, rhs)
	case *ast.IndexExpr:
		targetTy := ctx.typeOf(lhs.X)
		switch targetTy := targetTy.(type) {
		case *types.Slice:
			value := rhs
			return glang.NewAnonLet(glang.NewCallExpr(
				glang.GallinaIdent("SliceSet"),
				ctx.coqTypeOfType(lhs, targetTy.Elem()),
				ctx.expr(lhs.X),
				ctx.expr(lhs.Index),
				value))
		case *types.Map:
			value := rhs
			return glang.NewAnonLet(glang.NewCallExpr(
				glang.GallinaIdent("MapInsert"),
				ctx.expr(lhs.X),
				ctx.expr(lhs.Index),
				value))
		default:
			ctx.unsupported(s, "index update to unexpected target of type %v", targetTy)
		}
	case *ast.StarExpr:
		info, ok := ctx.getStructInfo(ctx.typeOf(lhs.X))
		if ok && info.throughPointer {
			return glang.NewAnonLet(glang.NewCallExpr(glang.GallinaIdent("struct.store"),
				glang.StructDesc(info.name),
				ctx.expr(lhs.X),
				rhs))
		}
		dstPtrTy, ok := ctx.typeOf(lhs.X).Underlying().(*types.Pointer)
		if !ok {
			ctx.unsupported(s,
				"could not identify element type of assignment through pointer")
		}
		return glang.NewAnonLet(glang.StoreStmt{
			Dst: ctx.expr(lhs.X),
			Ty:  ctx.coqTypeOfType(s, dstPtrTy.Elem()),
			X:   rhs,
		})
	case *ast.SelectorExpr:
		ty := ctx.typeOf(lhs.X)
		info, ok := ctx.getStructInfo(ty)
		var structExpr glang.Expr
		// TODO: this adjusts for pointer-wrapping in refExpr, but there should
		//  be a more systematic way to think about this (perhaps in terms of
		//  distinguishing between translating for lvalues and rvalue)
		if info.throughPointer {
			structExpr = ctx.expr(lhs.X)
		} else {
			structExpr = ctx.refExpr(lhs.X)
		}
		if ok {
			fieldName := lhs.Sel.Name
			return glang.NewAnonLet(glang.NewCallExpr(glang.GallinaIdent("struct.storeF"),
				glang.StructDesc(info.name),
				glang.GallinaString(fieldName),
				structExpr,
				rhs))
		}
		ctx.unsupported(s,
			"assigning to field of non-struct type %v", ty)
	default:
		ctx.unsupported(s, "assigning to complex expression")
	}
	return glang.Binding{}
}

func (ctx Ctx) multipleAssignStmt(s *ast.AssignStmt) glang.Binding {
	// Translates a, b, c = SomeCall(args)
	// into
	//
	// {
	//   ret1, ret2, ret3 := SomeCall(args)
	//   a = ret1
	//   b = ret2
	//   c = ret3
	// }
	//
	// Returns multiple bindings, since there are multiple statements

	if len(s.Rhs) > 1 {
		ctx.unsupported(s, "multiple assignments on right hand side")
	}
	rhs := ctx.expr(s.Rhs[0])

	if s.Tok != token.ASSIGN {
		// This should be invalid Go syntax anyway
		ctx.unsupported(s, "%v multiple assignment", s.Tok)
	}

	names := make([]string, len(s.Lhs))
	for i := 0; i < len(names); i += 1 {
		names[i] = fmt.Sprintf("%d_ret", i)
	}
	multipleRetBinding := glang.Binding{Names: names, Expr: rhs}

	coqStmts := make([]glang.Binding, len(s.Lhs)+1)
	coqStmts[0] = multipleRetBinding

	for i, name := range names {
		coqStmts[i+1] = ctx.assignFromTo(s, s.Lhs[i], glang.IdentExpr(name))
	}
	return glang.Binding{Names: make([]string, 0), Expr: glang.BlockExpr{Bindings: coqStmts}}
}

func (ctx Ctx) assignStmt(s *ast.AssignStmt, cont *glang.Expr) glang.Expr {
	if s.Tok == token.DEFINE {
		return ctx.defineStmt(s)
	}
	// FIXME: handle multiple assigs uniformly with 1 assign
	if len(s.Lhs) > 1 {
		return ctx.multipleAssignStmt(s)
	}
	lhs := s.Lhs[0]
	rhs := ctx.expr(s.Rhs[0])
	assignOps := map[token.Token]glang.BinOp{
		token.ADD_ASSIGN: glang.OpPlus,
		token.SUB_ASSIGN: glang.OpMinus,
	}
	if op, ok := assignOps[s.Tok]; ok {
		rhs = glang.BinaryExpr{
			X:  ctx.expr(lhs),
			Op: op,
			Y:  rhs,
		}
		return ctx.assignFromTo(s, lhs, rhs)
	} else if s.Tok != token.ASSIGN {
		ctx.unsupported(s, "%v assignment", s.Tok)
	}
	return ctx.assignFromTo(s, lhs, rhs)
}

func (ctx Ctx) incDecStmt(stmt *ast.IncDecStmt) glang.Binding {
	ident := getIdentOrNil(stmt.X)
	if ident == nil {
		ctx.todo(stmt, "cannot inc/dec non-var")
		return glang.Binding{}
	}
	op := glang.OpPlus
	if stmt.Tok == token.DEC {
		op = glang.OpMinus
	}
	return ctx.pointerAssign(ident, glang.BinaryExpr{
		X:  ctx.expr(stmt.X),
		Op: op,
		Y:  glang.IntLiteral{Value: 1},
	})
}

func (ctx Ctx) spawnExpr(thread ast.Expr) glang.SpawnExpr {
	f, ok := thread.(*ast.FuncLit)
	if !ok {
		ctx.futureWork(thread,
			"only function literal spawns are supported")
		return glang.SpawnExpr{}
	}
	return glang.SpawnExpr{Body: ctx.blockStmt(f.Body, ExprValLocal)}
}

func (ctx Ctx) branchStmt(s *ast.BranchStmt) glang.Expr {
	if s.Tok == token.CONTINUE {
		return glang.LoopContinue
	}
	if s.Tok == token.BREAK {
		return glang.LoopBreak
	}
	ctx.noExample(s, "unexpected control flow %v in loop", s.Tok)
	return nil
}

// getSpawn returns a non-nil spawned thread if the expression is a go call
func (ctx Ctx) goStmt(e *ast.GoStmt) glang.Expr {
	if len(e.Call.Args) > 0 {
		ctx.unsupported(e, "go statement with parameters")
	}
	return ctx.spawnExpr(e.Call.Fun)
}

// This function also returns whether the expression has been "finalized",
// which means the usage has been taken care of. If it is not finalized,
// the caller is responsible for adding a trailing "return unit"/"continue".
func (ctx Ctx) stmt(s ast.Stmt, cont glang.Expr) glang.Expr {
	switch s := s.(type) {
	case *ast.ReturnStmt:
		ctx.futureWork(s, "return in unsupported position")
	case *ast.BranchStmt:
		ctx.futureWork(s, "break/continue in unsupported position")
	case *ast.GoStmt:
		return glang.NewAnonLet(ctx.goStmt(s), cont)
	case *ast.ExprStmt:
		return glang.NewAnonLet(ctx.expr(s.X), cont)
	case *ast.AssignStmt:
		return ctx.assignStmt(s)
	case *ast.DeclStmt:
		return ctx.varDeclStmt(s)
	case *ast.IncDecStmt:
		return ctx.incDecStmt(s)
	case *ast.ForStmt:
		// note that this might be a nested loop,
		// in which case the loop var gets replaced by the inner loop.
		return glang.NewAnonLet(ctx.forStmt(s), cont)
	case *ast.RangeStmt:
		return glang.NewAnonLet(ctx.rangeStmt(s), cont)
	case *ast.SwitchStmt:
		ctx.todo(s, "check for switch statement")
	case *ast.TypeSwitchStmt:
		ctx.todo(s, "check for type switch statement")
	default:
		ctx.unsupported(s, "statement")
	}
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
		ts = append(ts, ctx.coqType(r.Type))
	}
	return glang.NewTupleType(ts)
}

func (ctx Ctx) funcDecl(d *ast.FuncDecl) glang.FuncDecl {

	fd := glang.FuncDecl{Name: d.Name.Name, AddTypes: ctx.Config.TypeCheck,
		TypeParams: ctx.typeParamList(d.Type.TypeParams),
	}
	addSourceDoc(d.Doc, &fd.Comment)
	ctx.addSourceFile(d, &fd.Comment)
	if d.Recv != nil {
		if len(d.Recv.List) != 1 {
			ctx.nope(d, "function with multiple receivers")
		}
		receiver := d.Recv.List[0]
		recvType := ctx.typeOf(receiver.Type)
		// TODO: factor out this struct-or-struct pointer pattern
		if pT, ok := recvType.(*types.Pointer); ok {
			recvType = pT.Elem()
		}

		structInfo, ok := ctx.getStructInfo(recvType)
		if !ok {
			ctx.unsupported(d.Recv, "receiver does not appear to be a struct")
		}
		fd.Name = glang.StructMethod(structInfo.name, d.Name.Name)
		fd.Args = append(fd.Args, ctx.field(receiver))
	}

	fd.Args = append(fd.Args, ctx.paramList(d.Type.Params)...)

	fd.ReturnType = ctx.returnType(d.Type.Results)
	fd.Body = ctx.blockStmt(d.Body, ExprValReturned)
	ctx.dep.addName(fd.Name)
	return fd
}

func (ctx Ctx) constSpec(spec *ast.ValueSpec) glang.ConstDecl {
	ident := spec.Names[0]
	cd := glang.ConstDecl{
		Name:     ident.Name,
		AddTypes: ctx.Config.TypeCheck,
	}
	addSourceDoc(spec.Comment, &cd.Comment)
	val := spec.Values[0]
	cd.Val = ctx.expr(val)
	if spec.Type == nil {
		cd.Type = ctx.coqTypeOfType(spec, ctx.typeOf(val))
	} else {
		cd.Type = ctx.coqType(spec.Type)
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
	// NOTE: this treats globals as constants, which is unsound but used for a
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

// TODO: put this in another file
var builtinImports = map[string]bool{
	"log": true,
	"fmt": true,
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
		if !builtinImports[importPath] {
			// TODO: this uses the syntax of the Go import to determine the Coq
			// import, but Go packages can contain a different name than their
			// path. We can get this information by using the *types.Package
			// returned by Check (or the pkg.Types field from *packages.Package).
			decls = append(decls, glang.ImportDecl{Path: importPath})
		}
	}
	return decls
}

func (ctx Ctx) exprInterface(cvs []glang.Decl, expr ast.Expr, d *ast.FuncDecl) []glang.Decl {
	switch f := expr.(type) {
	case *ast.UnaryExpr:
		if left, ok := f.X.(*ast.BinaryExpr); ok {
			if call, ok := left.X.(*ast.CallExpr); ok {
				cvs = ctx.callExprInterface(cvs, call, d)
			}
		}
	case *ast.BinaryExpr:
		if left, ok := f.X.(*ast.BinaryExpr); ok {
			if call, ok := left.X.(*ast.CallExpr); ok {
				cvs = ctx.callExprInterface(cvs, call, d)
			}
		}
		if right, ok := f.Y.(*ast.BinaryExpr); ok {
			if call, ok := right.X.(*ast.CallExpr); ok {
				cvs = ctx.callExprInterface(cvs, call, d)
			}
		}
	case *ast.CallExpr:
		cvs = ctx.callExprInterface(cvs, f, d)
	}
	return cvs
}

func (ctx Ctx) stmtInterface(cvs []glang.Decl, stmt ast.Stmt, d *ast.FuncDecl) []glang.Decl {
	switch f := stmt.(type) {
	case *ast.ReturnStmt:
		for _, result := range f.Results {
			cvs = ctx.exprInterface(cvs, result, d)
		}
		if len(f.Results) > 0 {
			if results, ok := f.Results[0].(*ast.BinaryExpr); ok {
				if call, ok := results.X.(*ast.CallExpr); ok {
					cvs = ctx.callExprInterface(cvs, call, d)
				}
			}
		}
	case *ast.IfStmt:
		if call, ok := f.Cond.(*ast.CallExpr); ok {
			cvs = ctx.callExprInterface(cvs, call, d)
		}
	case *ast.ExprStmt:
		if call, ok := f.X.(*ast.CallExpr); ok {
			cvs = ctx.callExprInterface(cvs, call, d)
		}
	case *ast.AssignStmt:
		if call, ok := f.Rhs[0].(*ast.CallExpr); ok {
			cvs = ctx.callExprInterface(cvs, call, d)
		}
	}
	return cvs
}

// TODO: this is a hack, should have a better scheme for putting
// interface/implementation types into the conversion name
func unqualifyName(name string) string {
	components := strings.Split(name, ".")
	// return strings.Join(components[1:], "")
	return components[len(components)-1]
}

func (ctx Ctx) callExprInterface(cvs []glang.Decl, r *ast.CallExpr, d *ast.FuncDecl) []glang.Decl {
	interfaceName := ""
	methods := []string{}
	if signature, ok := ctx.typeOf(r.Fun).(*types.Signature); ok {
		params := signature.Params()
		for j := 0; j < params.Len(); j++ {
			interfaceName = params.At(j).Type().String()
			interfaceName = unqualifyName(interfaceName)
			if v, ok := params.At(j).Type().Underlying().(*types.Interface); ok {
				for m := 0; m < v.NumMethods(); m++ {
					methods = append(methods, v.Method(m).Name())
				}
			}
		}
		for _, arg := range r.Args {
			structName := ctx.typeOf(arg).String()
			structName = unqualifyName(structName)
			if _, ok := ctx.typeOf(arg).Underlying().(*types.Struct); ok {
				cv := glang.StructToInterface{Struct: structName, Interface: interfaceName, Methods: methods}
				if len(cv.Coq(true)) > 1 && len(cv.MethodList()) > 0 {
					cvs = append(cvs, cv)
				}
			}
		}
	}
	return cvs
}

func (ctx Ctx) maybeDecls(d ast.Decl) []glang.Decl {
	switch d := d.(type) {
	case *ast.FuncDecl:
		cvs := []glang.Decl{}
		for _, stmt := range d.Body.List {
			cvs = ctx.stmtInterface(cvs, stmt, d)
		}
		fd := ctx.funcDecl(d)
		results := []glang.Decl{}
		if len(cvs) > 0 {
			results = append(cvs, fd)
		} else {
			results = []glang.Decl{fd}
		}
		return results
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
			ty := ctx.typeDecl(spec)
			return []glang.Decl{ty}
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
