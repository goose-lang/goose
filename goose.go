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

	"github.com/tchajed/goose/internal/coq"
	"golang.org/x/tools/go/packages"
)

// Ctx is a context for resolving Go code's types and source code
type Ctx struct {
	idents  identCtx
	info    *types.Info
	Fset    *token.FileSet
	pkgPath string
	errorReporter
	Config
}

// Implement flag.Value for a "set" of strings; used by Config
type StringSet map[string]bool

// Says how the result of the currently generated expression will be used
type ExprValUsage int

const (
	// The result of this expression will only be used locally, or entirelz discarded
	ExprValLocal ExprValUsage = iota
	// The result of this expression will be returned from the current function
	// (i.e., the "early return" control effect is available here)
	ExprValReturned
	// The result of this expression will control the current loop
	// (i.e., the "break/continue" control effect is available here)
	ExprValLoop
)

func (s *StringSet) String() string {
	r := ""
	for k := range *s {
		r += k
	}
	return r
}

func (s *StringSet) Set(value string) error {
	(*s)[value] = true
	return nil
}

// Config holds global configuration for Coq conversion
type Config struct {
	AddSourceFileComments bool
	TypeCheck             bool
	Ffi                   string
}

// Returns the default config
func MakeDefaultConfig() Config {
	var config Config
	config.Ffi = "none"
	return config
}

func getFfi(pkg *packages.Package) string {
	seenFfis := make(map[string]struct{})
	packages.Visit([]*packages.Package{pkg},
		func(pkg *packages.Package) bool {
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
		idents:        newIdentCtx(),
		info:          pkg.TypesInfo,
		Fset:          pkg.Fset,
		pkgPath:       pkg.PkgPath,
		errorReporter: newErrorReporter(pkg.Fset),
		Config:        config,
	}
}

// NewCtx loads a context for files passed directly,
// rather than loaded from a packages.
// Errors from this function are errors during type-checking.
func NewCtx(pkgPath string, conf Config) Ctx {
	info := &types.Info{
		Defs:   make(map[*ast.Ident]types.Object),
		Uses:   make(map[*ast.Ident]types.Object),
		Types:  make(map[ast.Expr]types.TypeAndValue),
		Scopes: make(map[ast.Node]*types.Scope),
	}
	fset := token.NewFileSet()
	return Ctx{
		idents:        newIdentCtx(),
		info:          info,
		Fset:          fset,
		pkgPath:       pkgPath,
		errorReporter: newErrorReporter(fset),
		Config:        conf,
	}
}

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

func (ctx Ctx) field(f *ast.Field) coq.FieldDecl {
	if len(f.Names) > 1 {
		ctx.futureWork(f, "multiple fields for same type (split them up)")
		return coq.FieldDecl{}
	}
	if len(f.Names) == 0 {
		ctx.unsupported(f, "unnamed field/parameter")
		return coq.FieldDecl{}
	}
	return coq.FieldDecl{
		Name: f.Names[0].Name,
		Type: ctx.coqType(f.Type),
	}
}

func (ctx Ctx) paramList(fs *ast.FieldList) []coq.FieldDecl {
	var decls []coq.FieldDecl
	for _, f := range fs.List {
		ty := ctx.coqType(f.Type)
		for _, name := range f.Names {
			decls = append(decls, coq.FieldDecl{
				Name: name.Name,
				Type: ty,
			})
			ctx.addDef(name, identInfo{
				IsPtrWrapped: false,
				IsMacro:      false,
			})
		}
		if len(f.Names) == 0 { // Unnamed parameter
			decls = append(decls, coq.FieldDecl{
				Name: "",
				Type: ty,
			})
		}
	}
	return decls
}

func (ctx Ctx) structFields(structName string,
	fs *ast.FieldList) []coq.FieldDecl {
	var decls []coq.FieldDecl
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
		info, ok := ctx.getStructInfo(ctx.typeOf(f.Type))
		if ok && info.name == structName && info.throughPointer {
			// TODO: Remove reference to refT, use indirection in coq.go
			ty = coq.NewCallExpr("refT", coq.TypeIdent("anyT"))
		}
		decls = append(decls, coq.FieldDecl{
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

func (ctx Ctx) typeDecl(doc *ast.CommentGroup, spec *ast.TypeSpec) coq.Decl {
	switch goTy := spec.Type.(type) {
	case *ast.StructType:
		ctx.addDef(spec.Name, identInfo{
			IsPtrWrapped: false,
			IsMacro:      false,
		})
		ty := coq.StructDecl{
			Name: spec.Name.Name,
		}
		addSourceDoc(doc, &ty.Comment)
		ctx.addSourceFile(spec, &ty.Comment)
		ty.Fields = ctx.structFields(spec.Name.Name, goTy.Fields)
		return ty
	case *ast.InterfaceType:
		ctx.addDef(spec.Name, identInfo{
			IsPtrWrapped: false,
			IsMacro:      false,
		})
		ty := coq.InterfaceDecl{
			Name: spec.Name.Name,
		}
		addSourceDoc(doc, &ty.Comment)
		ctx.addSourceFile(spec, &ty.Comment)
		ty.Methods = ctx.structFields(spec.Name.Name, goTy.Methods)
		return ty
	default:
		ctx.addDef(spec.Name, identInfo{
			IsPtrWrapped: false,
			IsMacro:      true,
		})
		return coq.TypeDecl{
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

func (ctx Ctx) lenExpr(e *ast.CallExpr) coq.CallExpr {
	x := e.Args[0]
	xTy := ctx.typeOf(x)
	switch ty := xTy.Underlying().(type) {
	case *types.Slice:
		return coq.NewCallExpr("slice.len", ctx.expr(x))
	case *types.Map:
		return coq.NewCallExpr("MapLen", ctx.expr(x))
	case *types.Basic:
		if ty.Kind() == types.String {
			return coq.NewCallExpr("strLen", ctx.expr(x))
		}
	}
	ctx.unsupported(e, "length of object of type %v", xTy)
	return coq.CallExpr{}
}

func (ctx Ctx) lockMethod(f *ast.SelectorExpr) coq.CallExpr {
	l := ctx.expr(f.X)
	switch f.Sel.Name {
	case "Lock":
		return coq.NewCallExpr("lock.acquire", l)
	case "Unlock":
		return coq.NewCallExpr("lock.release", l)
	default:
		ctx.nope(f, "method %s of sync.Mutex", ctx.printGo(f))
		return coq.CallExpr{}
	}
}

func (ctx Ctx) condVarMethod(f *ast.SelectorExpr) coq.CallExpr {
	l := ctx.expr(f.X)
	switch f.Sel.Name {
	case "Signal":
		return coq.NewCallExpr("lock.condSignal", l)
	case "Broadcast":
		return coq.NewCallExpr("lock.condBroadcast", l)
	case "Wait":
		return coq.NewCallExpr("lock.condWait", l)
	default:
		ctx.unsupported(f, "method %s of sync.Cond", f.Sel.Name)
		return coq.CallExpr{}
	}

}
func (ctx Ctx) packageMethod(f *ast.SelectorExpr,
	call *ast.CallExpr) coq.Expr {
	args := call.Args
	if isIdent(f.X, "filesys") {
		return ctx.newCoqCall("FS."+toInitialLower(f.Sel.Name), args)
	}
	if isIdent(f.X, "disk") {
		return ctx.newCoqCall("disk."+f.Sel.Name, args)
	}
	if isIdent(f.X, "machine") {
		switch f.Sel.Name {
		case "UInt64Get", "UInt64Put", "UInt32Get", "UInt32Put":
			return ctx.newCoqCall(f.Sel.Name, args)
		case "RandomUint64":
			return ctx.newCoqCall("Data.randomUint64", nil)
		case "UInt64ToString":
			return ctx.newCoqCall("uint64_to_string", args)
		case "Linearize":
			return coq.GallinaIdent("Linearize")
		case "Assume":
			return ctx.newCoqCall("control.impl.Assume", args)
		case "Assert":
			return ctx.newCoqCall("control.impl.Assert", args)
		case "WaitTimeout":
			return ctx.newCoqCall("lock.condWaitTimeout", args)
		default:
			ctx.futureWork(f, "unhandled call to machine.%s", f.Sel.Name)
			return coq.CallExpr{}
		}
	}
	if isIdent(f.X, "log") {
		switch f.Sel.Name {
		case "Print", "Printf", "Println":
			return coq.LoggingStmt{GoCall: ctx.printGo(call)}
		}
	}
	// FIXME: this hack ensures util.DPrintf runs correctly in goose-nfsd.
	//
	//  We always pass #() instead of a slice with the variadic arguments. The
	//  function is important to handle but has no observable behavior in
	//  GooseLang, so it's ok to skip the arguments.
	//
	// See https://github.com/mit-pdos/goose-nfsd/blob/master/util/util.go
	if isIdent(f.X, "util") && f.Sel.Name == "DPrintf" {
		return coq.NewCallExpr("util.DPrintf",
			ctx.expr(args[0]),
			ctx.expr(args[1]),
			coq.UnitLiteral{})
	}
	if isIdent(f.X, "fmt") {
		switch f.Sel.Name {
		case "Println", "Printf":
			return coq.LoggingStmt{GoCall: ctx.printGo(call)}
		}
	}
	if isIdent(f.X, "sync") {
		switch f.Sel.Name {
		case "NewCond":
			return ctx.newCoqCall("lock.newCond", args)
		}
	}
	pkg := f.X.(*ast.Ident)
	return ctx.newCoqCall(
		coq.PackageIdent{Package: pkg.Name, Ident: f.Sel.Name}.Coq(),
		args)
}

func (ctx Ctx) selectorMethod(f *ast.SelectorExpr,
	call *ast.CallExpr) coq.Expr {
	args := call.Args
	selectorType, ok := ctx.getType(f.X)
	if !ok {
		return ctx.packageMethod(f, call)
	}
	if isLockRef(selectorType) {
		return ctx.lockMethod(f)
	}
	if isCondVar(selectorType) {
		return ctx.condVarMethod(f)
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
				coq.InterfaceMethod(interfaceInfo.name, f.Sel.Name),
				callArgs)
		}
	default:
		structInfo, ok := ctx.getStructInfo(selectorType)
		if ok {
			callArgs := append([]ast.Expr{f.X}, args...)
			return ctx.newCoqCall(
				coq.StructMethod(structInfo.name, f.Sel.Name),
				callArgs)
		}
	}
	ctx.unsupported(f, "unexpected select on type "+selectorType.String())
	return nil
}

func (ctx Ctx) newCoqCall(method string, es []ast.Expr) coq.CallExpr {
	var args []coq.Expr
	for _, e := range es {
		args = append(args, ctx.expr(e))
	}
	return coq.NewCallExpr(method, args...)
}

func (ctx Ctx) methodExpr(call *ast.CallExpr) coq.Expr {
	args := call.Args
	// discovered this API via
	// https://go.googlesource.com/example/+/HEAD/gotypes#named-types
	if ctx.info.Types[call.Fun].IsType() {
		// string -> []byte conversions are handled specially
		if f, ok := call.Fun.(*ast.ArrayType); ok {
			if f.Len == nil && isIdent(f.Elt, "byte") {
				arg := args[0]
				if isString(ctx.typeOf(arg)) {
					return ctx.newCoqCall("Data.stringToBytes", args)
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
				return coq.CallExpr{}
			}
			return ctx.newCoqCall("Data.bytesToString", args)
		}
		// a different type conversion, which is a noop in GooseLang (which is
		// untyped)
		// TODO: handle integer conversions here, checking if call.Fun is an integer
		//  type; see https://github.com/tchajed/goose/issues/14
		return ctx.expr(args[0])
	}
	switch f := call.Fun.(type) {
	case *ast.Ident:
		name := f.Name
		// If the identifier name is actually a variable, need to output
		// "\"" + name "\"" instead of name
		if _, ok := ctx.info.ObjectOf(f).(*types.Var); ok {
			name = fmt.Sprintf("\"%s\"", name)
		}
		return ctx.newCoqCall(name, args)
	case *ast.SelectorExpr:
		return ctx.selectorMethod(f, call)
	}
	ctx.unsupported(call, "call to unexpected function")
	return coq.CallExpr{}
}

// makeExpr parses a call to make() into the appropriate data-structure Call
func (ctx Ctx) makeExpr(args []ast.Expr) coq.CallExpr {
	switch typeArg := args[0].(type) {
	case *ast.MapType:
		mapTy := ctx.mapType(typeArg)
		return coq.NewCallExpr("NewMap", mapTy.Value)
	case *ast.ArrayType:
		if typeArg.Len != nil {
			ctx.nope(typeArg, "can't make() arrays (only slices)")
		}
		elt := ctx.coqType(typeArg.Elt)
		return coq.NewCallExpr("NewSlice", elt, ctx.expr(args[1]))
	}
	switch ty := ctx.typeOf(args[0]).Underlying().(type) {
	case *types.Slice:
		return coq.NewCallExpr("NewSlice",
			ctx.coqTypeOfType(args[0], ty.Elem()),
			ctx.expr(args[1]))
	case *types.Map:
		return coq.NewCallExpr("NewMap",
			ctx.coqTypeOfType(args[0], ty.Elem()))
	default:
		ctx.unsupported(args[0],
			"make of should be slice or map, got %v", ty)
	}
	return coq.CallExpr{}
}

// newExpr parses a call to new() into an appropriate allocation
func (ctx Ctx) newExpr(s ast.Node, ty ast.Expr) coq.CallExpr {
	if sel, ok := ty.(*ast.SelectorExpr); ok {
		if isIdent(sel.X, "sync") && isIdent(sel.Sel, "Mutex") {
			return coq.NewCallExpr("lock.new")
		}
	}
	if t, ok := ctx.typeOf(ty).(*types.Array); ok {
		return coq.NewCallExpr("zero_array",
			ctx.coqTypeOfType(ty, t.Elem()),
			coq.IntLiteral{uint64(t.Len())})
	}
	e := coq.NewCallExpr("zero_val", ctx.coqType(ty))
	// check for new(T) where T is a struct, but not a pointer to a struct
	// (new(*T) should be translated to ref (zero_val (ptrT ...)) as usual,
	// a pointer to a nil pointer)
	if info, ok := ctx.getStructInfo(ctx.typeOf(ty)); ok && !info.throughPointer {
		return coq.NewCallExpr("struct.alloc", coq.StructDesc(info.name), e)
	}
	return coq.NewCallExpr("ref", e)
}

// integerConversion generates an expression for converting x to an integer
// of a specific width
//
// s is only used for error reporting
func (ctx Ctx) integerConversion(s ast.Node, x ast.Expr, width int) coq.Expr {
	if info, ok := getIntegerType(ctx.typeOf(x)); ok {
		if info.isUntyped {
			ctx.todo(s, "conversion from untyped int to uint64")
		}
		if info.width == width {
			return ctx.expr(x)
		}
		return coq.NewCallExpr(fmt.Sprintf("to_u%d", width),
			ctx.expr(x))
	}
	ctx.unsupported(s, "casts from unsupported type %v to uint%d",
		ctx.typeOf(x), width)
	return nil
}

func (ctx Ctx) copyExpr(n ast.Node, dst ast.Expr, src ast.Expr) coq.Expr {
	e := sliceElem(ctx.typeOf(dst))
	return coq.NewCallExpr("SliceCopy",
		ctx.coqTypeOfType(n, e),
		ctx.expr(dst), ctx.expr(src))
}

func (ctx Ctx) callExpr(s *ast.CallExpr) coq.Expr {
	if isIdent(s.Fun, "make") {
		return ctx.makeExpr(s.Args)
	}
	if isIdent(s.Fun, "new") {
		return ctx.newExpr(s, s.Args[0])
	}
	if isIdent(s.Fun, "len") {
		return ctx.lenExpr(s)
	}
	if isIdent(s.Fun, "append") {
		elemTy := sliceElem(ctx.typeOf(s.Args[0]))
		if s.Ellipsis == token.NoPos {
			return coq.NewCallExpr("SliceAppend",
				ctx.coqTypeOfType(s, elemTy),
				ctx.expr(s.Args[0]),
				ctx.expr(s.Args[1]))
		}
		// append(s1, s2...)
		return coq.NewCallExpr("SliceAppendSlice",
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
		return coq.NewCallExpr("MapDelete", ctx.expr(s.Args[0]), ctx.expr(s.Args[1]))
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
		return coq.NewCallExpr("Panic", coq.GallinaString(msg))
	}
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
						conversion := coq.StructToInterfaceDecl{
							Fun:       ctx.expr(s.Fun).Coq(),
							Struct:    structName,
							Interface: interfaceName,
							Arg:       ctx.expr(s.Args[0]).Coq(),
						}.Coq()
						for i, arg := range s.Args {
							if i > 0 {
								conversion += " " + ctx.expr(arg).Coq()
							}
						}
						return coq.CallExpr{MethodName: conversion}
					}
				}
			}
		}
	}
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

func (ctx Ctx) selectExpr(e *ast.SelectorExpr) coq.Expr {
	selectorType, ok := ctx.getType(e.X)
	if !ok {
		if isIdent(e.X, "filesys") {
			return coq.GallinaIdent("FS." + e.Sel.Name)
		}
		if isIdent(e.X, "disk") {
			return coq.GallinaIdent("disk." + e.Sel.Name)
		}
		if pkg, ok := getIdent(e.X); ok {
			return coq.PackageIdent{
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
		return coq.NewCallExpr(
			coq.StructMethod(structInfo.name, e.Sel.Name), ctx.expr(e.X))
	}
	if ok {
		return ctx.structSelector(structInfo, e)
	}
	ctx.unsupported(e, "unexpected select expression")
	return nil
}

func (ctx Ctx) structSelector(info structTypeInfo, e *ast.SelectorExpr) coq.StructFieldAccessExpr {
	return coq.StructFieldAccessExpr{
		Struct:         info.name,
		Field:          e.Sel.Name,
		X:              ctx.expr(e.X),
		ThroughPointer: info.throughPointer,
	}
}

func (ctx Ctx) compositeLiteral(e *ast.CompositeLit) coq.Expr {
	if _, ok := ctx.typeOf(e).Underlying().(*types.Slice); ok {
		if len(e.Elts) == 0 {
			return coq.NewCallExpr("nil")
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
	e *ast.CompositeLit) coq.StructLiteral {
	lit := coq.NewStructLiteral(info.name)
	for _, el := range e.Elts {
		switch el := el.(type) {
		case *ast.KeyValueExpr:
			ident, ok := getIdent(el.Key)
			if !ok {
				ctx.noExample(el.Key, "struct field keyed by non-identifier %+v", el.Key)
				return coq.StructLiteral{}
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
func (ctx Ctx) basicLiteral(e *ast.BasicLit) coq.Expr {
	if e.Kind == token.STRING {
		v := ctx.info.Types[e].Value
		s := constant.StringVal(v)
		if strings.ContainsRune(s, '"') {
			ctx.unsupported(e, "string literals with quotes")
		}
		return coq.StringLiteral{s}
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
			return coq.IntLiteral{n}
		} else if info.isUint32() {
			return coq.Int32Literal{uint32(n)}
		} else if info.isUint8() {
			return coq.ByteLiteral{uint8(n)}
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

func (ctx Ctx) binExpr(e *ast.BinaryExpr) coq.Expr {
	op, ok := map[token.Token]coq.BinOp{
		token.LSS:  coq.OpLessThan,
		token.GTR:  coq.OpGreaterThan,
		token.SUB:  coq.OpMinus,
		token.EQL:  coq.OpEquals,
		token.NEQ:  coq.OpNotEquals,
		token.MUL:  coq.OpMul,
		token.QUO:  coq.OpQuot,
		token.REM:  coq.OpRem,
		token.LEQ:  coq.OpLessEq,
		token.GEQ:  coq.OpGreaterEq,
		token.AND:  coq.OpAnd,
		token.LAND: coq.OpLAnd,
		token.OR:   coq.OpOr,
		token.LOR:  coq.OpLOr,
		token.XOR:  coq.OpXor,
		token.SHL:  coq.OpShl,
		token.SHR:  coq.OpShr,
	}[e.Op]
	if e.Op == token.ADD {
		if isString(ctx.typeOf(e.X)) {
			op = coq.OpAppend
		} else {
			op = coq.OpPlus
		}
		ok = true
	}
	if ok {
		expr := coq.BinaryExpr{
			X:  ctx.expr(e.X),
			Op: op,
			Y:  ctx.expr(e.Y),
		}
		if ctx.isNilCompareExpr(e) {
			if _, ok := ctx.typeOf(e.X).(*types.Pointer); ok {
				expr.Y = coq.Null
			}
		}
		return expr
	}
	ctx.unsupported(e, "binary operator %v", e.Op)
	return nil
}

func (ctx Ctx) sliceExpr(e *ast.SliceExpr) coq.Expr {
	if e.Slice3 {
		ctx.unsupported(e, "3-index slice")
		return nil
	}
	x := ctx.expr(e.X)
	if e.Low != nil && e.High == nil {
		return coq.NewCallExpr("SliceSkip",
			ctx.coqTypeOfType(e, sliceElem(ctx.typeOf(e.X))),
			x, ctx.expr(e.Low))
	}
	if e.Low == nil && e.High != nil {
		return coq.NewCallExpr("SliceTake",
			x, ctx.expr(e.High))
	}
	if e.Low != nil && e.High != nil {
		return coq.NewCallExpr("SliceSubslice",
			ctx.coqTypeOfType(e, sliceElem(ctx.typeOf(e.X))),
			x, ctx.expr(e.Low), ctx.expr(e.High))
	}
	if e.Low == nil && e.High == nil {
		ctx.unsupported(e, "complete slice doesn't do anything")
	}
	return nil
}

func (ctx Ctx) nilExpr(e *ast.Ident) coq.Expr {
	t := ctx.typeOf(e)
	switch t.(type) {
	case *types.Pointer:
		return coq.GallinaIdent("null")
	case *types.Slice:
		return coq.GallinaIdent("slice.nil")
	case *types.Basic:
		// TODO: this gets triggered for all of our unit tests because the
		//  nil identifier is mapped to an untyped nil object.
		//  This seems wrong; the runtime representation of each of these
		//  uses depends on the type, so Go must know how they're being used.
		return coq.GallinaIdent("slice.nil")
	default:
		ctx.unsupported(e, "nil of type %v (not pointer or slice)", t)
		return nil
	}
}

func (ctx Ctx) unaryExpr(e *ast.UnaryExpr) coq.Expr {
	if e.Op == token.NOT {
		return coq.NotExpr{ctx.expr(e.X)}
	}
	if e.Op == token.XOR {
		return coq.NotExpr{ctx.expr(e.X)}
	}
	if e.Op == token.AND {
		if x, ok := e.X.(*ast.IndexExpr); ok {
			// e is &a[b] where x is a.b
			if _, ok := ctx.typeOf(x.X).(*types.Slice); ok {
				return coq.NewCallExpr("SliceRef",
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

func (ctx Ctx) variable(s *ast.Ident) coq.Expr {
	info := ctx.identInfo(s)
	if info.IsMacro {
		return coq.GallinaIdent(s.Name)
	}
	e := coq.IdentExpr(s.Name)
	if info.IsPtrWrapped {
		return coq.DerefExpr{X: e, Ty: ctx.coqTypeOfType(s, ctx.typeOf(s))}
	}
	return e
}

func (ctx Ctx) goBuiltin(e *ast.Ident) bool {
	s, ok := ctx.info.Uses[e]
	if !ok {
		return false
	}
	return s.Parent() == types.Universe
}

func (ctx Ctx) identExpr(e *ast.Ident) coq.Expr {
	if ctx.goBuiltin(e) {
		switch e.Name {
		case "nil":
			return ctx.nilExpr(e)
		case "true":
			return coq.True
		case "false":
			return coq.False
		}
		ctx.unsupported(e, "special identifier")
	}
	return ctx.variable(e)
}

func (ctx Ctx) indexExpr(e *ast.IndexExpr, isSpecial bool) coq.CallExpr {
	xTy := ctx.typeOf(e.X).Underlying()
	switch xTy := xTy.(type) {
	case *types.Map:
		e := coq.NewCallExpr("MapGet", ctx.expr(e.X), ctx.expr(e.Index))
		if !isSpecial {
			e = coq.NewCallExpr("Fst", e)
		}
		return e
	case *types.Slice:
		return coq.NewCallExpr("SliceGet",
			ctx.coqTypeOfType(e, xTy.Elem()),
			ctx.expr(e.X), ctx.expr(e.Index))
	}
	ctx.unsupported(e, "index into unknown type %v", xTy)
	return coq.CallExpr{}
}

func (ctx Ctx) derefExpr(e ast.Expr) coq.Expr {
	info, ok := ctx.getStructInfo(ctx.typeOf(e))
	if ok && info.throughPointer {
		return coq.NewCallExpr("struct.load",
			coq.StructDesc(info.name),
			ctx.expr(e))
	}
	return coq.DerefExpr{
		X:  ctx.expr(e),
		Ty: ctx.coqTypeOfType(e, ptrElem(ctx.typeOf(e))),
	}
}

func (ctx Ctx) expr(e ast.Expr) coq.Expr {
	return ctx.exprSpecial(e, false)
}

func (ctx Ctx) funcLit(e *ast.FuncLit) coq.FuncLit {
	fl := coq.FuncLit{}

	fl.Args = ctx.paramList(e.Type.Params)
	// fl.ReturnType = ctx.returnType(d.Type.Results)
	fl.Body = ctx.blockStmt(e.Body, ExprValReturned)
	return fl
}

func (ctx Ctx) exprSpecial(e ast.Expr, isSpecial bool) coq.Expr {
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

func (ctx Ctx) blockStmt(s *ast.BlockStmt, usage ExprValUsage) coq.BlockExpr {
	return ctx.stmts(s.List, usage)
}

type cursor struct {
	Stmts []ast.Stmt
}

// HasNext returns true if the cursor has any remaining statements
func (c cursor) HasNext() bool {
	return len(c.Stmts) > 0
}

// Next returns the next statement. Requires that the cursor is non-empty (check with HasNext()).
func (c *cursor) Next() ast.Stmt {
	s := c.Stmts[0]
	c.Stmts = c.Stmts[1:]
	return s
}

// Remainder consumes and returns all remaining statements
func (c *cursor) Remainder() []ast.Stmt {
	s := c.Stmts
	c.Stmts = nil
	return s
}

// If this returns true, the body truly *must* always end in an early return or loop control effect.
func (ctx Ctx) endsWithReturn(s ast.Stmt) bool {
	if s == nil {
		return false
	}
	switch s := s.(type) {
	case *ast.BlockStmt:
		return ctx.stmtsEndWithReturn(s.List)
	default:
		return ctx.stmtsEndWithReturn([]ast.Stmt{s})
	}
}

func (ctx Ctx) stmtsEndWithReturn(ss []ast.Stmt) bool {
	if len(ss) == 0 {
		return false
	}
	switch s := ss[len(ss)-1].(type) {
	case *ast.ReturnStmt, *ast.BranchStmt:
		return true
	case *ast.IfStmt:
		left := ctx.endsWithReturn(s.Body)
		right := ctx.endsWithReturn(s.Else)
		return left && right // we can only return true if we *always* end in a control effect
	}
	return false
}

func (ctx Ctx) stmts(ss []ast.Stmt, usage ExprValUsage) coq.BlockExpr {
	c := &cursor{ss}
	var bindings []coq.Binding
	var finalized bool
	for c.HasNext() {
		s := c.Next()
		// ifStmt is special, it gets a chance to "wrap" the entire remainder
		// to better support early returns.
		switch s := s.(type) {
		case *ast.IfStmt:
			bindings = append(bindings, ctx.ifStmt(s, c.Remainder(), usage))
			finalized = true
			break // This would happen anyway since we consumed the iterator via "Remainder"
		default:
			// All other statements are translated one-by-one
			if c.HasNext() {
				bindings = append(bindings, ctx.stmt(s))
			} else {
				// The last statement is special: we propagate the usage and store "finalized"
				binding, fin := ctx.stmtInBlock(s, usage)
				bindings = append(bindings, binding)
				finalized = fin
			}
		}
	}
	// Crucially, we also arrive in this branch if the list of statements is empty.
	if !finalized {
		switch usage {
		case ExprValReturned:
			bindings = append(bindings, coq.NewAnon(coq.ReturnExpr{coq.Tt}))
		case ExprValLoop:
			bindings = append(bindings, coq.NewAnon(coq.LoopContinue))
		case ExprValLocal:
			// Make sure the list of bindings is not empty -- translate empty blocks to unit
			if len(bindings) == 0 {
				bindings = append(bindings, coq.NewAnon(coq.ReturnExpr{coq.Tt}))
			}
		default:
			panic("bad ExprValUsage")
		}
	}
	return coq.BlockExpr{bindings}
}

// ifStmt has special support for an early-return "then" branch; to achieve that
// it is responsible for generating the if *together with* all the statements that
// follow it in the same block.
// It is also responsible for "finalizing" the expression according to the usage.
func (ctx Ctx) ifStmt(s *ast.IfStmt, remainder []ast.Stmt, usage ExprValUsage) coq.Binding {
	// TODO: be more careful about nested if statements; if the then branch has
	//  an if statement with early return, this is probably not handled correctly.
	//  We should conservatively disallow such returns until they're properly analyzed.
	if s.Init != nil {
		ctx.unsupported(s.Init, "if statement initializations")
		return coq.Binding{}
	}
	condExpr := ctx.expr(s.Cond)
	ife := coq.IfExpr{
		Cond: condExpr,
	}
	// Extract (possibly empty) block in Else
	var Else = &ast.BlockStmt{List: []ast.Stmt{}}
	if s.Else != nil {
		Else = s.Else.(*ast.BlockStmt)
	}

	// Supported cases are:
	// - There is no code after the conditional -- then anything goes.
	// - The "then" branch always returns, and there is no "else" branch.
	// - Neither "then" nor "else" ever return.

	if len(remainder) == 0 {
		// The remainder is empty, so just propagate the usage to both branches.
		ife.Then = ctx.blockStmt(s.Body, usage)
		ife.Else = ctx.blockStmt(Else, usage)
		return coq.NewAnon(ife)
	}

	// There is code after the conditional -- merging control flow. Let us see what we can do.
	// Determine if we want to propagate our usage (i.e. the availability of control effects)
	// to the conditional or not.
	if ctx.endsWithReturn(s.Body) {
		ife.Then = ctx.blockStmt(s.Body, usage)
		// Put trailing code into "else". This is correct because "then" will always return.
		// "else" must be empty.
		if len(Else.List) > 0 {
			ctx.futureWork(s.Else, "early return in if with an else branch")
			return coq.Binding{}
		}
		// We can propagate the usage here since the return value of this part
		// will become the return value of the entire conditional (that's why we
		// put the remainder *inside* the conditional).
		ife.Else = ctx.stmts(remainder, usage)
		return coq.NewAnon(ife)
	}

	// No early return in "then" branch; translate this as a conditional in the middle of
	// a block (not propagating the usage). This will implicitly check that
	// the two branches do not rely on control effects.
	ife.Then = ctx.blockStmt(s.Body, ExprValLocal)
	ife.Else = ctx.blockStmt(Else, ExprValLocal)
	// And translate the remainder with our usage.
	tailExpr := ctx.stmts(remainder, usage)
	// Prepend the if-then-else before the tail.
	bindings := append([]coq.Binding{coq.NewAnon(ife)}, tailExpr.Bindings...)
	return coq.NewAnon(coq.BlockExpr{Bindings: bindings})
}

func (ctx Ctx) loopVar(s ast.Stmt) (ident *ast.Ident, init coq.Expr) {
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

func (ctx Ctx) forStmt(s *ast.ForStmt) coq.ForLoopExpr {
	var init = coq.NewAnon(coq.Skip)
	var ident *ast.Ident
	if s.Init != nil {
		ident, _ = ctx.loopVar(s.Init)
		ctx.addDef(ident, identInfo{
			IsPtrWrapped: true,
		})
		init = ctx.stmt(s.Init)
	}
	var cond coq.Expr = coq.True
	if s.Cond != nil {
		cond = ctx.expr(s.Cond)
	}
	var post coq.Expr = coq.Skip
	if s.Post != nil {
		postBlock := ctx.stmt(s.Post)
		if len(postBlock.Names) > 0 {
			ctx.unsupported(s.Post, "post cannot bind names")
		}
		post = postBlock.Expr
	}

	body := ctx.blockStmt(s.Body, ExprValLoop)
	return coq.ForLoopExpr{
		Init: init,
		Cond: cond,
		Post: post,
		Body: body,
	}
}

func getIdentOrAnonymous(e ast.Expr) (ident string, ok bool) {
	if e == nil {
		return "_", true
	}
	return getIdent(e)
}

func (ctx Ctx) getMapClearIdiom(s *ast.RangeStmt) coq.Expr {
	if _, ok := ctx.typeOf(s.X).(*types.Map); !ok {
		return nil
	}
	key, ok := getIdent(s.Key)
	if !ok {
		ctx.nope(s.Key, "range with non-ident key")
		return nil
	}
	if s.Value != nil {
		return nil
	}
	if len(s.Body.List) != 1 {
		return nil
	}
	exprStmt, ok := s.Body.List[0].(*ast.ExprStmt)
	if !ok {
		return nil
	}
	callExpr, ok := exprStmt.X.(*ast.CallExpr)
	if !(ok && isIdent(callExpr.Fun, "delete") && len(callExpr.Args) == 2) {
		return nil
	}
	// we have a single call to a delete
	mapName, ok := getIdent(s.X)
	if !ok {
		ctx.unsupported(s.X, "clearing a complex map expression")
	}
	if !(isIdent(callExpr.Args[0], mapName) &&
		isIdent(callExpr.Args[1], key)) {
		return nil
	}
	return coq.NewCallExpr("MapClear", coq.IdentExpr(mapName))
}

func (ctx Ctx) mapRangeStmt(s *ast.RangeStmt) coq.Expr {
	if expr := ctx.getMapClearIdiom(s); expr != nil {
		return expr
	}
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
	return coq.MapIterExpr{
		KeyIdent:   key,
		ValueIdent: val,
		Map:        ctx.expr(s.X),
		Body:       ctx.blockStmt(s.Body, ExprValLocal),
	}
}

func getIdentOrNil(e ast.Expr) *ast.Ident {
	if id, ok := e.(*ast.Ident); ok {
		return id
	}
	return nil
}

func (ctx Ctx) identBinder(id *ast.Ident) coq.Binder {
	if id == nil {
		return coq.Binder(nil)
	}
	e := coq.IdentExpr(id.Name)
	return &e
}

func (ctx Ctx) sliceRangeStmt(s *ast.RangeStmt) coq.Expr {
	key := getIdentOrNil(s.Key)
	val := getIdentOrNil(s.Value)
	if key != nil {
		ctx.addDef(key, identInfo{
			IsPtrWrapped: false,
			IsMacro:      false,
		})
	}
	if val != nil {
		ctx.addDef(val, identInfo{
			IsPtrWrapped: false,
			IsMacro:      false,
		})
	}
	return coq.SliceLoopExpr{
		Key:   ctx.identBinder(key),
		Val:   ctx.identBinder(val),
		Slice: ctx.expr(s.X),
		Ty:    ctx.coqTypeOfType(s.X, sliceElem(ctx.typeOf(s.X))),
		Body:  ctx.blockStmt(s.Body, ExprValLocal),
	}
}

func (ctx Ctx) rangeStmt(s *ast.RangeStmt) coq.Expr {
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

func (ctx Ctx) referenceTo(rhs ast.Expr) coq.Expr {
	return coq.RefExpr{
		X:  ctx.expr(rhs),
		Ty: ctx.coqTypeOfType(rhs, ctx.typeOf(rhs)),
	}
}

func (ctx Ctx) defineStmt(s *ast.AssignStmt) coq.Binding {
	if len(s.Rhs) > 1 {
		ctx.futureWork(s, "multiple defines (split them up)")
	}
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
			if !ctx.doesDefHaveInfo(ident) {
				ctx.addDef(ident, identInfo{
					IsPtrWrapped: false,
					IsMacro:      false,
				})
			}
		} else {
			ctx.nope(lhsExpr, "defining a non-identifier")
		}
	}
	var names []string
	for _, ident := range idents {
		names = append(names, ident.Name)
	}
	// NOTE: this checks whether the identifier being defined is supposed to be
	// 	pointer wrapped, so to work correctly the caller must set this identInfo
	// 	before processing the defining expression.
	if len(idents) == 1 && ctx.definesPtrWrapped(idents[0]) {
		return coq.Binding{Names: names, Expr: ctx.referenceTo(rhs)}
	} else {
		return coq.Binding{Names: names, Expr: ctx.exprSpecial(rhs, len(idents) == 2)}
	}
}

func (ctx Ctx) varSpec(s *ast.ValueSpec) coq.Binding {
	if len(s.Names) > 1 {
		ctx.unsupported(s, "multiple declarations in one block")
	}
	lhs := s.Names[0]
	ctx.addDef(lhs, identInfo{
		IsPtrWrapped: true,
		IsMacro:      false,
	})
	var rhs coq.Expr
	if len(s.Values) == 0 {
		ty := ctx.typeOf(lhs)
		rhs = coq.NewCallExpr("ref",
			coq.NewCallExpr("zero_val", ctx.coqTypeOfType(s, ty)))
	} else {
		rhs = ctx.referenceTo(s.Values[0])
	}
	return coq.Binding{
		Names: []string{lhs.Name},
		Expr:  rhs,
	}
}

// varDeclStmt translates declarations within functions
func (ctx Ctx) varDeclStmt(s *ast.DeclStmt) coq.Binding {
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
//   note that we will no longer special-case when the reference is to a
//   basic value and will use generic type-based support in Coq,
//   hence on the Coq side we'll always have to reduce type-based loads and
//   stores when they end up loading single-word values.
func (ctx Ctx) refExpr(s ast.Expr) coq.Expr {
	switch s := s.(type) {
	case *ast.Ident:
		// this is the intended translation even if s is pointer-wrapped
		return coq.IdentExpr(s.Name)
	case *ast.SelectorExpr:
		ty := ctx.typeOf(s.X)
		info, ok := ctx.getStructInfo(ty)
		if !ok {
			ctx.unsupported(s,
				"reference to selector from non-struct type %v", ty)
		}
		fieldName := s.Sel.Name

		var structExpr coq.Expr
		if info.throughPointer {
			structExpr = ctx.expr(s.X)
		} else {
			structExpr = ctx.refExpr(s.X)
		}
		return coq.NewCallExpr("struct.fieldRef", coq.StructDesc(info.name),
			coq.GallinaString(fieldName), structExpr)
	// TODO: should move support for slice indexing here as well
	default:
		ctx.futureWork(s, "reference to other types of expressions")
		return nil
	}
}

func (ctx Ctx) pointerAssign(dst *ast.Ident, x coq.Expr) coq.Binding {
	ty := ctx.typeOf(dst)
	return coq.NewAnon(coq.StoreStmt{
		Dst: coq.IdentExpr(dst.Name),
		X:   x,
		Ty:  ctx.coqTypeOfType(dst, ty),
	})
}

func (ctx Ctx) assignFromTo(s ast.Node,
	lhs ast.Expr, rhs coq.Expr) coq.Binding {
	// assignments can mean various things
	switch lhs := lhs.(type) {
	case *ast.Ident:
		if lhs.Name == "_" {
			return coq.NewAnon(rhs)
		}
		if ctx.identInfo(lhs).IsPtrWrapped {
			return ctx.pointerAssign(lhs, rhs)
		}
		ctx.unsupported(s, "variable %s is not assignable\n\t(declare it with 'var' to pointer-wrap in GooseLang and support re-assignment)", lhs.Name)
	case *ast.IndexExpr:
		targetTy := ctx.typeOf(lhs.X)
		switch targetTy := targetTy.(type) {
		case *types.Slice:
			value := rhs
			return coq.NewAnon(coq.NewCallExpr(
				"SliceSet",
				ctx.coqTypeOfType(lhs, targetTy.Elem()),
				ctx.expr(lhs.X),
				ctx.expr(lhs.Index),
				value))
		case *types.Map:
			value := rhs
			return coq.NewAnon(coq.NewCallExpr(
				"MapInsert",
				ctx.expr(lhs.X),
				ctx.expr(lhs.Index),
				value))
		default:
			ctx.unsupported(s, "index update to unexpected target of type %v", targetTy)
		}
	case *ast.StarExpr:
		info, ok := ctx.getStructInfo(ctx.typeOf(lhs.X))
		if ok && info.throughPointer {
			return coq.NewAnon(coq.NewCallExpr("struct.store",
				coq.StructDesc(info.name),
				ctx.expr(lhs.X),
				rhs))
		}
		dstPtrTy, ok := ctx.typeOf(lhs.X).Underlying().(*types.Pointer)
		if !ok {
			ctx.unsupported(s,
				"could not identify element type of assignment through pointer")
		}
		return coq.NewAnon(coq.StoreStmt{
			Dst: ctx.expr(lhs.X),
			Ty:  ctx.coqTypeOfType(s, dstPtrTy.Elem()),
			X:   rhs,
		})
	case *ast.SelectorExpr:
		ty := ctx.typeOf(lhs.X)
		info, ok := ctx.getStructInfo(ty)
		var structExpr coq.Expr
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
			return coq.NewAnon(coq.NewCallExpr("struct.storeF",
				coq.StructDesc(info.name),
				coq.GallinaString(fieldName),
				structExpr,
				rhs))
		}
		ctx.unsupported(s,
			"assigning to field of non-struct type %v", ty)
	default:
		ctx.unsupported(s, "assigning to complex expression")
	}
	return coq.Binding{}
}

func (ctx Ctx) assignStmt(s *ast.AssignStmt) coq.Binding {
	if s.Tok == token.DEFINE {
		return ctx.defineStmt(s)
	}
	if len(s.Lhs) > 1 || len(s.Rhs) > 1 {
		ctx.unsupported(s, "multiple assignment")
	}
	lhs := s.Lhs[0]
	rhs := ctx.expr(s.Rhs[0])
	assignOps := map[token.Token]coq.BinOp{
		token.ADD_ASSIGN: coq.OpPlus,
		token.SUB_ASSIGN: coq.OpMinus,
	}
	if op, ok := assignOps[s.Tok]; ok {
		rhs = coq.BinaryExpr{
			X:  ctx.expr(lhs),
			Op: op,
			Y:  rhs,
		}
	} else if s.Tok != token.ASSIGN {
		ctx.unsupported(s, "%v assignment", s.Tok)
	}
	return ctx.assignFromTo(s, lhs, rhs)
}

func (ctx Ctx) incDecStmt(stmt *ast.IncDecStmt) coq.Binding {
	ident := getIdentOrNil(stmt.X)
	if ident == nil {
		ctx.todo(stmt, "cannot inc/dec non-var")
		return coq.Binding{}
	}
	if !ctx.identInfo(ident).IsPtrWrapped {
		// should also be able to support variables that are of pointer type
		ctx.todo(stmt, "can only inc/dec pointer-wrapped variables")
	}
	op := coq.OpPlus
	if stmt.Tok == token.DEC {
		op = coq.OpMinus
	}
	return ctx.pointerAssign(ident, coq.BinaryExpr{
		X:  ctx.expr(stmt.X),
		Op: op,
		Y:  coq.IntLiteral{1},
	})
}

func (ctx Ctx) spawnExpr(thread ast.Expr) coq.SpawnExpr {
	f, ok := thread.(*ast.FuncLit)
	if !ok {
		ctx.futureWork(thread,
			"only function literal spawns are supported")
		return coq.SpawnExpr{}
	}
	return coq.SpawnExpr{Body: ctx.blockStmt(f.Body, ExprValLocal)}
}

func (ctx Ctx) branchStmt(s *ast.BranchStmt) coq.Expr {
	if s.Tok == token.CONTINUE {
		return coq.LoopContinue
	}
	if s.Tok == token.BREAK {
		return coq.LoopBreak
	}
	ctx.noExample(s, "unexpected control flow %v in loop", s.Tok)
	return nil
}

// getSpawn returns a non-nil spawned thread if the expression is a go call
func (ctx Ctx) goStmt(e *ast.GoStmt) coq.Expr {
	if len(e.Call.Args) > 0 {
		ctx.unsupported(e, "go statement with parameters")
	}
	return ctx.spawnExpr(e.Call.Fun)
}

// This function also returns wether the expression has been "finalized",
// which means the usage has been taken care of. If it is not finalized,
// the caller is responsible for adding a trailing "return unit"/"continue".
func (ctx Ctx) stmtInBlock(s ast.Stmt, usage ExprValUsage) (coq.Binding, bool) {
	// First the case where the statement matches the usage, i.e. the necessary
	// control effect is actually available.
	switch usage {
	case ExprValReturned:
		s, ok := s.(*ast.ReturnStmt)
		if ok {
			return coq.NewAnon(ctx.returnExpr(s.Results)), true
		}
	case ExprValLoop:
		s, ok := s.(*ast.BranchStmt)
		if ok {
			return coq.NewAnon(ctx.branchStmt(s)), true
		}
	}
	// Some statements can handle the usage themselves, and they make sure to finalize it, too
	switch s := s.(type) {
	case *ast.IfStmt:
		return ctx.ifStmt(s, []ast.Stmt{}, usage), true
	case *ast.BlockStmt:
		return coq.NewAnon(ctx.blockStmt(s, usage)), true
	}
	// For everything else, we generate the statement and possibly tell the caller
	// that this is not yet finalized.
	var binding coq.Binding = coq.Binding{}
	switch s := s.(type) {
	case *ast.ReturnStmt:
		ctx.futureWork(s, "return in unsupported position")
	case *ast.BranchStmt:
		ctx.futureWork(s, "break/continue in unsupported position")
	case *ast.GoStmt:
		binding = coq.NewAnon(ctx.goStmt(s))
	case *ast.ExprStmt:
		binding = coq.NewAnon(ctx.expr(s.X))
	case *ast.AssignStmt:
		binding = ctx.assignStmt(s)
	case *ast.DeclStmt:
		binding = ctx.varDeclStmt(s)
	case *ast.IncDecStmt:
		binding = ctx.incDecStmt(s)
	case *ast.ForStmt:
		// note that this might be a nested loop,
		// in which case the loop var gets replaced by the inner loop.
		binding = coq.NewAnon(ctx.forStmt(s))
	case *ast.RangeStmt:
		binding = coq.NewAnon(ctx.rangeStmt(s))
	case *ast.SwitchStmt:
		ctx.todo(s, "check for switch statement")
	case *ast.TypeSwitchStmt:
		ctx.todo(s, "check for type switch statement")
	default:
		ctx.unsupported(s, "statement")
	}
	switch usage {
	case ExprValLocal:
		// Nothing to finalize.
		return binding, true
	default:
		// Finalization required
		return binding, false
	}
}

// Translate a single statement without usage (i.e., no control effects available)
func (ctx Ctx) stmt(s ast.Stmt) coq.Binding {
	// stmts takes care of finalization...
	binding, finalized := ctx.stmtInBlock(s, ExprValLocal)
	if !finalized {
		panic("ExprValLocal usage should always be finalized")
	}
	return binding
}

func (ctx Ctx) returnExpr(es []ast.Expr) coq.Expr {
	if len(es) == 0 {
		// named returns are not supported, so this must return unit
		return coq.ReturnExpr{coq.UnitLiteral{}}
	}
	var exprs coq.TupleExpr
	for _, r := range es {
		exprs = append(exprs, ctx.expr(r))
	}
	return coq.ReturnExpr{coq.NewTuple(exprs)}
}

// returnType converts an Ast.FuncType's Results to a Coq return type
func (ctx Ctx) returnType(results *ast.FieldList) coq.Type {
	if results == nil {
		return coq.TypeIdent("unitT")
	}
	rs := results.List
	for _, r := range rs {
		if len(r.Names) > 0 {
			ctx.unsupported(r, "named returned value")
			return coq.TypeIdent("<invalid>")
		}
	}
	var ts []coq.Type
	for _, r := range rs {
		if len(r.Names) > 0 {
			ctx.unsupported(r, "named returned value")
			return coq.TypeIdent("<invalid>")
		}
		ts = append(ts, ctx.coqType(r.Type))
	}
	return coq.NewTupleType(ts)
}

func (ctx Ctx) funcDecl(d *ast.FuncDecl) coq.FuncDecl {
	fd := coq.FuncDecl{Name: d.Name.Name, AddTypes: ctx.Config.TypeCheck}
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
		fd.Name = coq.StructMethod(structInfo.name, d.Name.Name)
		fd.Args = append(fd.Args, ctx.field(receiver))
	}
	fd.Args = append(fd.Args, ctx.paramList(d.Type.Params)...)
	fd.ReturnType = ctx.returnType(d.Type.Results)
	fd.Body = ctx.blockStmt(d.Body, ExprValReturned)
	return fd
}

func (ctx Ctx) constSpec(spec *ast.ValueSpec) coq.ConstDecl {
	ident := spec.Names[0]
	cd := coq.ConstDecl{
		Name:     ident.Name,
		AddTypes: ctx.Config.TypeCheck,
	}
	ctx.addDef(ident, identInfo{
		IsPtrWrapped: false,
		IsMacro:      true,
	})
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

func (ctx Ctx) constDecl(d *ast.GenDecl) []coq.Decl {
	var specs []coq.Decl
	for _, spec := range d.Specs {
		specs = append(specs, ctx.constSpec(spec.(*ast.ValueSpec)))
	}
	return specs
}

func (ctx Ctx) globalVarDecl(d *ast.GenDecl) []coq.Decl {
	// NOTE: this treats globals as constants, which is unsound but used for a
	// configurable Debug level in goose-nfsd. Configuration variables should
	// instead be treated as a non-deterministic constant, assuming they aren't
	// changed after startup.
	var specs []coq.Decl
	for _, spec := range d.Specs {
		specs = append(specs, ctx.constSpec(spec.(*ast.ValueSpec)))
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
	"github.com/tchajed/goose/machine":         true,
	"github.com/tchajed/goose/machine/filesys": true,
	"github.com/mit-pdos/gokv/grove_ffi":       true,
	"github.com/tchajed/goose/machine/disk":    true,
	"sync":                                     true,
	"log":                                      true,
	"fmt":                                      true,
}

var ffiMapping = map[string]string{
	"github.com/mit-pdos/gokv/grove_ffi":    "grove",
	"github.com/tchajed/goose/machine/disk": "disk",
}

func (ctx Ctx) imports(d []ast.Spec) []coq.Decl {
	var decls []coq.Decl
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
			decls = append(decls, coq.ImportDecl{importPath})
		}
	}
	return decls
}

func (ctx Ctx) exprInterface(cvs []coq.Decl, expr ast.Expr, d *ast.FuncDecl) []coq.Decl {
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

func (ctx Ctx) stmtInterface(cvs []coq.Decl, stmt ast.Stmt, d *ast.FuncDecl) []coq.Decl {
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

func (ctx Ctx) callExprInterface(cvs []coq.Decl, r *ast.CallExpr, d *ast.FuncDecl) []coq.Decl {
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
				cv := coq.StructToInterface{Struct: structName, Interface: interfaceName, Methods: methods}
				if len(cv.Coq()) > 1 && len(cv.MethodList()) > 0 {
					cvs = append(cvs, cv)
				}
			}
		}
	}
	return cvs
}

func (ctx Ctx) maybeDecls(d ast.Decl) []coq.Decl {
	switch d := d.(type) {
	case *ast.FuncDecl:
		cvs := []coq.Decl{}
		for _, stmt := range d.Body.List {
			cvs = ctx.stmtInterface(cvs, stmt, d)
		}
		fd := ctx.funcDecl(d)
		results := []coq.Decl{}
		if len(cvs) > 0 {
			results = append(cvs, fd)
		} else {
			results = []coq.Decl{fd}
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
			ty := ctx.typeDecl(d.Doc, spec)
			return []coq.Decl{ty}
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
