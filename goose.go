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
)

type identInfo struct {
	IsPtrWrapped bool
	IsMacro      bool
}

type scopedName struct {
	scope *types.Scope
	name  string
}

type identCtx struct {
	info map[scopedName]identInfo
}

func newIdentCtx() identCtx {
	return identCtx{info: make(map[scopedName]identInfo)}
}

func (ctx Ctx) lookupIdentScope(ident *ast.Ident) scopedName {
	obj, ok := ctx.info.Uses[ident]
	if !ok {
		return scopedName{nil, ""}
	}
	useScope := obj.Parent()
	name := ident.Name
	defScope, _ := useScope.LookupParent(name, ident.Pos())
	return scopedName{scope: defScope, name: name}
}

func (idents identCtx) lookupName(scope *types.Scope, name string) identInfo {
	if scope == types.Universe {
		return identInfo{
			IsPtrWrapped: false,
			// TODO: setting this to true triggers too often
			IsMacro: false,
		}
	}
	info, ok := idents.info[scopedName{scope, name}]
	if ok {
		return info
	}
	return idents.lookupName(scope.Parent(), name)
}

func (ctx Ctx) identInfo(ident *ast.Ident) identInfo {
	scope := ctx.info.Uses[ident].Parent()
	return ctx.idents.lookupName(scope, ident.Name)
}

func (ctx Ctx) doesDefHaveInfo(ident *ast.Ident) bool {
	obj := ctx.info.Defs[ident]
	if obj == nil {
		// ident is not actually a definition (this is what happens when you
		// multiply assign variables and only one of them is fresh - the others
		// are not being defined but just re-assigned)
		return true
	}
	defScope := obj.Parent()
	key := scopedName{scope: defScope, name: ident.Name}
	_, ok := ctx.idents.info[key]
	return ok
}

func (ctx Ctx) addDef(ident *ast.Ident, info identInfo) {
	if ident.Name == "_" {
		return
	}
	obj := ctx.info.Defs[ident]
	defScope := obj.Parent()
	key := scopedName{scope: defScope, name: ident.Name}
	ctx.idents.info[key] = info
}

func (ctx Ctx) definesPtrWrapped(ident *ast.Ident) bool {
	obj := ctx.info.Defs[ident]
	defScope := obj.Parent()
	key := scopedName{scope: defScope, name: ident.Name}
	return ctx.idents.info[key].IsPtrWrapped
}

// Ctx is a context for resolving Go code's types and source code
type Ctx struct {
	idents identCtx
	info   *types.Info
	fset   *token.FileSet
	errorReporter
	Config
}

// Config holds global configuration for Coq conversion
type Config struct {
	AddSourceFileComments bool
	TypeCheck             bool
}

// NewCtx initializes a context
func NewCtx(fset *token.FileSet, config Config) Ctx {
	info := &types.Info{
		Defs:   make(map[*ast.Ident]types.Object),
		Uses:   make(map[*ast.Ident]types.Object),
		Types:  make(map[ast.Expr]types.TypeAndValue),
		Scopes: make(map[ast.Node]*types.Scope),
	}
	return Ctx{
		idents:        newIdentCtx(),
		info:          info,
		fset:          fset,
		errorReporter: newErrorReporter(fset),
		Config:        config,
	}
}

// TypeCheck type-checks a set of files and stores the result in the Ctx
//
// This is needed before conversion to Coq to disambiguate some methods.
func (ctx Ctx) TypeCheck(pkgName string, files []*ast.File) error {
	imp := importer.ForCompiler(ctx.fset, "source", nil)
	conf := types.Config{Importer: imp}
	_, err := conf.Check(pkgName, ctx.fset, files, ctx.info)
	return err
}

func (ctx Ctx) where(node ast.Node) string {
	return ctx.fset.Position(node.Pos()).String()
}

func (ctx Ctx) printGo(node ast.Node) string {
	var what bytes.Buffer
	err := printer.Fprint(&what, ctx.fset, node)
	if err != nil {
		panic(err.Error())
	}
	return what.String()
}

func (ctx Ctx) typeOf(e ast.Expr) types.Type {
	return ctx.info.TypeOf(e)
}

func (ctx Ctx) getType(e ast.Expr) (typ types.Type, ok bool) {
	typ = ctx.typeOf(e)
	ok = typ != types.Typ[types.Invalid]
	return
}

func getIdent(e ast.Expr) (ident string, ok bool) {
	if ident, ok := e.(*ast.Ident); ok {
		return ident.Name, true
	}
	return "", false
}

func isIdent(e ast.Expr, ident string) bool {
	i, ok := getIdent(e)
	return ok && i == ident
}

func (ctx Ctx) mapType(e *ast.MapType) coq.MapType {
	switch k := e.Key.(type) {
	case *ast.Ident:
		if k.Name == "uint64" {
			return coq.MapType{ctx.coqType(e.Value)}
		}
	}
	ctx.unsupported(e, "maps must be from uint64 (not %v)", e.Key)
	return coq.MapType{}
}

func (ctx Ctx) selectorExprType(e *ast.SelectorExpr) coq.TypeIdent {
	if isIdent(e.X, "filesys") && isIdent(e.Sel, "File") {
		return "fileT"
	}
	if isIdent(e.X, "disk") && isIdent(e.Sel, "Block") {
		return "disk.blockT"
	}
	ctx.unsupported(e, "unknown package type %s", e)
	return "<selector expr>"
}

func (ctx Ctx) coqTypeOfType(n ast.Node, t types.Type) coq.Type {
	// TODO: move support for various types in ctx.coqType with this function
	//
	// ctx.coqType operates syntactically whereas this function uses type
	// checker info. We can always write ctx.coqType in terms of this function,
	// since the go/types package will give a types.Type expression for the
	// "type" of an Ast.Expr representing a type. Improving this function is
	// also useful because there are some situations where there is no
	// syntactic type and we need to operate on the output of type inference
	// anyway.
	switch t := t.(type) {
	case *types.Named:
		if _, ok := t.Underlying().(*types.Struct); ok {
			return coq.StructName(t.Obj().Name())
		}
		return coq.TypeIdent(t.Obj().Name())
	case *types.Struct:
		return coq.StructName(t.String())
	case *types.Basic:
		switch t.Name() {
		case "uint64":
			return coq.TypeIdent("uint64T")
		case "uint32":
			return coq.TypeIdent("uint32T")
		case "byte":
			return coq.TypeIdent("byteT")
		case "bool":
			return coq.TypeIdent("boolT")
		case "string", "untyped string":
			return coq.TypeIdent("stringT")
		default:
			ctx.unsupported(n, "basic type %s", t.Name())
		}
	}
	return coq.TypeIdent("<type>")
}

func (ctx Ctx) arrayType(e *ast.ArrayType) coq.Type {
	if e.Len != nil {
		t := ctx.typeOf(e).(*types.Array)
		return coq.ArrayType{Len: uint64(t.Len()), Elt: ctx.coqType(e.Elt)}
	}
	return coq.SliceType{ctx.coqType(e.Elt)}
}

func (ctx Ctx) ptrType(e *ast.StarExpr) coq.Type {
	// check for *sync.RWMutex
	if e, ok := e.X.(*ast.SelectorExpr); ok {
		if isIdent(e.X, "sync") && isIdent(e.Sel, "RWMutex") {
			return coq.TypeIdent("lockRefT")
		}
	}
	info, ok := getStructInfo(ctx.typeOf(e.X))
	if ok {
		return coq.NewCallExpr("struct.ptrT", coq.StructDesc(info.name))
	}
	return coq.PtrType{ctx.coqType(e.X)}
}

func (ctx Ctx) coqType(e ast.Expr) coq.Type {
	switch e := e.(type) {
	case *ast.Ident:
		if ctx.identInfo(e).IsMacro {
			return coq.TypeIdent(e.Name)
		}
		return ctx.coqTypeOfType(e, ctx.typeOf(e))
	case *ast.MapType:
		return ctx.mapType(e)
	case *ast.SelectorExpr:
		return ctx.selectorExprType(e)
	case *ast.ArrayType:
		return ctx.arrayType(e)
	case *ast.StarExpr:
		return ctx.ptrType(e)
	default:
		ctx.unsupported(e, "unexpected type expr")
	}
	return coq.TypeIdent("<type>")
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
		info, ok := getStructInfo(ctx.typeOf(f.Type))
		if ok && info.name == structName && info.throughPointer {
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
	switch xTy.(type) {
	case *types.Slice:
		return coq.NewCallExpr("slice.len", ctx.expr(x))
	case *types.Map:
		return coq.NewCallExpr("MapLen", ctx.expr(x))
	default:
		ctx.unsupported(e, "length of object of type %v", xTy)
		return coq.CallExpr{}
	}
}

func isLockRef(t types.Type) bool {
	if t, ok := t.(*types.Pointer); ok {
		if elTy, ok := t.Elem().(*types.Named); ok {
			name := elTy.Obj()
			return name.Pkg().Name() == "sync" &&
				name.Name() == "RWMutex"
		}
	}
	return false
}

func isByteSlice(t types.Type) bool {
	if t, ok := t.(*types.Slice); ok {
		if elTy, ok := t.Elem().(*types.Basic); ok {
			return elTy.Name() == "byte"
		}
	}
	return false
}

func isString(t types.Type) bool {
	if t, ok := t.(*types.Basic); ok {
		return t.Name() == "string"
	}
	return false
}

func (ctx Ctx) lockMethod(f *ast.SelectorExpr) coq.CallExpr {
	var args []coq.Expr
	var acquire, writer bool
	switch f.Sel.Name {
	case "Lock":
		acquire, writer = true, true
	case "RLock":
		acquire, writer = true, false
	case "Unlock":
		acquire, writer = false, true
	case "RUnlock":
		acquire, writer = false, false
	default:
		ctx.unsupported(f, "method %s of sync.RWMutex", f.Sel.Name)
		return coq.CallExpr{}
	}
	if writer {
		args = append(args, coq.GallinaIdent("Writer"))
	} else {
		args = append(args, coq.GallinaIdent("Reader"))
	}
	args = append(args, ctx.expr(f.X))
	if acquire {
		return coq.NewCallExpr("Data.lockAcquire", args...)
	}
	return coq.NewCallExpr("Data.lockRelease", args...)

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
	if isIdent(f.X, "globals") {
		switch f.Sel.Name {
		case "SetX", "GetX":
			return ctx.newCoqCall("Globals."+toInitialLower(f.Sel.Name), args)
		default:
			ctx.futureWork(f, "unhandled call to globals.%s", f.Sel.Name)
			return coq.CallExpr{}
		}
	}
	if isIdent(f.X, "machine") {
		switch f.Sel.Name {
		case "UInt64Get", "UInt64Put", "UInt32Get", "UInt32Put":
			return ctx.newCoqCall(f.Sel.Name, args)
		case "RandomUint64":
			return ctx.newCoqCall("Data.randomUint64", nil)
		case "UInt64ToString":
			return ctx.newCoqCall("uint64_to_string", args)
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
	ctx.unsupported(f, "cannot call methods selected from %s", f.X)
	return coq.CallExpr{}
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
	if t, ok := selectorType.(*types.Pointer); ok {
		selectorType = t.Elem()
	}
	structInfo, ok := getStructInfo(selectorType)
	if ok {
		callArgs := append([]ast.Expr{f.X}, args...)
		return ctx.newCoqCall(
			coq.StructMethod(structInfo.name, f.Sel.Name),
			callArgs)
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
	switch f := call.Fun.(type) {
	case *ast.Ident:
		if f.Name == "string" {
			arg := args[0]
			if !isByteSlice(ctx.typeOf(arg)) {
				ctx.unsupported(arg,
					"conversion from type %v to string", ctx.typeOf(arg))
				return coq.CallExpr{}
			}
			return ctx.newCoqCall("Data.bytesToString", args)
		}
		return ctx.newCoqCall(f.Name, args)
	case *ast.SelectorExpr:
		return ctx.selectorMethod(f, call)
	case *ast.ArrayType:
		// string -> []byte conversions are supported
		if f.Len == nil && isIdent(f.Elt, "byte") {
			arg := args[0]
			if !isString(ctx.typeOf(arg)) {
				ctx.unsupported(arg,
					"conversion from type %v to []byte", ctx.typeOf(arg))
				return coq.CallExpr{}
			}
			return ctx.newCoqCall("Data.stringToBytes", args)
		}
	default:
		ctx.unsupported(f, "call on this expression")
	}
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
	default:
		ctx.nope(typeArg, "make() of %s, not a map or array", typeArg)
	}
	return coq.CallExpr{}
}

// newExpr parses a call to new() into an appropriate allocation
func (ctx Ctx) newExpr(s ast.Node, ty ast.Expr) coq.CallExpr {
	if sel, ok := ty.(*ast.SelectorExpr); ok {
		if isIdent(sel.X, "sync") && isIdent(sel.Sel, "RWMutex") {
			return coq.NewCallExpr("Data.newLock")
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
	if info, ok := getStructInfo(ctx.typeOf(ty)); ok && !info.throughPointer {
		return coq.NewCallExpr("struct.alloc", coq.StructDesc(info.name), e)
	}
	return coq.NewCallExpr("ref", e)
}

type intTypeInfo struct {
	width     int
	isUntyped bool
}

func (info intTypeInfo) isUint64() bool {
	return info.width == 64 || info.isUntyped
}

func (info intTypeInfo) isUint32() bool {
	return info.width == 32 || info.isUntyped
}

func (info intTypeInfo) isUint8() bool {
	return info.width == 8 || info.isUntyped
}

func getIntegerType(t types.Type) (intTypeInfo, bool) {
	basicTy, ok := t.Underlying().(*types.Basic)
	if !ok {
		return intTypeInfo{}, false
	}
	switch basicTy.Kind() {
	// conversion from uint64 -> uint64 is possible if the conversion
	// causes an untyped literal to become a uint64
	case types.Uint, types.Int, types.Uint64:
		return intTypeInfo{width: 64}, true
	case types.UntypedInt:
		return intTypeInfo{isUntyped: true}, true
	case types.Uint32:
		return intTypeInfo{width: 32}, true
	case types.Uint8:
		return intTypeInfo{width: 8}, true
	default:
		return intTypeInfo{}, false
	}
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
		if s.Ellipsis == token.NoPos {
			return coq.NewCallExpr("SliceAppend", ctx.expr(s.Args[0]), ctx.expr(s.Args[1]))
		}
		// append(s1, s2...)
		return coq.NewCallExpr("SliceAppendSlice",
			ctx.expr(s.Args[0]),
			ctx.expr(s.Args[1]))
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
	return ctx.methodExpr(s)
}

type structTypeInfo struct {
	name           string
	throughPointer bool
}

func getStructInfo(t types.Type) (structTypeInfo, bool) {
	throughPointer := false
	if pt, ok := t.(*types.Pointer); ok {
		throughPointer = true
		t = pt.Elem()
	}
	if t, ok := t.(*types.Named); ok {
		if _, ok := t.Underlying().(*types.Struct); ok {
			return structTypeInfo{
				name:           t.Obj().Name(),
				throughPointer: throughPointer,
			}, true
		}
	}
	return structTypeInfo{}, false
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
		ctx.unsupported(e, "package select")
		return nil
	}
	structInfo, ok := getStructInfo(selectorType)
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

func structTypeFields(ty *types.Struct) []string {
	var fields []string
	for i := 0; i < ty.NumFields(); i++ {
		fields = append(fields, ty.Field(i).Name())
	}
	return fields
}

func (ctx Ctx) structLiteral(e *ast.CompositeLit) coq.StructLiteral {
	structType, ok := ctx.typeOf(e).Underlying().(*types.Struct)
	if !ok {
		ctx.unsupported(e, "non-struct literal")
	}
	structName, ok := getIdent(e.Type)
	if !ok {
		ctx.nope(e.Type, "non-struct literal after type check")
	}
	lit := coq.NewStructLiteral(structName)
	foundFields := make(map[string]bool)
	for _, el := range e.Elts {
		switch el := el.(type) {
		case *ast.KeyValueExpr:
			ident, ok := getIdent(el.Key)
			if !ok {
				ctx.noExample(el.Key, "struct field keyed by non-identifier %+v", el.Key)
				return coq.StructLiteral{}
			}
			lit.AddField(ident, ctx.expr(el.Value))
			foundFields[ident] = true
		default:
			// shouldn't be possible given type checking above
			ctx.nope(el, "literal component in struct")
		}
	}
	for _, f := range structTypeFields(structType) {
		if !foundFields[f] {
			ctx.unsupported(e, "incomplete struct literal")
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
		if !ok || n < 0 {
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

func (ctx Ctx) binExpr(e *ast.BinaryExpr) coq.Expr {
	op, ok := map[token.Token]coq.BinOp{
		token.LSS:  coq.OpLessThan,
		token.GTR:  coq.OpGreaterThan,
		token.SUB:  coq.OpMinus,
		token.EQL:  coq.OpEquals,
		token.MUL:  coq.OpMul,
		token.QUO:  coq.OpQuot,
		token.REM:  coq.OpRem,
		token.LEQ:  coq.OpLessEq,
		token.GEQ:  coq.OpGreaterEq,
		token.AND:  coq.OpAnd,
		token.LAND: coq.OpAnd,
		token.OR:   coq.OpOr,
		token.LOR:  coq.OpOr,
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
		return coq.BinaryExpr{X: ctx.expr(e.X), Op: op, Y: ctx.expr(e.Y)}
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
			x, ctx.expr(e.Low))
	}
	if e.Low == nil && e.High != nil {
		return coq.NewCallExpr("SliceTake",
			x, ctx.expr(e.High))
	}
	if e.Low != nil && e.High != nil {
		return coq.NewCallExpr("SliceSubslice",
			x, ctx.expr(e.Low), ctx.expr(e.High))
	}
	if e.Low == nil && e.High == nil {
		ctx.unsupported(e, "complete slice doesn't do anything")
	}
	return nil
}

func (ctx Ctx) nilExpr(e *ast.Ident) coq.Expr {
	return coq.GallinaIdent("slice.nil")
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
		if _, ok := ctx.typeOf(e.X).Underlying().(*types.Struct); ok {
			structLit, ok := e.X.(*ast.CompositeLit)
			if !ok {
				ctx.unsupported(e,
					"'&' on a struct can only be for literals")
			}
			sl := ctx.structLiteral(structLit)
			sl.Allocation = true
			return sl
		}
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
		// TODO: check if this should be a struct load
		return coq.DerefExpr{e}
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

func (ctx Ctx) indexExpr(e *ast.IndexExpr) coq.CallExpr {
	xTy := ctx.typeOf(e.X)
	switch xTy.(type) {
	case *types.Map:
		return coq.NewCallExpr("MapGet",
			ctx.expr(e.X), ctx.expr(e.Index))
	case *types.Slice:
		return coq.NewCallExpr("SliceGet",
			ctx.expr(e.X), ctx.expr(e.Index))
	}
	ctx.unsupported(e, "index into unknown type %v", xTy)
	return coq.CallExpr{}
}

func (ctx Ctx) derefExpr(e ast.Expr) coq.Expr {
	info, ok := getStructInfo(ctx.typeOf(e))
	if ok && info.throughPointer {
		return coq.NewCallExpr("struct.load",
			coq.StructDesc(info.name),
			ctx.expr(e))
	}
	return coq.DerefExpr{ctx.expr(e)}
}

func (ctx Ctx) expr(e ast.Expr) coq.Expr {
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
		return ctx.structLiteral(e)
	case *ast.BasicLit:
		return ctx.basicLiteral(e)
	case *ast.BinaryExpr:
		return ctx.binExpr(e)
	case *ast.SliceExpr:
		return ctx.sliceExpr(e)
	case *ast.IndexExpr:
		return ctx.indexExpr(e)
	case *ast.UnaryExpr:
		return ctx.unaryExpr(e)
	case *ast.ParenExpr:
		return ctx.expr(e.X)
	case *ast.StarExpr:
		return ctx.derefExpr(e.X)
	default:
		ctx.unsupported(e, "unexpected expr")
	}
	return nil
}

func (ctx Ctx) blockStmt(s *ast.BlockStmt, loopVar *string) coq.BlockExpr {
	return ctx.stmts(s.List, loopVar)
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

func endsWithReturn(b *ast.BlockStmt) bool {
	// TODO: should also catch implicit continue
	switch b.List[len(b.List)-1].(type) {
	case *ast.ReturnStmt, *ast.BranchStmt:
		return true
	}
	return false
}

func (ctx Ctx) stmts(ss []ast.Stmt, loopVar *string) coq.BlockExpr {
	c := &cursor{ss}
	var bindings []coq.Binding
	for c.HasNext() {
		bindings = append(bindings, ctx.stmt(c.Next(), c, loopVar))
	}
	if len(bindings) == 0 {
		retExpr := coq.ReturnExpr{coq.Tt}
		return coq.BlockExpr{[]coq.Binding{coq.NewAnon(retExpr)}}
	}
	return coq.BlockExpr{bindings}
}

func (ctx Ctx) ifStmt(s *ast.IfStmt, c *cursor, loopVar *string) coq.Binding {
	// TODO: be more careful about nested if statements; if the then branch has
	//  an if statement with early return, this is probably not handled correctly.
	//  We should conservatively disallow such returns until they're properly analyzed.
	if s.Init != nil {
		ctx.unsupported(s.Init, "if statement initializations")
		return coq.Binding{}
	}
	thenExpr, ok := ctx.stmt(s.Body, &cursor{nil}, loopVar).Unwrap()
	if !ok {
		ctx.nope(s.Body, "if statement body ends with an assignment")
		return coq.Binding{}
	}
	ife := coq.IfExpr{
		Cond: ctx.expr(s.Cond),
		Then: thenExpr,
	}

	// supported use cases
	// (1) early return, no else branch; remainder of function is lifted to else
	// (2) both branches and no remainder
	//
	// If the else branch also doesn't return it's not a problem to handle subsequent code,
	// but that's annoying and we can leave it for later. Maybe the special case
	// of Else == nil should be supported, though.

	remaining := c.HasNext()
	bodyEndsWithReturn := endsWithReturn(s.Body)
	if bodyEndsWithReturn && remaining {
		if s.Else != nil {
			ctx.futureWork(s.Else, "else with early return")
			return coq.Binding{}
		}
		ife.Else = ctx.stmts(c.Remainder(), loopVar)
		return coq.NewAnon(ife)
	}
	if !bodyEndsWithReturn && remaining && s.Else == nil {
		// conditional statement in the middle of a block
		retUnit := coq.ReturnExpr{coq.Tt}
		ife.Then = coq.BlockExpr{[]coq.Binding{
			coq.NewAnon(ife.Then),
			coq.NewAnon(retUnit),
		}}
		ife.Else = retUnit
		return coq.NewAnon(ife)
	}
	if !remaining {
		if s.Else == nil {
			ife.Else = coq.ReturnExpr{coq.Tt}
			return coq.NewAnon(ife)
		}
		elseExpr, ok := ctx.stmt(s.Else, c, loopVar).Unwrap()
		if !ok {
			ctx.nope(s.Else, "if statement else ends with an assignment")
			return coq.Binding{}
		}
		ife.Else = elseExpr
		return coq.NewAnon(ife)
	}
	// there are some other cases that can be handled but it's a bit tricky
	ctx.futureWork(s, "non-terminal if expressions are only partially supported")
	return coq.Binding{}
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
	loopVar := new(string)
	if s.Init != nil {
		ident, _ = ctx.loopVar(s.Init)
		ctx.addDef(ident, identInfo{
			IsPtrWrapped: true,
		})
		init = ctx.stmt(s.Init, &cursor{nil}, nil)
		loopVar = &ident.Name
	}
	var cond coq.Expr = coq.True
	if s.Cond != nil {
		cond = ctx.expr(s.Cond)
	}
	var post coq.Expr = coq.Skip
	if s.Post != nil {
		postBlock := ctx.stmt(s.Post, &cursor{nil}, loopVar)
		if len(postBlock.Names) > 0 {
			ctx.unsupported(s.Post, "post cannot bind names")
		}
		post = postBlock.Expr
	}

	hasExplicitBranch := endsWithReturn(s.Body)
	c := &cursor{s.Body.List}
	var bindings []coq.Binding
	for c.HasNext() {
		bindings = append(bindings, ctx.stmt(c.Next(), c, loopVar))
	}
	if !hasExplicitBranch {
		bindings = append(bindings, coq.NewAnon(coq.LoopContinue))
	}
	body := coq.BlockExpr{bindings}
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
		Body:       ctx.blockStmt(s.Body, nil),
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
	var loopVar *string
	key := getIdentOrNil(s.Key)
	val := getIdentOrNil(s.Value)
	if key != nil {
		ctx.addDef(key, identInfo{
			IsPtrWrapped: false,
			IsMacro:      false,
		})
		loopVar = &key.Name
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
		Body:  ctx.blockStmt(s.Body, loopVar),
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
	// TODO: this may need some type info to handle struct allocation
	return coq.RefExpr{X: ctx.expr(rhs)}
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
		return coq.Binding{Names: names, Expr: ctx.expr(rhs)}
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
	return ctx.varSpec(decl.Specs[0].(*ast.ValueSpec))
}

func pointerAssign(dst *ast.Ident, x coq.Expr) coq.Binding {
	return coq.NewAnon(coq.StoreStmt{Dst: coq.IdentExpr(dst.Name), X: x})
}

func (ctx Ctx) assignStmt(s *ast.AssignStmt, c *cursor, loopVar *string) coq.Binding {
	if s.Tok == token.DEFINE {
		return ctx.defineStmt(s)
	}
	if s.Tok != token.ASSIGN {
		ctx.unsupported(s, "%v assignment", s.Tok)
	}
	if len(s.Lhs) > 1 || len(s.Rhs) > 1 {
		ctx.unsupported(s, "multiple assignment")
	}
	rhs := s.Rhs[0]
	// assignments can mean various things
	switch lhs := s.Lhs[0].(type) {
	case *ast.Ident:
		if ctx.identInfo(lhs).IsPtrWrapped {
			return pointerAssign(lhs, ctx.expr(rhs))
		}
		// the support for making variables assignable is in flux, but currently
		// the only way the assignment would be supported is if it was created
		// in a loop initializer
		ctx.unsupported(s, "variable %s is not assignable", lhs.Name)
	case *ast.IndexExpr:
		targetTy := ctx.typeOf(lhs.X)
		switch targetTy.(type) {
		case *types.Slice:
			value := ctx.expr(s.Rhs[0])
			return coq.NewAnon(coq.NewCallExpr(
				"SliceSet",
				ctx.expr(lhs.X),
				ctx.expr(lhs.Index),
				value))
		case *types.Map:
			value := ctx.expr(s.Rhs[0])
			return coq.NewAnon(coq.NewCallExpr(
				"MapInsert",
				ctx.expr(lhs.X),
				ctx.expr(lhs.Index),
				value))
		default:
			ctx.unsupported(s, "index update to unexpected target of type %v", targetTy)
		}
	case *ast.StarExpr:
		info, ok := getStructInfo(ctx.typeOf(lhs.X))
		if ok && info.throughPointer {
			return coq.NewAnon(coq.NewCallExpr("struct.store",
				coq.StructDesc(info.name),
				ctx.expr(lhs.X),
				ctx.expr(s.Rhs[0])))
		}
		return coq.NewAnon(coq.StoreStmt{
			Dst: ctx.expr(lhs.X),
			X:   ctx.expr(s.Rhs[0]),
		})
	case *ast.SelectorExpr:
		ty := ctx.typeOf(lhs.X)
		if ty, ok := ty.(*types.Pointer); ok {
			info, ok := getStructInfo(ty.Elem())
			if ok {
				fieldName := lhs.Sel.Name
				return coq.NewAnon(coq.NewCallExpr("struct.storeF",
					coq.StructDesc(info.name),
					coq.GallinaString(fieldName),
					ctx.expr(lhs.X),
					ctx.expr(rhs)))
			}
		}
		ctx.unsupported(s,
			"assigning to field of non-struct pointer type %v", ty)
	default:
		ctx.unsupported(s, "assigning to complex expression")
	}
	return coq.Binding{}
}

func (ctx Ctx) incDecStmt(stmt *ast.IncDecStmt, c *cursor, loopVar *string) coq.Binding {
	if loopVar == nil || !isIdent(stmt.X, *loopVar) {
		ctx.todo(stmt, "cannot inc/dec non-loop var")
		return coq.Binding{}
	}
	op := coq.OpPlus
	if stmt.Tok == token.DEC {
		op = coq.OpMinus
	}
	return pointerAssign(stmt.X.(*ast.Ident), coq.BinaryExpr{
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
	return coq.SpawnExpr{Body: ctx.blockStmt(f.Body, nil)}
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

// getSpawn returns a non-nil spawned thread if the expression is a call to
// machine.Spawn()
func getSpawn(e *ast.ExprStmt) ast.Expr {
	callExpr, ok := e.X.(*ast.CallExpr)
	if !ok {
		return nil
	}
	method, ok := callExpr.Fun.(*ast.SelectorExpr)
	if !ok {
		return nil
	}
	if isIdent(method.X, "machine") &&
		isIdent(method.Sel, "Spawn") {
		return callExpr.Args[0]
	}
	return nil
}

func (ctx Ctx) stmt(s ast.Stmt, c *cursor, loopVar *string) coq.Binding {
	switch s := s.(type) {
	case *ast.ReturnStmt:
		if c.HasNext() {
			ctx.unsupported(c.Next(), "statement following return")
			return coq.Binding{}
		}
		if loopVar != nil {
			ctx.futureWork(s, "return in loop (use break)")
			return coq.Binding{}
		}
		return coq.NewAnon(ctx.returnExpr(s.Results))
	case *ast.BranchStmt:
		if loopVar == nil {
			ctx.unsupported(s, "branching outside of a loop")
		}
		return coq.NewAnon(ctx.branchStmt(s))
	case *ast.ExprStmt:
		if thread := getSpawn(s); thread != nil {
			return coq.NewAnon(ctx.spawnExpr(thread))
		}
		return coq.NewAnon(ctx.expr(s.X))
	case *ast.AssignStmt:
		return ctx.assignStmt(s, c, loopVar)
	case *ast.DeclStmt:
		return ctx.varDeclStmt(s)
	case *ast.IncDecStmt:
		return ctx.incDecStmt(s, c, loopVar)
	case *ast.BlockStmt:
		return coq.NewAnon(ctx.blockStmt(s, loopVar))
	case *ast.IfStmt:
		return ctx.ifStmt(s, c, loopVar)
	case *ast.ForStmt:
		// note that this might be a nested loop,
		// in which case the loop var gets replaced by the inner loop.
		return coq.NewAnon(ctx.forStmt(s))
	case *ast.RangeStmt:
		return coq.NewAnon(ctx.rangeStmt(s))
	case *ast.GoStmt:
		ctx.unsupported(s, "threads must be spawned with machine.Spawn")
		return coq.Binding{}
	default:
		ctx.unsupported(s, "statement")
	}
	return coq.Binding{}
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

		structInfo, ok := getStructInfo(recvType)
		if !ok {
			ctx.unsupported(d.Recv, "receiver does not appear to be a struct")
		}
		fd.Name = coq.StructMethod(structInfo.name, d.Name.Name)
		fd.Args = append(fd.Args, ctx.field(receiver))
	}
	fd.Args = append(fd.Args, ctx.paramList(d.Type.Params)...)
	fd.ReturnType = ctx.returnType(d.Type.Results)
	fd.Body = ctx.blockStmt(d.Body, nil)
	return fd
}

func (ctx Ctx) constDecl(d *ast.GenDecl) coq.ConstDecl {
	spec := d.Specs[0].(*ast.ValueSpec)
	if len(d.Specs) > 1 || len(spec.Names) > 1 {
		ctx.unsupported(d, "multiple const declarations")
		return coq.ConstDecl{}
	}
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

func (ctx Ctx) checkGlobalVar(d *ast.ValueSpec) {
	ctx.futureWork(d, "global variables (might be used for objects)")
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

var okImports = map[string]bool{
	"github.com/tchajed/goose/machine":         true,
	"github.com/tchajed/goose/machine/disk":    true,
	"github.com/tchajed/goose/machine/filesys": true,
	"github.com/tchajed/mailboat/globals":      true,
	"sync":                                     true,
	"log":                                      true,
}

func (ctx Ctx) checkImports(d []ast.Spec) {
	for _, s := range d {
		s := s.(*ast.ImportSpec)
		importPath := stringLitValue(s.Path)
		if !okImports[importPath] {
			ctx.unsupported(s, "non-whitelisted import")
		}
		if s.Name != nil {
			ctx.unsupported(s, "renaming imports")
		}
	}
}

func (ctx Ctx) maybeDecl(d ast.Decl) coq.Decl {
	switch d := d.(type) {
	case *ast.FuncDecl:
		fd := ctx.funcDecl(d)
		return fd
	case *ast.GenDecl:
		switch d.Tok {
		case token.IMPORT:
			ctx.checkImports(d.Specs)
			return nil
		case token.CONST:
			return ctx.constDecl(d)
		case token.VAR:
			if len(d.Specs) > 1 {
				ctx.unsupported(d, "multiple vars")
			}
			spec := d.Specs[0].(*ast.ValueSpec)
			ctx.checkGlobalVar(spec)
		case token.TYPE:
			if len(d.Specs) > 1 {
				ctx.noExample(d, "multiple specs in a type decl")
			}
			spec := d.Specs[0].(*ast.TypeSpec)
			ty := ctx.typeDecl(d.Doc, spec)
			return ty
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
