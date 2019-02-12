package goose

import (
	"fmt"
	"go/ast"
	"go/importer"
	"go/token"
	"go/types"
	"strconv"
	"strings"
	"unicode"

	"github.com/davecgh/go-spew/spew"

	"github.com/tchajed/goose/coq"
)

// Ctx is a context for resolving Go code's types and source code
type Ctx struct {
	info *types.Info
	fset *token.FileSet
	errorReporter
	Config
}

type Config struct {
	AddSourceFileComments bool
}

func NewCtx(fset *token.FileSet, config Config) Ctx {
	info := &types.Info{
		Defs:       make(map[*ast.Ident]types.Object),
		Uses:       make(map[*ast.Ident]types.Object),
		Types:      make(map[ast.Expr]types.TypeAndValue),
		Selections: make(map[*ast.SelectorExpr]*types.Selection),
	}
	return Ctx{
		info:          info,
		fset:          fset,
		errorReporter: newErrorReporter(fset),
		Config:        config,
	}
}

func (ctx Ctx) TypeCheck(pkgName string, files []*ast.File) error {
	conf := types.Config{Importer: importer.Default()}
	_, err := conf.Check(pkgName, ctx.fset, files, ctx.info)
	return err
}

func (ctx Ctx) Where(node ast.Node) string {
	return ctx.fset.Position(node.Pos()).String()
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
	default:
		ctx.Unsupported(k, "maps must be from uint64 (not %s)", spew.Sdump(k))
	}
	return coq.MapType{}
}

func (ctx Ctx) selectorExprType(e *ast.SelectorExpr) coq.TypeIdent {
	if isIdent(e.X, "filesys") && isIdent(e.Sel, "File") {
		return coq.TypeIdent("Fd")
	}
	ctx.Unsupported(e, "selector for unknown type %s", spew.Sdump(e))
	return coq.TypeIdent("<selector expr>")
}

func (ctx Ctx) coqTypeOfType(n ast.Node, t types.Type) coq.Type {
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
		case "string":
			return coq.TypeIdent("Path")
		case "uint64":
			return coq.TypeIdent("uint64")
		case "byte":
			return coq.TypeIdent("byte")
		default:
			ctx.Todo(n, "explicitly handle basic types")
		}
	}
	return coq.TypeIdent("<type>")
}

func (ctx Ctx) arrayType(e *ast.ArrayType) coq.Type {
	return coq.SliceType{ctx.coqType(e.Elt)}
}

func (ctx Ctx) coqType(e ast.Expr) coq.Type {
	switch e := e.(type) {
	case *ast.Ident:
		return ctx.coqTypeOfType(e, ctx.info.TypeOf(e))
	case *ast.MapType:
		return ctx.mapType(e)
	case *ast.SelectorExpr:
		return ctx.selectorExprType(e)
	case *ast.ArrayType:
		return ctx.arrayType(e)
	default:
		ctx.NoExample(e, "unexpected type expr %s", spew.Sdump(e))
	}
	return coq.TypeIdent("<type>")
}

func (ctx Ctx) fieldDecl(f *ast.Field) coq.FieldDecl {
	if len(f.Names) > 1 {
		ctx.FutureWork(f, "multiple fields for same type (split them up)")
	}
	return coq.FieldDecl{
		Name: f.Names[0].Name,
		Type: ctx.coqType(f.Type),
	}
}

func addSourceDoc(doc *ast.CommentGroup, comment *string) {
	if doc == nil {
		return
	}
	if *comment != "" {
		*comment += "\n\n"
	}
	*comment += stripTrailingNewline(doc.Text())
}

func (ctx Ctx) addSourceFile(node ast.Node, comment *string) {
	if !ctx.AddSourceFileComments {
		return
	}
	if *comment != "" {
		*comment += "\n\n   "
	}
	*comment += fmt.Sprintf("go: %s", ctx.Where(node))
}

func (ctx Ctx) typeDecl(doc *ast.CommentGroup, spec *ast.TypeSpec) coq.StructDecl {
	structTy, ok := spec.Type.(*ast.StructType)
	if !ok {
		ctx.Unsupported(spec, "non-struct type %s", spew.Sdump(spec))
		return coq.StructDecl{}
	}
	ty := coq.StructDecl{
		Name: spec.Name.Name,
	}
	addSourceDoc(doc, &ty.Comment)
	ctx.addSourceFile(spec, &ty.Comment)
	for _, f := range structTy.Fields.List {
		ty.Fields = append(ty.Fields, ctx.fieldDecl(f))
	}
	return ty
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

func (ctx Ctx) methodExpr(f ast.Expr) string {
	switch f := f.(type) {
	case *ast.Ident:
		if f.Name == "len" {
			return "slice.length"
		}
		return f.Name
	case *ast.SelectorExpr:
		if isIdent(f.X, "fs") {
			return "FS." + toInitialLower(f.Sel.Name)
		}
		if isIdent(f.X, "machine") {
			switch f.Sel.Name {
			case "UInt64Get":
				return "uint64_from_le"
			case "UInt64Encode":
				return "uint64_to_le"
			}
		}
		ctx.Unsupported(f, "cannot call methods selected from %s", spew.Sdump(f.X))
		return "<selector>"
	default:
		ctx.Unsupported(f, "call on expression %s", spew.Sdump(f))
	}
	return "<fun expr>"
}

// makeExpr parses a call to make() into the appropriate data-structure Call
func (ctx Ctx) makeExpr(args []ast.Expr) coq.CallExpr {
	switch typeArg := args[0].(type) {
	case *ast.MapType:
		mapTy := ctx.mapType(typeArg)
		return coq.NewCallExpr("Data.newHashTable", mapTy.Value)
	case *ast.ArrayType:
		if typeArg.Len != nil {
			ctx.Nope(typeArg, "can't make() arrays (only slices)")
		}
		ctx.Todo(typeArg, "array types are not really implemented")
		// TODO: need to check that slice is being initialized to an empty one
		elt := ctx.coqType(typeArg.Elt)
		return coq.NewCallExpr("Data.newArray", elt)
	default:
		ctx.Nope(typeArg, "make() of %s, not a map or array", typeArg)
	}
	return coq.CallExpr{}
}

func (ctx Ctx) callExpr(s *ast.CallExpr) coq.CallExpr {
	call := coq.CallExpr{}
	if isIdent(s.Fun, "make") {
		return ctx.makeExpr(s.Args)
	}
	call.MethodName = ctx.methodExpr(s.Fun)
	for _, arg := range s.Args {
		call.Args = append(call.Args, ctx.expr(arg))
	}
	return call
}

func (ctx Ctx) structSelector(e *ast.SelectorExpr) coq.ProjExpr {
	structType := ctx.info.Selections[e].Recv().(*types.Named)
	proj := fmt.Sprintf("%s.%s", structType.Obj().Name(), e.Sel.Name)
	return coq.ProjExpr{Projection: proj, Arg: ctx.expr(e.X)}
}

func structTypeFields(ty *types.Struct) []string {
	var fields []string
	for i := 0; i < ty.NumFields(); i++ {
		fields = append(fields, ty.Field(i).Name())
	}
	return fields
}

func (ctx Ctx) structLiteral(e *ast.CompositeLit) coq.StructLiteral {
	structType, ok := ctx.info.TypeOf(e).Underlying().(*types.Struct)
	if !ok {
		ctx.Unsupported(e, "non-struct literal %s", spew.Sdump(e))
	}
	structName, ok := getIdent(e.Type)
	if !ok {
		ctx.Nope(e.Type, "non-struct literal after type check")
	}
	lit := coq.StructLiteral{StructName: structName}
	foundFields := make(map[string]bool)
	for _, el := range e.Elts {
		switch el := el.(type) {
		case *ast.KeyValueExpr:
			ident, ok := getIdent(el.Key)
			if !ok {
				ctx.NoExample(el.Key, "struct field keyed by non-identifier %+v", el.Key)
				return coq.StructLiteral{}
			}
			lit.Elts = append(lit.Elts, coq.FieldVal{
				Field: ident,
				Value: ctx.expr(el.Value),
			})
			foundFields[ident] = true
		default:
			// shouldn't be possible given type checking above
			ctx.Nope(el, "literal component in struct %s", spew.Sdump(e))
		}
	}
	for _, f := range structTypeFields(structType) {
		if !foundFields[f] {
			ctx.Unsupported(e, "incomplete struct literal %s", spew.Sdump(e))
		}
	}
	return lit
}

// basicLiteral parses a basic literal; only Go int literals are supported
func (ctx Ctx) basicLiteral(e *ast.BasicLit) coq.IntLiteral {
	if e.Kind != token.INT {
		ctx.Unsupported(e, "non-integer literals are not supported")
		return coq.IntLiteral{^uint64(0)}
	}
	n, err := strconv.ParseUint(e.Value, 10, 64)
	if err != nil {
		panic(err) // could not parse integer literal?
	}
	return coq.IntLiteral{n}
}

func (ctx Ctx) binExpr(e *ast.BinaryExpr) coq.Expr {
	be := coq.BinaryExpr{X: ctx.expr(e.X), Y: ctx.expr(e.Y)}
	switch e.Op {
	case token.LSS:
		be.Op = coq.OpLessThan
	case token.ADD:
		be.Op = coq.OpPlus
	case token.SUB:
		be.Op = coq.OpMinus
	case token.EQL:
		be.Op = coq.OpEquals
	default:
		ctx.Unsupported(e, "binary operator")
	}
	return be
}

func (ctx Ctx) sliceExpr(e *ast.SliceExpr) coq.Expr {
	ctx.Todo(e, "slice expressions")
	return nil
}

func (ctx Ctx) expr(e ast.Expr) coq.Expr {
	switch e := e.(type) {
	case *ast.CallExpr:
		return ctx.callExpr(e)
	case *ast.MapType:
		return ctx.mapType(e)
	case *ast.Ident:
		return coq.IdentExpr(e.Name)
	case *ast.SelectorExpr:
		return ctx.structSelector(e)
	case *ast.CompositeLit:
		return ctx.structLiteral(e)
	case *ast.BasicLit:
		return ctx.basicLiteral(e)
	case *ast.BinaryExpr:
		return ctx.binExpr(e)
	case *ast.SliceExpr:
		return ctx.sliceExpr(e)
	case *ast.IndexExpr:
		ctx.Todo(e, "map/slice indexing")
	default:
		ctx.NoExample(e, "expr %s", spew.Sdump(e))
	}
	return nil
}

func (ctx Ctx) blockStmt(s *ast.BlockStmt) coq.BlockExpr {
	var bindings []coq.Binding
	for _, s := range s.List {
		bindings = append(bindings, ctx.stmt(s))
	}
	return coq.BlockExpr{bindings}
}

func (ctx Ctx) stmt(s ast.Stmt) coq.Binding {
	switch s := s.(type) {
	case *ast.ReturnStmt:
		return coq.NewAnon(ctx.returnExpr(s.Results))
	case *ast.ExprStmt:
		return coq.NewAnon(ctx.expr(s.X))
	case *ast.AssignStmt:
		if len(s.Rhs) > 1 {
			ctx.Unsupported(s, "multiple RHS assignment (split them up)")
		}
		lhs, rhs := s.Lhs, s.Rhs[0]
		if s.Tok != token.DEFINE {
			// NOTE: Do we need these? Should they become bindings anyway, or perhaps we should support let bindings?
			ctx.FutureWork(s, "re-assignments are not supported (only definitions")
		}
		var names []string
		for _, lhsExpr := range lhs {
			ident, ok := getIdent(lhsExpr)
			if !ok {
				ctx.Nope(lhsExpr, "defining a non-identifier")
			}
			names = append(names, ident)
		}
		return coq.Binding{Names: names, Expr: ctx.expr(rhs)}
	case *ast.IfStmt:
		thenExpr, ok := ctx.stmt(s.Body).Unwrap()
		if !ok {
			ctx.Nope(s.Body, "if statement body ends with an assignment")
			return coq.Binding{}
		}
		ife := coq.IfExpr{
			Cond: ctx.expr(s.Cond),
			Then: thenExpr,
		}
		if s.Else == nil {
			ife.Else = coq.ReturnExpr{coq.IdentExpr("tt")}
		} else {
			elseExpr, ok := ctx.stmt(s.Else).Unwrap()
			if !ok {
				ctx.Nope(s.Else, "if statement else ends with an assignment")
				return coq.Binding{}
			}
			ife.Else = elseExpr
		}
		return coq.NewAnon(ife)
	case *ast.ForStmt:
		ctx.Todo(s, "for statements")
	case *ast.BlockStmt:
		return coq.NewAnon(ctx.blockStmt(s))
	case *ast.GoStmt:
		ctx.Todo(s, "go func(){ ... } statements")
	default:
		ctx.NoExample(s, "unexpected statement %s", spew.Sdump(s))
	}
	return coq.Binding{}
}

func (ctx Ctx) returnExpr(es []ast.Expr) coq.Expr {
	var exprs coq.TupleExpr
	for _, r := range es {
		exprs = append(exprs, ctx.expr(r))
	}
	return coq.ReturnExpr{coq.NewTuple(exprs)}
}

func (ctx Ctx) returnType(results *ast.FieldList) coq.Type {
	if results == nil {
		return coq.TypeIdent("unit")
	}
	rs := results.List
	for _, r := range rs {
		if len(r.Names) > 0 {
			ctx.Unsupported(r, "named returned value")
			return coq.TypeIdent("<invalid>")
		}
	}
	var ts []coq.Type
	for _, r := range rs {
		if len(r.Names) > 0 {
			ctx.Unsupported(r, "named returned value")
			return coq.TypeIdent("<invalid>")
		}
		ts = append(ts, ctx.coqType(r.Type))
	}
	return coq.NewTupleType(ts)
}

func stripTrailingNewline(text string) string {
	if text == "" {
		return text
	}
	if text[len(text)-1] == '\n' {
		return text[:len(text)-1]
	}
	return text
}

func (ctx Ctx) funcDecl(d *ast.FuncDecl) coq.FuncDecl {
	fd := coq.FuncDecl{Name: d.Name.Name}
	addSourceDoc(d.Doc, &fd.Comment)
	ctx.addSourceFile(d, &fd.Comment)
	if d.Recv != nil {
		ctx.FutureWork(d.Recv, "methods need to be lifted by moving the receiver to the arg list")
	}
	for _, p := range d.Type.Params.List {
		fd.Args = append(fd.Args, ctx.fieldDecl(p))
	}
	fd.ReturnType = ctx.returnType(d.Type.Results)
	fd.Body = ctx.blockStmt(d.Body)
	return fd
}

func (ctx Ctx) checkFilesysVar(d *ast.ValueSpec) {
	if !isIdent(d.Names[0], "fs") {
		ctx.Unsupported(d, "non-fs global variable")
	}
	ty, ok := d.Type.(*ast.SelectorExpr)
	if !ok {
		ctx.Unsupported(ty, "wrong type for fs")
	}
	if !(isIdent(ty.X, "filesys") &&
		isIdent(ty.Sel, "Filesys")) {
		ctx.Unsupported(ty, "wrong type for fs")
	}
	if len(d.Names) > 1 {
		ctx.Unsupported(d, "multiple fs variables")
	}
}

func stringBasicLit(lit *ast.BasicLit) string {
	if lit.Kind != token.STRING {
		panic("unexpected non-string literal")
	}
	s := lit.Value
	return s[1 : len(s)-1]
}

func (ctx Ctx) checkImports(d []ast.Spec) {
	for _, s := range d {
		s := s.(*ast.ImportSpec)
		importPath := stringBasicLit(s.Path)
		if !strings.HasPrefix(importPath, "github.com/tchajed/goose/machine") {
			ctx.Unsupported(s, "non-whitelisted import")
		}
		if s.Name != nil {
			ctx.Unsupported(s, "renaming imports")
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
			ctx.Todo(d, "global constants")
		case token.VAR:
			if len(d.Specs) > 1 {
				ctx.Unsupported(d, "multiple vars")
			}
			spec := d.Specs[0].(*ast.ValueSpec)
			ctx.checkFilesysVar(spec)
		case token.TYPE:
			if len(d.Specs) > 1 {
				ctx.NoExample(d, "multiple specs in a type decl")
			}
			spec := d.Specs[0].(*ast.TypeSpec)
			ty := ctx.typeDecl(d.Doc, spec)
			return ty
		default:
			ctx.Nope(d, "unknown GenDecl token type for %s", spew.Sdump(d))
		}
	case *ast.BadDecl:
		ctx.Nope(d, "bad declaration in type-checked code")
	default:
		ctx.Nope(d, "top-level decl %s")
	}
	return nil
}

func (ctx Ctx) FileDecls(f *ast.File) []coq.Decl {
	var decls []coq.Decl
	for _, d := range f.Decls {
		if d := ctx.maybeDecl(d); d != nil {
			decls = append(decls, d)
		}
	}
	return decls
}
