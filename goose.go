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

	"github.com/tchajed/goose/coq"
)

// Ctx is a context for resolving Go code's types and source code
type Ctx struct {
	info *types.Info
	fset *token.FileSet
	errorReporter
	Config
}

// Config holds global configuration for Coq conversion
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

// TypeCheck type-checks a set of files and stores the result in the Ctx
//
// This is needed before conversion to Coq to disambiguate some methods.
func (ctx Ctx) TypeCheck(pkgName string, files []*ast.File) error {
	conf := types.Config{Importer: importer.Default()}
	_, err := conf.Check(pkgName, ctx.fset, files, ctx.info)
	return err
}

func (ctx Ctx) where(node ast.Node) string {
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
		ctx.Unsupported(k, "maps must be from uint64 (not %v)", k)
	}
	return coq.MapType{}
}

func (ctx Ctx) selectorExprType(e *ast.SelectorExpr) coq.TypeIdent {
	if isIdent(e.X, "filesys") && isIdent(e.Sel, "File") {
		return coq.TypeIdent("Fd")
	}
	ctx.Unsupported(e, "selector for unknown type %s", e)
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
		ctx.Unsupported(e, "unexpected type expr")
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
	*comment += fmt.Sprintf("go: %s", ctx.where(node))
}

func (ctx Ctx) typeDecl(doc *ast.CommentGroup, spec *ast.TypeSpec) coq.StructDecl {
	structTy, ok := spec.Type.(*ast.StructType)
	if !ok {
		ctx.Unsupported(spec, "non-struct type")
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

func (ctx Ctx) lenExpr(e *ast.CallExpr) coq.PureCall {
	x := e.Args[0]
	xTy := ctx.info.TypeOf(x)
	if _, ok := xTy.(*types.Slice); !ok {
		ctx.Unsupported(e, "length of object of type %v", xTy)
		return coq.PureCall(coq.CallExpr{})
	}
	return coq.PureCall(coq.NewCallExpr("slice.length",
		ctx.expr(x),
	))
}

func (ctx Ctx) methodExpr(f ast.Expr) string {
	switch f := f.(type) {
	case *ast.Ident:
		return f.Name
	case *ast.SelectorExpr:
		if isIdent(f.X, "fs") {
			switch f.Sel.Name {
			case "ReadAt":
				return "Base.sliceReadAt"
			case "Append":
				return "Base.sliceAppend"
			}
			return "FS." + toInitialLower(f.Sel.Name)
		}
		if isIdent(f.X, "machine") {
			switch f.Sel.Name {
			case "UInt64Get":
				return "Data.uint64Get"
			case "UInt64Encode":
				return "Data.uint64Put"
			}
		}
		ctx.Unsupported(f, "cannot call methods selected from %s", f.X)
		return "<selector>"
	default:
		ctx.Unsupported(f, "call on expression")
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

// basicallyUInt64 returns true conservatively when an
// expression can be treated as a uint64
func (ctx Ctx) basicallyUInt64(e ast.Expr) bool {
	basicTy, ok := ctx.info.TypeOf(e).(*types.Basic)
	if !ok {
		return false
	}
	switch basicTy.Kind() {
	// conversion from uint64 -> uint64 is possible if the conversion
	// causes an untyped literal to become a uint64
	case types.Int, types.Uint64:
		return true
	}
	return false
}

func (ctx Ctx) callExpr(s *ast.CallExpr) coq.Expr {
	call := coq.CallExpr{}
	if isIdent(s.Fun, "make") {
		return ctx.makeExpr(s.Args)
	}
	if isIdent(s.Fun, "len") {
		return ctx.lenExpr(s)
	}
	if isIdent(s.Fun, "append") {
		if s.Ellipsis == token.NoPos {
			return coq.NewCallExpr("Data.sliceAppend", ctx.expr(s.Args[0]), ctx.expr(s.Args[1]))
		}
		// append(s1, s2...)
		return coq.NewCallExpr("Data.sliceAppendSlice", ctx.expr(s.Args[0]), ctx.expr(s.Args[1]))
	}
	if isIdent(s.Fun, "uint64") {
		x := s.Args[0]
		if ctx.basicallyUInt64(x) {
			return ctx.expr(x)
		}
		ctx.Unsupported(s, "casts from non-int type %v to uint64", ctx.info.TypeOf(x))
		return nil
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
		ctx.Unsupported(e, "non-struct literal")
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
			ctx.Nope(el, "literal component in struct")
		}
	}
	for _, f := range structTypeFields(structType) {
		if !foundFields[f] {
			ctx.Unsupported(e, "incomplete struct literal")
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
	case token.GTR:
		be.Op = coq.OpGreaterThan
	case token.ADD:
		be.Op = coq.OpPlus
	case token.SUB:
		be.Op = coq.OpMinus
	case token.EQL:
		be.Op = coq.OpEquals
	default:
		ctx.Unsupported(e, "binary operator %v", e.Op)
	}
	return be
}

func (ctx Ctx) sliceExpr(e *ast.SliceExpr) coq.Expr {
	if e.Slice3 {
		ctx.Unsupported(e, "3-index slice")
		return nil
	}
	x := ctx.expr(e.X)
	if e.Low != nil && e.High == nil {
		return coq.PureCall(coq.NewCallExpr("slice.skip",
			ctx.expr(e.Low), x))
	}
	if e.Low == nil && e.High != nil {
		return coq.PureCall(coq.NewCallExpr("slice.take",
			ctx.expr(e.High), x))
	}
	if e.Low != nil && e.High != nil {
		return coq.PureCall(coq.NewCallExpr("slice.subslice",
			ctx.expr(e.Low), ctx.expr(e.High), x))
	}
	if e.Low == nil && e.High == nil {
		ctx.Unsupported(e, "complete slice doesn't do anything")
	}
	return nil
}

func (ctx Ctx) nilExpr(e *ast.Ident) coq.CallExpr {
	valueType := coq.TypeIdent("_")
	switch nilTy := ctx.info.TypeOf(e).(type) {
	case *types.Basic:
		if nilTy.Kind() != types.UntypedNil {
			ctx.Nope(e, "nil that is of a non-nil basic kind")
			return coq.CallExpr{}
		}
	default:
		ctx.Todo(e, "take advantage of nil type %s", nilTy)
	}
	return coq.CallExpr{
		MethodName: "slice.nil",
		Args:       []coq.Expr{valueType},
	}
}

func (ctx Ctx) expr(e ast.Expr) coq.Expr {
	switch e := e.(type) {
	case *ast.CallExpr:
		return ctx.callExpr(e)
	case *ast.MapType:
		return ctx.mapType(e)
	case *ast.Ident:
		if e.Obj != nil {
			return coq.IdentExpr(e.Name)
		}
		if e.Name == "nil" {
			return ctx.nilExpr(e)
		}
		ctx.Unsupported(e, "special identifier")
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
	case *ast.ParenExpr:
		return ctx.expr(e.X)
	default:
		ctx.Unsupported(e, "expr")
	}
	return nil
}

type genericAssign struct {
	Names    []string
	Rhs      coq.Expr
	IsDefine bool
}

func (ctx Ctx) parseAssignment(s *ast.AssignStmt) genericAssign {
	if len(s.Rhs) > 1 {
		ctx.Unsupported(s, "multiple RHS assignment (split them up)")
	}
	lhs, rhs := s.Lhs, s.Rhs[0]
	var names []string
	for _, lhsExpr := range lhs {
		ident, ok := getIdent(lhsExpr)
		if !ok {
			ctx.Nope(lhsExpr, "defining a non-identifier")
		}
		names = append(names, ident)
	}
	return genericAssign{names, ctx.expr(rhs), s.Tok == token.DEFINE}
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
		retExpr := coq.ReturnExpr{coq.IdentExpr("tt")}
		return coq.BlockExpr{[]coq.Binding{coq.NewAnon(retExpr)}}
	}
	return coq.BlockExpr{bindings}
}

func (ctx Ctx) ifStmt(s *ast.IfStmt, c *cursor, loopVar *string) coq.Binding {
	// TODO: be more careful about nested if statements; if the then branch has
	//  an if statement with early return, this is probably not handled correctly.
	//  We should conservatively disallow such returns until they're properly analyzed.
	thenExpr, ok := ctx.stmt(s.Body, &cursor{nil}, loopVar).Unwrap()
	if !ok {
		ctx.Nope(s.Body, "if statement body ends with an assignment")
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
	if endsWithReturn(s.Body) && remaining {
		if s.Else != nil {
			ctx.FutureWork(s.Else, "else with early return")
			return coq.Binding{}
		}
		ife.Else = ctx.stmts(c.Remainder(), loopVar)
		return coq.NewAnon(ife)
	}
	if !remaining {
		if s.Else == nil {
			if loopVar != nil {
				ctx.Unsupported(s, "implicit loop continue")
				return coq.Binding{}
			}
			ife.Else = coq.ReturnExpr{coq.IdentExpr("tt")}
			return coq.NewAnon(ife)
		}
		elseExpr, ok := ctx.stmt(s.Else, c, loopVar).Unwrap()
		if !ok {
			ctx.Nope(s.Else, "if statement else ends with an assignment")
			return coq.Binding{}
		}
		ife.Else = elseExpr
		return coq.NewAnon(ife)
	}
	// there are some other cases that can be handled but it's a bit tricky
	ctx.FutureWork(s, "non-terminal if expressions are only partially supported")
	return coq.Binding{}
}

func (ctx Ctx) loopVar(s ast.Stmt) (ident string, init coq.Expr) {
	initAssign, ok := s.(*ast.AssignStmt)
	if !ok ||
		len(initAssign.Lhs) > 1 ||
		len(initAssign.Rhs) > 1 ||
		initAssign.Tok != token.DEFINE {
		ctx.Unsupported(s, "loop initialization must be a single assignment")
		return "", nil
	}
	lhs, rhs := initAssign.Lhs[0], initAssign.Rhs[0]
	loopIdent, ok := getIdent(lhs)
	if !ok {
		ctx.Nope(initAssign, "definition of non-identifier")
		return "", nil
	}
	return loopIdent, ctx.expr(rhs)
}

func (ctx Ctx) forStmt(s *ast.ForStmt) coq.LoopExpr {
	if s.Cond != nil || s.Post != nil {
		ctx.Unsupported(s, "loop conditions and post expressions are unsupported")
		return coq.LoopExpr{}
	}
	if s.Init == nil {
		// need special handling (in particular, need to skip looking for a loop variable assignment)
		ctx.FutureWork(s, "loops without a loop variable")
		return coq.LoopExpr{}
	}
	ident, init := ctx.loopVar(s.Init)
	loop := coq.LoopExpr{
		LoopVarIdent: ident,
		Initial:      init,
	}
	c := &cursor{s.Body.List}
	var bindings []coq.Binding
	for c.HasNext() {
		bindings = append(bindings, ctx.stmt(c.Next(), c, &ident))
	}
	loop.Body = coq.BlockExpr{bindings}
	return loop
}

func (ctx Ctx) defineStmt(s *ast.AssignStmt) coq.Binding {
	if len(s.Rhs) > 1 {
		ctx.FutureWork(s, "multiple defines (split them up)")
	}
	rhs := s.Rhs[0]
	var names []string
	for _, lhsExpr := range s.Lhs {
		ident, ok := getIdent(lhsExpr)
		if !ok {
			ctx.Nope(lhsExpr, "defining a non-identifier")
		}
		names = append(names, ident)
	}
	return coq.Binding{names, ctx.expr(rhs)}
}

func (ctx Ctx) loopAssignStmt(s *ast.AssignStmt, c *cursor) coq.Binding {
	// look for correct loop continue/return
	if !c.HasNext() {
		ctx.Unsupported(s, "implicit control flow in loop (expected continue)")
	}
	b, ok := c.Next().(*ast.BranchStmt)
	if !ok || b.Tok != token.CONTINUE {
		loopVar := s.Lhs[0].(*ast.Ident).Name
		ctx.Unsupported(s, "expected continue following %s loop assignment", loopVar)
	}
	rhs := ctx.expr(s.Rhs[0])
	return coq.NewAnon(coq.LoopContinueExpr{rhs})
}

func (ctx Ctx) assignStmt(s *ast.AssignStmt, c *cursor, loopVar *string) coq.Binding {
	if s.Tok == token.DEFINE {
		return ctx.defineStmt(s)
	}
	if len(s.Lhs) > 1 || len(s.Rhs) > 1 {
		ctx.Unsupported(s, "multiple assignment")
	}
	// assignments can mean various things
	switch lhs := s.Lhs[0].(type) {
	case *ast.Ident:
		if loopVar != nil {
			if lhs.Name != *loopVar {
				ctx.Unsupported(s, "expected assignment to loop variable %s", *loopVar)
				return coq.Binding{}
			}
			return ctx.loopAssignStmt(s, c)
		}
		ctx.FutureWork(s, "general re-assignments are future work")
		return coq.Binding{}
	case *ast.IndexExpr:
		targetTy := ctx.info.TypeOf(lhs.X)
		switch targetTy.(type) {
		case *types.Slice:
			ctx.Todo(s, "slice updates")
		case *types.Map:
			value := ctx.expr(s.Rhs[0])
			return coq.NewAnon(coq.NewCallExpr(
				"Data.hashTableAlter",
				ctx.expr(lhs.X),
				ctx.expr(lhs.Index),
				coq.HashTableInsert{value}))
		default:
			ctx.Unsupported(s, "index update to unexpected target of type %v", targetTy)
		}
	case *ast.StarExpr:
		ctx.Todo(s, "storing to pointers")
	default:
		ctx.Unsupported(s, "assigning to complex ")
	}
	return coq.Binding{}
}

func (ctx Ctx) stmt(s ast.Stmt, c *cursor, loopVar *string) coq.Binding {
	switch s := s.(type) {
	case *ast.ReturnStmt:
		if c.HasNext() {
			ctx.Unsupported(c.Next(), "statement following return")
			return coq.Binding{}
		}
		if loopVar != nil {
			ctx.FutureWork(s, "return in loop (use break)")
			return coq.Binding{}
		}
		return coq.NewAnon(ctx.returnExpr(s.Results))
	case *ast.BranchStmt:
		if loopVar == nil {
			ctx.Unsupported(s, "branching outside of a loop")
		}
		if s.Tok != token.BREAK {
			ctx.Unsupported(s, "only break is supported to exit loops")
		}
		return coq.NewAnon(coq.LoopRetExpr{})
	case *ast.ExprStmt:
		return coq.NewAnon(ctx.expr(s.X))
	case *ast.AssignStmt:
		return ctx.assignStmt(s, c, loopVar)
	case *ast.BlockStmt:
		return coq.NewAnon(ctx.blockStmt(s, loopVar))
	case *ast.IfStmt:
		return ctx.ifStmt(s, c, loopVar)
	case *ast.ForStmt:
		return coq.NewAnon(ctx.forStmt(s))
	case *ast.GoStmt:
		ctx.Todo(s, "go func(){ ... } statements")
	default:
		ctx.Unsupported(s, "statement")
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
	fd.Body = ctx.blockStmt(d.Body, nil)
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
			ctx.Nope(d, "unknown token type in decl")
		}
	case *ast.BadDecl:
		ctx.Nope(d, "bad declaration in type-checked code")
	default:
		ctx.Nope(d, "top-level decl")
	}
	return nil
}

func (ctx Ctx) Decls(fs ...*ast.File) (decls []coq.Decl, err *ConversionError) {
	defer func() {
		if r := recover(); r != nil {
			r, ok := r.(ConversionError)
			if !ok {
				panic(r)
			}
			err = &r
		}
	}()
	for _, f := range fs {
		for _, d := range f.Decls {
			if d := ctx.maybeDecl(d); d != nil {
				decls = append(decls, d)
			}
		}
	}
	return
}
