package goose

import (
	"fmt"
	"go/ast"
	"go/constant"
	"go/importer"
	"go/token"
	"go/types"
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
		Defs:  make(map[*ast.Ident]types.Object),
		Uses:  make(map[*ast.Ident]types.Object),
		Types: make(map[ast.Expr]types.TypeAndValue),
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

func (ctx Ctx) typeOf(e ast.Expr) types.Type {
	return ctx.info.TypeOf(e)
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
		return coq.TypeIdent("File")
	}
	ctx.unsupported(e, "selector for unknown type %s", e)
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
		case "string", "uint64", "byte", "bool":
			return coq.TypeIdent(t.Name())
		default:
			ctx.unsupported(n, "basic types")
		}
	}
	return coq.TypeIdent("<type>")
}

func (ctx Ctx) arrayType(e *ast.ArrayType) coq.Type {
	if e.Len != nil {
		// arrays are not supported, only slices
		ctx.unsupported(e, "array types")
		return nil
	}
	return coq.SliceType{ctx.coqType(e.Elt)}
}

func (ctx Ctx) ptrType(e *ast.StarExpr) coq.Type {
	// check for *sync.RWMutex
	if e, ok := e.X.(*ast.SelectorExpr); ok {
		if isIdent(e.X, "sync") && isIdent(e.Sel, "RWMutex") {
			return coq.TypeIdent("LockRef")
		}
	}
	return coq.PtrType{ctx.coqType(e.X)}
}

func (ctx Ctx) coqType(e ast.Expr) coq.Type {
	switch e := e.(type) {
	case *ast.Ident:
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

func (ctx Ctx) fieldDecl(f *ast.Field) coq.FieldDecl {
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
		ctx.unsupported(spec, "non-struct type")
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
	xTy := ctx.typeOf(x)
	if _, ok := xTy.(*types.Slice); !ok {
		ctx.unsupported(e, "length of object of type %v", xTy)
		return coq.PureCall(coq.CallExpr{})
	}
	return coq.PureCall(coq.NewCallExpr("slice.length",
		ctx.expr(x),
	))
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
	args := []coq.Expr{ctx.expr(f.X)}
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
		args = append(args, coq.IdentExpr("Writer"))
	} else {
		args = append(args, coq.IdentExpr("Reader"))
	}
	if acquire {
		return coq.NewCallExpr("Data.lockAcquire", args...)
	}
	return coq.NewCallExpr("Data.lockRelease", args...)

}

func (ctx Ctx) selectorMethod(f *ast.SelectorExpr,
	args []ast.Expr) coq.CallExpr {
	if isIdent(f.X, "filesys") {
		return ctx.newCoqCall("FS."+toInitialLower(f.Sel.Name), args)
	}
	if isIdent(f.X, "machine") {
		switch f.Sel.Name {
		case "UInt64Get":
			return ctx.newCoqCall("Data.uint64Get", args)
		case "UInt64Put":
			return ctx.newCoqCall("Data.uint64Put", args)
		default:
			ctx.futureWork(f, "unhandled call to machine.%s", f.Sel.Name)
			return coq.CallExpr{}
		}
	}
	if isLockRef(ctx.typeOf(f.X)) {
		return ctx.lockMethod(f)
	}
	ctx.unsupported(f, "cannot call methods selected from %s", f.X)
	return coq.CallExpr{}
}

func (ctx Ctx) newCoqCall(method string, es []ast.Expr) coq.CallExpr {
	var args []coq.Expr
	for _, e := range es {
		args = append(args, ctx.expr(e))
	}
	return coq.NewCallExpr(method, args...)
}

func (ctx Ctx) methodExpr(f ast.Expr, args []ast.Expr) coq.CallExpr {
	switch f := f.(type) {
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
		return ctx.selectorMethod(f, args)
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
		return coq.NewCallExpr("Data.newMap", mapTy.Value)
	case *ast.ArrayType:
		if typeArg.Len != nil {
			ctx.nope(typeArg, "can't make() arrays (only slices)")
		}
		elt := ctx.coqType(typeArg.Elt)
		return coq.NewCallExpr("Data.newSlice", elt, ctx.expr(args[1]))
	default:
		ctx.nope(typeArg, "make() of %s, not a map or array", typeArg)
	}
	return coq.CallExpr{}
}

// newExpr parses a call to new() into an appropriate allocation
func (ctx Ctx) newExpr(ty ast.Expr) coq.CallExpr {
	if sel, ok := ty.(*ast.SelectorExpr); ok {
		if isIdent(sel.X, "sync") && isIdent(sel.Sel, "RWMutex") {
			return coq.NewCallExpr("Data.newLock")
		}
	}
	return coq.NewCallExpr("Data.newPtr", ctx.coqType(ty))
}

// basicallyUInt64 returns true conservatively when an
// expression can be treated as a uint64
func (ctx Ctx) basicallyUInt64(e ast.Expr) bool {
	basicTy, ok := ctx.typeOf(e).(*types.Basic)
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
	if isIdent(s.Fun, "make") {
		return ctx.makeExpr(s.Args)
	}
	if isIdent(s.Fun, "new") {
		return ctx.newExpr(s.Args[0])
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
		ctx.unsupported(s, "casts from non-int type %v to uint64", ctx.typeOf(x))
		return nil
	}
	return ctx.methodExpr(s.Fun, s.Args)
}

func (ctx Ctx) structSelector(e *ast.SelectorExpr) coq.ProjExpr {
	structType := ctx.typeOf(e.X).(*types.Named)
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
	structType, ok := ctx.typeOf(e).Underlying().(*types.Struct)
	if !ok {
		ctx.unsupported(e, "non-struct literal")
	}
	structName, ok := getIdent(e.Type)
	if !ok {
		ctx.nope(e.Type, "non-struct literal after type check")
	}
	lit := coq.StructLiteral{StructName: structName}
	foundFields := make(map[string]bool)
	for _, el := range e.Elts {
		switch el := el.(type) {
		case *ast.KeyValueExpr:
			ident, ok := getIdent(el.Key)
			if !ok {
				ctx.noExample(el.Key, "struct field keyed by non-identifier %+v", el.Key)
				return coq.StructLiteral{}
			}
			lit.Elts = append(lit.Elts, coq.FieldVal{
				Field: ident,
				Value: ctx.expr(el.Value),
			})
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
		v := ctx.info.Types[e].Value
		n, ok := constant.Uint64Val(v)
		if !ok {
			ctx.unsupported(e, "int literal isn't a valid uint64")
			return nil
		}
		return coq.IntLiteral{n}
	}
	ctx.unsupported(e, "literal with kind %s", e.Kind)
	return nil
}

func (ctx Ctx) binExpr(e *ast.BinaryExpr) coq.Expr {
	op, ok := map[token.Token]coq.BinOp{
		token.LSS: coq.OpLessThan,
		token.GTR: coq.OpGreaterThan,
		token.SUB: coq.OpMinus,
		token.EQL: coq.OpEquals,
	}[e.Op]
	if e.Op == token.ADD {
		if b, ok := ctx.typeOf(e.X).(*types.Basic); ok && b.Name() == "string" {
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
		ctx.unsupported(e, "complete slice doesn't do anything")
	}
	return nil
}

func (ctx Ctx) nilExpr(e *ast.Ident) coq.CallExpr {
	valueType := coq.TypeIdent("_")
	switch nilTy := ctx.typeOf(e).(type) {
	case *types.Basic:
		if nilTy.Kind() != types.UntypedNil {
			ctx.nope(e, "nil that is of a non-nil basic kind")
			return coq.CallExpr{}
		}
	default:
		ctx.todo(e, "take advantage of nil type %s", nilTy)
	}
	return coq.CallExpr{
		MethodName: "slice.nil",
		Args:       []coq.Expr{valueType},
	}
}

func (ctx Ctx) unaryExpr(e *ast.UnaryExpr) coq.Expr {
	if e.Op == token.NOT {
		return coq.NotExpr{ctx.expr(e.X)}
	}
	ctx.unsupported(e, "unary expression %s", e.Op)
	return nil
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
		if e.Name == "true" || e.Name == "false" {
			return coq.IdentExpr(e.Name)
		}
		ctx.unsupported(e, "special identifier")
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
		xTy := ctx.typeOf(e.X)
		switch xTy.(type) {
		case *types.Map:
			return coq.NewCallExpr("Data.mapGet",
				ctx.expr(e.X), ctx.expr(e.Index))
		case *types.Slice:
			return coq.NewCallExpr("Data.sliceRead",
				ctx.expr(e.X), ctx.expr(e.Index))
		}
		ctx.unsupported(e, "index into unknown type %v", xTy)
		return nil
	case *ast.UnaryExpr:
		return ctx.unaryExpr(e)
	case *ast.ParenExpr:
		return ctx.expr(e.X)
	case *ast.StarExpr:
		return coq.NewCallExpr("Data.readPtr", ctx.expr(e.X))
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
		ife.Else = coq.ReturnExpr{coq.IdentExpr("tt")}
		return coq.NewAnon(ife)
	}
	if !remaining {
		if s.Else == nil {
			if loopVar != nil {
				ctx.unsupported(s, "implicit loop continue")
				return coq.Binding{}
			}
			ife.Else = coq.ReturnExpr{coq.IdentExpr("tt")}
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

func (ctx Ctx) loopVar(s ast.Stmt) (ident string, init coq.Expr) {
	initAssign, ok := s.(*ast.AssignStmt)
	if !ok ||
		len(initAssign.Lhs) > 1 ||
		len(initAssign.Rhs) > 1 ||
		initAssign.Tok != token.DEFINE {
		ctx.unsupported(s, "loop initialization must be a single assignment")
		return "", nil
	}
	lhs, rhs := initAssign.Lhs[0], initAssign.Rhs[0]
	loopIdent, ok := getIdent(lhs)
	if !ok {
		ctx.nope(initAssign, "definition of non-identifier")
		return "", nil
	}
	return loopIdent, ctx.expr(rhs)
}

func (ctx Ctx) forStmt(s *ast.ForStmt) coq.LoopExpr {
	if s.Cond != nil || s.Post != nil {
		var bad ast.Node = s.Cond
		if s.Cond == nil {
			bad = s.Post
		}
		ctx.unsupported(bad, "loop conditions and post expressions are unsupported")
		return coq.LoopExpr{}
	}
	if s.Init == nil {
		// need special handling (in particular, need to skip looking for a loop variable assignment)
		ctx.futureWork(s, "loop without a loop variable")
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

func getIdentOrAnonymous(e ast.Expr) (ident string, ok bool) {
	if e == nil {
		return "_", true
	}
	return getIdent(e)
}

func (ctx Ctx) rangeStmt(s *ast.RangeStmt) coq.Expr {
	if _, ok := ctx.typeOf(s.X).(*types.Map); !ok {
		ctx.unsupported(s,
			"range over %v (only maps are supported)",
			ctx.typeOf(s.X))
		return nil
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

	var names []string
	for _, lhsExpr := range s.Lhs {
		ident, ok := getIdent(lhsExpr)
		if !ok {
			ctx.nope(lhsExpr, "defining a non-identifier")
		}
		names = append(names, ident)
	}
	return coq.Binding{names, ctx.expr(rhs)}
}

func (ctx Ctx) loopAssignStmt(s *ast.AssignStmt, c *cursor) coq.Binding {
	// look for correct loop continue/return
	if !c.HasNext() {
		ctx.unsupported(s, "implicit control flow in loop (expected continue)")
	}
	b, ok := c.Next().(*ast.BranchStmt)
	if !ok || b.Tok != token.CONTINUE {
		loopVar := s.Lhs[0].(*ast.Ident).Name
		ctx.unsupported(s, "expected continue following %s loop assignment", loopVar)
	}
	rhs := ctx.expr(s.Rhs[0])
	return coq.NewAnon(coq.LoopContinueExpr{rhs})
}

func (ctx Ctx) assignStmt(s *ast.AssignStmt, c *cursor, loopVar *string) coq.Binding {
	if s.Tok == token.DEFINE {
		return ctx.defineStmt(s)
	}
	if len(s.Lhs) > 1 || len(s.Rhs) > 1 {
		ctx.unsupported(s, "multiple assignment")
	}
	// assignments can mean various things
	switch lhs := s.Lhs[0].(type) {
	case *ast.Ident:
		if loopVar != nil {
			if lhs.Name != *loopVar {
				ctx.unsupported(s, "expected assignment to loop variable %s", *loopVar)
				return coq.Binding{}
			}
			return ctx.loopAssignStmt(s, c)
		}
		ctx.futureWork(s, "general re-assignments are future work")
		return coq.Binding{}
	case *ast.IndexExpr:
		targetTy := ctx.typeOf(lhs.X)
		switch targetTy.(type) {
		case *types.Slice:
			value := ctx.expr(s.Rhs[0])
			return coq.NewAnon(coq.NewCallExpr(
				"Data.sliceWrite",
				ctx.expr(lhs.X),
				ctx.expr(lhs.Index),
				value))
		case *types.Map:
			value := ctx.expr(s.Rhs[0])
			return coq.NewAnon(coq.NewCallExpr(
				"Data.mapAlter",
				ctx.expr(lhs.X),
				ctx.expr(lhs.Index),
				coq.HashTableInsert{value}))
		default:
			ctx.unsupported(s, "index update to unexpected target of type %v", targetTy)
		}
	case *ast.StarExpr:
		return coq.NewAnon(coq.NewCallExpr("Data.writePtr",
			ctx.expr(lhs.X), ctx.expr(s.Rhs[0])))
	default:
		ctx.unsupported(s, "assigning to complex ")
	}
	return coq.Binding{}
}

func (ctx Ctx) goStmt(s *ast.GoStmt, loopVar *string) coq.Expr {
	f, ok := s.Call.Fun.(*ast.FuncLit)
	if !ok {
		ctx.futureWork(s, "only go <func literal> is supported")
		return nil
	}
	if loopVar != nil {
		if !(len(s.Call.Args) == 1 &&
			isIdent(s.Call.Args[0], *loopVar)) {
			// if loop variable is not passed, function literal
			// captures the variable itself rather than its
			// value, which is not captured in the Coq model.
			//
			// go vet has a special check for this issue (see
			// https://play.golang.org/p/OBqSYKLtv4E for incorrect code it
			// catches, and https://play.golang.org/p/b7jZQ_QXcrF
			// for one idiomatic fix),
			//
			// We still need this check if the loop variable is unused in the
			// body (go vet won't complain in that case), but the code passes
			// something into the spawned code, which we don't substitute in
			// the emitted Coq.
			ctx.unsupported(s,
				"go statement must pass loop variable %s",
				*loopVar)
			return nil
		}
	} else {
		if len(s.Call.Args) != 0 {
			ctx.unsupported(f, "go of functions with arguments "+
				"(other than passing loop variables)")
			return nil
		}
	}
	return coq.SpawnExpr{Body: ctx.blockStmt(f.Body, nil)}
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
		if s.Tok != token.BREAK {
			ctx.unsupported(s, "only break is supported to exit loops")
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
		if loopVar != nil {
			ctx.unsupported(s, "nested loops")
			return coq.Binding{}
		}
		return coq.NewAnon(ctx.forStmt(s))
	case *ast.RangeStmt:
		return coq.NewAnon(ctx.rangeStmt(s))
	case *ast.GoStmt:
		return coq.NewAnon(ctx.goStmt(s, loopVar))
	default:
		ctx.unsupported(s, "statement")
	}
	return coq.Binding{}
}

func (ctx Ctx) returnExpr(es []ast.Expr) coq.Expr {
	if len(es) == 0 {
		// named returns are not supported, so this must return unit
		return coq.ReturnExpr{coq.IdentExpr("tt")}
	}
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
		ctx.futureWork(d.Recv, "methods need to be lifted by moving the receiver to the arg list")
	}
	for _, p := range d.Type.Params.List {
		fd.Args = append(fd.Args, ctx.fieldDecl(p))
	}
	fd.ReturnType = ctx.returnType(d.Type.Results)
	fd.Body = ctx.blockStmt(d.Body, nil)
	return fd
}

func (ctx Ctx) checkGlobalVar(d *ast.ValueSpec) {
	ctx.futureWork(d, "global variables (might be used for objects)")
}

func stringBasicLit(lit *ast.BasicLit) string {
	if lit.Kind != token.STRING {
		panic("unexpected non-string literal")
	}
	s := lit.Value
	return s[1 : len(s)-1]
}

var okImports = map[string]bool{
	"github.com/tchajed/goose/machine":         true,
	"github.com/tchajed/goose/machine/filesys": true,
	"sync": true,
}

func (ctx Ctx) checkImports(d []ast.Spec) {
	for _, s := range d {
		s := s.(*ast.ImportSpec)
		importPath := stringBasicLit(s.Path)
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
			ctx.todo(d, "global constants")
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
