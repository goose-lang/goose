package example

func TodoVarFunc() {
	// TODO: we should support function types.
	var f func() // ERROR function type
	_ = f
}
