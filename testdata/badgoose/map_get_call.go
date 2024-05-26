package badgoose

func mapGetCall() {
	handlers := make(map[uint64]func())
	handlers[0] = func() {}
	handlers[0]()
}
