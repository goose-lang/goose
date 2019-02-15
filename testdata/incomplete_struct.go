package example

type S struct {
	foo uint64
	bar []byte
}

func mkS() S {
	return S{foo: 3} // ERROR incomplete struct
}
