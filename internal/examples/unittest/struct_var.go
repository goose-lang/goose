package unittest

type StructWrap struct {
	i uint64
}

func storeInStructVar() {
	var p StructWrap = StructWrap{i: 0}
	p.i = 5
}

func storeInStructPointerVar() {
	var p *StructWrap = new(StructWrap)
	p.i = 5
}
