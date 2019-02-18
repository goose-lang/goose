package example

func nestedLoops() {
	for i := uint64(0); ; {
		for j := uint64(0); ; { // ERROR nested loop
			if true {
				break
			}
			j = j + 1
			continue
		}
		i = i + 1
		continue
	}
}
