package newloop

/*
goose_lang.lib.loop.Loop:

Definition Loop: val :=
	λ: "body",
	(rec: "loop" <> :=
	   let: "continue" := (Var "body") #() in
	   if: Var "continue"
	   then (Var "loop") #()
	   else #()) #().
*/

func basicLoop(body func() bool) {
	if !body() {
		return
	}
	basicLoop(body)
}

/*
goose_lang.lib.loop.For:

Definition For: val :=

λ: "cond" "body" "post",
(rec: "loop" <> :=
	let: "continue" :=
	   (if: (Var "cond") #()
	    then (Var "body") #()
	    else #false) in
	if: (Var "continue")
	then (Var "post") #();; (Var "loop") #()
	else #()) #().
*/

func iterLoop(cond func() bool, body func() bool, post func()) {
	// Run cond and body sequentially.
	if !cond() {
		return
	}
	if !body() {
		return
	}
	post()
	iterLoop(cond, body, post)
}

func sumBasic(n uint64) uint64 {
	var sum uint64
	var i uint64
	for {
		sum += i
		if i == n {
			break
		}
		i++
	}
	return sum
}

func sumBasicNew(n uint64) uint64 {
	var sum uint64
	var i uint64
	body := func() bool {
		sum += i
		if i == n {
			return false
		}
		i++
		return true
	}
	basicLoop(body)
	return sum
}

func sumIter(n uint64) uint64 {
	var sum uint64
	var i uint64
	for ; i <= n; i++ {
		sum += i
	}
	return sum
}

func sumIterNew(n uint64) uint64 {
	var sum uint64
	var i uint64
	cond := func() bool {
		return i <= n
	}
	body := func() bool {
		sum += i
		return true
	}
	post := func() {
		i++
	}
	iterLoop(cond, body, post)
	return sum
}
