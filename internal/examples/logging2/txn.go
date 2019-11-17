package logging2

import (
	"github.com/tchajed/goose/machine/disk"
)

type Txn struct {
	log  *Log
	blks *map[uint64]disk.Block
}

// XXX wait if cannot reserve space in log
func Begin(log *Log) Txn {
	txn := Txn{
		log:  log,
		blks: new(map[uint64]disk.Block),
	}
	return txn
}

func (txn Txn) Write(addr uint64, blk *disk.Block) bool {
	_, ok := (*txn.blks)[addr]
	if ok {
		(*txn.blks)[addr] = *blk
	}
	if !ok {
		// goose doesn't like LogMaxBlk
		//if n == LOGMAXBLK {
		//	return false
		//}
		(*txn.blks)[addr] = *blk
	}
	return true
}

func (txn Txn) Read(addr uint64) disk.Block {
	v, ok := (*txn.blks)[addr]
	if ok {
		return v
	} else {
		// goose doesn't like LogEnd
		// return disk.Read(addr + LOGEND)
		return disk.Read(addr)
	}
}

func (txn Txn) Commit() bool {
	blks := new([]disk.Block)
	for _, v := range *txn.blks {
		*blks = append(*blks, v)
	}
	ok := (*txn.log).Append(*blks)
	return ok
}
