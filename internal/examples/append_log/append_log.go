package append_log

import (
	"github.com/tchajed/goose/machine"
	"github.com/tchajed/goose/machine/disk"
)

/*
	Append-only, sequential, crash-safe log.

    The main interesting feature is that the log supports multi-block atomic
    appends, which are implemented by atomically updating an on-disk header with
    the number of valid blocks in the log.
*/

type Log struct {
	logSz  uint64
	diskSz uint64
}

func (log Log) writeHdr() {
	hdr := make([]byte, 4096)
	machine.UInt64Put(hdr, log.logSz)
	machine.UInt64Put(hdr[8:], log.logSz)
	disk.Write(0, hdr)
}

func Init(diskSz uint64) (Log, bool) {
	if diskSz < 1 {
		return Log{logSz: 0, diskSz: 0}, false
	}
	log := Log{logSz: 0, diskSz: diskSz}
	log.writeHdr()
	return log, true
}

func (log Log) Get(i uint64) (disk.Block, bool) {
	sz := log.logSz
	if i < sz {
		return disk.Read(1 + i), true
	}
	return nil, false
}

func writeAll(bks []disk.Block, off uint64) {
	numBks := uint64(len(bks))
	for i := uint64(0); i < numBks; i++ {
		bk := bks[i]
		disk.Write(off+i, bk)
	}
}

func (log *Log) Append(bks []disk.Block) bool {
	sz := log.logSz
	if 1+sz+uint64(len(bks)) >= log.diskSz {
		return false
	}
	writeAll(bks, 1+sz)
	newLog := Log{logSz: sz + uint64(len(bks)), diskSz: log.diskSz}
	newLog.writeHdr()
	*log = newLog
	return true
}

func (log *Log) Reset() {
	newLog := Log{logSz: 0, diskSz: log.diskSz}
	newLog.writeHdr()
	*log = newLog
}
