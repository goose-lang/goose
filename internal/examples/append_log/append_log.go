// Append-only, sequential, crash-safe log.
//
// The main interesting feature is that the log supports multi-block atomic
// appends, which are implemented by atomically updating an on-disk header with
// the number of valid blocks in the log.
package append_log

import (
	"github.com/tchajed/goose/machine"
	"github.com/tchajed/goose/machine/disk"
)

// TODO: use this instead of encoding manually
type Enc struct {
	b   disk.Block
	off *uint64
}

func NewEnc() Enc {
	return Enc{
		b:   make(disk.Block, disk.BlockSize),
		off: new(uint64),
	}
}

func (enc Enc) PutInt(x uint64) {
	off := *enc.off
	machine.UInt64Put(enc.b[off:], x)
	*enc.off += 8
}

func (enc Enc) Finish() disk.Block {
	return enc.b
}

type Dec struct {
	b   disk.Block
	off *uint64
}

func NewDec(b disk.Block) Dec {
	return Dec{b: b, off: new(uint64)}
}

func (dec Dec) GetInt() uint64 {
	off := *dec.off
	*dec.off += 8
	return machine.UInt64Get(dec.b[off:])
}

type Log struct {
	sz     uint64
	diskSz uint64
}

func (log Log) mkHdr() disk.Block {
	enc := NewEnc()
	enc.PutInt(log.sz)
	enc.PutInt(log.diskSz)
	return enc.Finish()
}

func (log Log) writeHdr() {
	disk.Write(0, log.mkHdr())
}

func Init(diskSz uint64) (Log, bool) {
	if diskSz < 1 {
		return Log{sz: 0, diskSz: 0}, false
	}
	log := Log{sz: 0, diskSz: diskSz}
	log.writeHdr()
	return log, true
}

func Open() Log {
	hdr := disk.Read(0)
	dec := NewDec(hdr)
	sz := dec.GetInt()
	diskSz := dec.GetInt()
	return Log{sz: sz, diskSz: diskSz}
}

func (log Log) Get(i uint64) (disk.Block, bool) {
	sz := log.sz
	if i < sz {
		return disk.Read(1 + i), true
	}
	return nil, false
}

func writeAll(bks []disk.Block, off uint64) {
	for i, bk := range bks {
		disk.Write(off+uint64(i), bk)
	}
}

func (log *Log) Append(bks []disk.Block) bool {
	sz := log.sz
	if uint64(len(bks)) >= log.diskSz-1-sz {
		return false
	}
	writeAll(bks, 1+sz)
	newLog := Log{sz: sz + uint64(len(bks)), diskSz: log.diskSz}
	newLog.writeHdr()
	*log = newLog
	return true
}

func (log *Log) Reset() {
	newLog := Log{sz: 0, diskSz: log.diskSz}
	newLog.writeHdr()
	*log = newLog
}
