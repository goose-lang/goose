package logging2

import (
	"github.com/tchajed/goose/machine"
	"github.com/tchajed/goose/machine/disk"

	"sync"
)

const LogCommit = uint64(0)
const LogStart = uint64(1)

type Log struct {
	logLock   *sync.RWMutex // protects on disk log
	memLock   *sync.RWMutex // protects in-memory state
	logSz     uint64
	memLog    *[]disk.Block // in-memory log
	memLen    *uint64       // length of in-memory log
	memTxnNxt *uint64       // next in-memory transaction number
	logTxnNxt *uint64       // next log transaction number
}

func (log Log) writeHdr(len uint64) {
	hdr := make([]byte, 4096)
	machine.UInt64Put(hdr, len)
	disk.Write(LogCommit, hdr)
}

func Init(logSz uint64) Log {
	memLenPtr := new(uint64)
	*memLenPtr = 0
	memTxnNxtPtr := new(uint64)
	*memTxnNxtPtr = 0
	logTxnNxtPtr := new(uint64)
	*logTxnNxtPtr = 0
	log := Log{
		logLock:   new(sync.RWMutex),
		memLock:   new(sync.RWMutex),
		logSz:     logSz,
		memLog:    new([]disk.Block),
		memLen:    memLenPtr,
		memTxnNxt: memTxnNxtPtr,
		logTxnNxt: logTxnNxtPtr,
	}
	log.writeHdr(0)
	return log
}

func (log Log) readHdr() uint64 {
	hdr := disk.Read(LogCommit)
	disklen := machine.UInt64Get(hdr)
	return disklen
}

func (log Log) readBlocks(len uint64) []disk.Block {
	blks := new([]disk.Block)
	initblks := make([]disk.Block, 0)
	*blks = initblks
	for i := uint64(0); ; {
		if i < len {
			blk := disk.Read(LogStart + i)
			oldblks := *blks
			newblks := append(oldblks, blk)
			*blks = newblks
			i = i + 1
			continue
		}
		break
	}
	blocks := *blks
	return blocks
}

func (log Log) Read() []disk.Block {
	log.logLock.Lock()
	disklen := log.readHdr()
	blks := log.readBlocks(disklen)
	log.logLock.Unlock()
	return blks
}

func (log Log) memWrite(l []disk.Block) {
	for i := uint64(0); ; {
		if i < uint64(len(l)) {
			oldblks := *log.memLog
			newblks := append(oldblks, l[i])
			*log.memLog = newblks
			i = i + 1
			continue
		}
		break
	}
}

func (log Log) memAppend(l []disk.Block) (bool, uint64) {
	log.memLock.Lock()
	if *log.memLen+uint64(len(l)) >= log.logSz {
		log.memLock.Unlock()
		return false, uint64(0)
	} else {
		txn := *log.memTxnNxt
		n := *log.memLen + uint64(len(l))
		*log.memLen = n
		*log.memTxnNxt = *log.memTxnNxt + 1
		log.memLock.Unlock()
		return true, txn
	}
}

// XXX just an atomic read?
func (log Log) readLogTxnNxt() uint64 {
	log.memLock.Lock()
	n := *log.logTxnNxt
	log.memLock.Unlock()
	return n
}

func (log Log) diskAppendWait(txn uint64) {
	for done := false; ; {
		if done {
			break
		}
		logtxn := log.readLogTxnNxt()
		done = txn < logtxn
		continue
	}
}

func (log Log) Append(l []disk.Block) bool {
	ok, txn := log.memAppend(l)
	if ok {
		log.diskAppendWait(txn)
	}
	return ok
}

func (log Log) writeBlocks(l []disk.Block, pos uint64) {
	n := uint64(len(l))
	for i := uint64(0); i < n; i++ {
		bk := l[i]
		disk.Write(pos+i, bk)
	}
}

func (log Log) diskAppend() {
	log.logLock.Lock()
	disklen := log.readHdr()

	log.memLock.Lock()
	memlen := *log.memLen
	allblks := *log.memLog
	blks := allblks[disklen:]
	memnxt := *log.memTxnNxt
	log.memLock.Unlock()

	log.writeBlocks(blks, disklen)
	log.writeHdr(memlen)

	*log.logTxnNxt = memnxt // XXX updating wo holding lock, atomic write?

	log.logLock.Unlock()
}

func (log Log) Logger() {
	for dummy := true; ; {
		log.diskAppend()
		dummy = !dummy
		continue
	}
}
