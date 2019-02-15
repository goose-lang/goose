package simpledb

import (
	"sync"

	"github.com/tchajed/goose/machine"
	"github.com/tchajed/goose/machine/filesys"
)

// A Table provides access to an immutable copy of data on the filesystem,
// along with an index for fast random access.
type Table struct {
	Index map[uint64]uint64
	File  filesys.File
}

// CreateTable creates a new, empty table.
func CreateTable(p string) Table {
	index := make(map[uint64]uint64)
	f := filesys.Create(p)
	filesys.Close(f)
	f2 := filesys.Open(p)
	return Table{Index: index, File: f2}
}

// Entry represents a (key, value) pair.
type Entry struct {
	Key   uint64
	Value []byte
}

// DecodeUInt64 is a Decoder(uint64)
//
// All decoders have the shape func(p []byte) (T, uint64)
//
// The uint64 represents the number of bytes consumed; if 0,
// then decoding failed, and the value of type T should be ignored.
func DecodeUInt64(p []byte) (uint64, uint64) {
	if len(p) < 8 {
		return 0, 0
	}
	n := machine.UInt64Get(p)
	return n, 8
}

// DecodeEntry is a Decoder(Entry)
func DecodeEntry(data []byte) (Entry, uint64) {
	key, l1 := DecodeUInt64(data)
	if l1 == 0 {
		return Entry{Key: 0, Value: nil}, 0
	}
	valueLen, l2 := DecodeUInt64(data[l1:])
	if l2 == 0 {
		return Entry{Key: 0, Value: nil}, 0
	}
	value := data[l1+l2 : l1+l2+valueLen]
	return Entry{
		Key:   key,
		Value: value,
	}, l1 + l2 + valueLen
}

type lazyFileBuf struct {
	offset uint64
	next   []byte
}

// readTableIndex parses a complete table on disk into a key->offset index
func readTableIndex(f filesys.File, index map[uint64]uint64) {
	for buf := (lazyFileBuf{offset: 0, next: nil}); ; {
		e, l := DecodeEntry(buf.next)
		if l > 0 {
			index[e.Key] = 8 + buf.offset
			buf = lazyFileBuf{offset: buf.offset + l, next: buf.next[l:]}
			continue
		} else {
			p := filesys.ReadAt(f, buf.offset, 4096)
			if len(p) == 0 {
				break
			} else {
				newBuf := append(buf.next, p...)
				buf = lazyFileBuf{
					offset: buf.offset,
					next:   newBuf,
				}
				continue
			}
		}
	}
}

// RecoverTable restores a table from disk on startup.
func RecoverTable(p string) Table {
	index := make(map[uint64]uint64)
	f := filesys.Open(p)
	readTableIndex(f, index)
	return Table{Index: index, File: f}
}

// CloseTable frees up the fd held by a table.
func CloseTable(t Table) {
	filesys.Close(t.File)
}

func ReadValue(f filesys.File, off uint64) []byte {
	startBuf := filesys.ReadAt(f, off, 4096)
	totalBytes := machine.UInt64Get(startBuf)
	// should have enough data for the key if the file is a proper encoding
	buf := startBuf[8:]
	haveBytes := uint64(len(buf))
	if haveBytes < totalBytes {
		buf2 := filesys.ReadAt(f, off+4096, totalBytes-haveBytes)
		newBuf := append(buf, buf2...)
		return newBuf
	}
	return buf[:totalBytes]
}

func TableRead(t Table, k uint64) ([]byte, bool) {
	off, ok := t.Index[k]
	if !ok {
		return nil, false
	}
	p := ReadValue(t.File, off)
	return p, true
}

type bufFile struct {
	file filesys.File
	buf  *[]byte
}

func newBuf(f filesys.File) bufFile {
	buf := new([]byte)
	return bufFile{
		file: f,
		buf:  buf,
	}
}

func bufFlush(f bufFile) {
	buf := *f.buf
	if len(buf) == 0 {
		return
	}
	filesys.Append(f.file, buf)
	*f.buf = nil
}

func bufAppend(f bufFile, p []byte) {
	buf := *f.buf
	buf2 := append(buf, p...)
	*f.buf = buf2
}

func bufClose(f bufFile) {
	bufFlush(f)
	filesys.Close(f.file)
}

type tableWriter struct {
	index  map[uint64]uint64
	name   string
	file   bufFile
	offset *uint64
}

func newTableWriter(p string) tableWriter {
	index := make(map[uint64]uint64)
	f := filesys.Create(p)
	buf := newBuf(f)
	off := new(uint64)
	return tableWriter{
		index:  index,
		name:   p,
		file:   buf,
		offset: off,
	}
}

func tableWriterAppend(w tableWriter, p []byte) {
	bufAppend(w.file, p)
	off := *w.offset
	*w.offset = off + uint64(len(p))
}

func tableWriterClose(w tableWriter) Table {
	bufClose(w.file)
	f := filesys.Open(w.name)
	return Table{
		Index: w.index,
		File:  f,
	}
}

// EncodeUInt64 is an Encoder(uint64)
func EncodeUInt64(x uint64, p []byte) []byte {
	tmp := make([]byte, 8)
	machine.UInt64Put(tmp, x)
	p2 := append(p, tmp...)
	return p2
}

// EncodeSlice is an Encoder([]byte)
func EncodeSlice(data []byte, p []byte) []byte {
	p2 := EncodeUInt64(uint64(len(data)), p)
	p3 := append(p2, data...)
	return p3
}

func tablePut(w tableWriter, k uint64, v []byte) {
	tmp := make([]byte, 0)
	tmp2 := EncodeUInt64(k, tmp)
	tmp3 := EncodeSlice(v, tmp2)

	off := *w.offset
	// index points to encoded value
	w.index[k] = off + uint64(len(tmp2))

	// write to table
	tableWriterAppend(w, tmp3)
}

type Database struct {
	wbuffer *map[uint64][]byte
	rbuffer *map[uint64][]byte
	bufferL *sync.RWMutex
	table   *Table
	// the manifest
	tableName *string
	// protects both table and tableName
	tableL *sync.RWMutex
	// protects constructing shadow tables
	compactionL *sync.RWMutex
}

func makeValueBuffer() *map[uint64][]byte {
	buf := make(map[uint64][]byte)
	bufPtr := new(map[uint64][]byte)
	*bufPtr = buf
	return bufPtr
}

func NewDb() Database {
	wbuf := makeValueBuffer()
	rbuf := makeValueBuffer()
	bufferL := new(sync.RWMutex)
	tableName := "table.0"
	tableNameRef := new(string)
	*tableNameRef = tableName
	table := CreateTable(tableName)
	tableRef := new(Table)
	*tableRef = table
	tableL := new(sync.RWMutex)
	compactionL := new(sync.RWMutex)
	return Database{
		wbuffer:     wbuf,
		rbuffer:     rbuf,
		bufferL:     bufferL,
		table:       tableRef,
		tableName:   tableNameRef,
		tableL:      tableL,
		compactionL: compactionL,
	}
}

func Read(db Database, k uint64) ([]byte, bool) {
	db.bufferL.RLock()
	// first try write buffer
	buf := *db.wbuffer
	v, ok := buf[k]
	if ok {
		db.bufferL.RUnlock()
		return v, true
	}
	// ...then try read buffer
	rbuf := *db.rbuffer
	v2, ok := rbuf[k]
	if ok {
		db.bufferL.RUnlock()
		return v2, true
	}
	// ...and finally go to the table
	db.tableL.RLock()
	tbl := *db.table
	v3, ok := TableRead(tbl, k)
	db.tableL.RUnlock()
	db.bufferL.RUnlock()
	return v3, ok
}

func Write(db Database, k uint64, v []byte) {
	db.bufferL.Lock()
	buf := *db.wbuffer
	buf[k] = v
	db.bufferL.Unlock()
}
