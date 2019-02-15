package simpledb

import (
	"github.com/tchajed/goose/machine"
	"github.com/tchajed/goose/machine/filesys"
)

// A Table provides access to an immutable copy of data on the filesystem, along
// with an index for fast random access.
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
// The uint64 represents the number of bytes consumed; if 0, then decoding
// failed, and the value of type T should be ignored.
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
			buf = lazyFileBuf{offset: buf.offset + 1, next: buf.next[l:]}
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
	buf := filesys.ReadAt(f, off, 4096)
	totalBytes := machine.UInt64Get(buf)
	haveBytes := uint64(len(buf[8:]))
	if haveBytes < totalBytes {
		buf2 := filesys.ReadAt(f, off+4096, totalBytes-haveBytes)
		newBuf := append(buf, buf2...)
		return newBuf
	}
	return buf
}

func TableRead(t Table, k uint64) []byte {
	off, ok := t.Index[k]
	if !ok {
		return nil
	}
	p := ReadValue(t.File, off)
	return p
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
