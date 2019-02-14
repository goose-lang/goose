package goose

import (
	"strings"

	. "gopkg.in/check.v1"
)

type EndToEndSuite struct{}

var _ = Suite(&EndToEndSuite{})

type goCoqExample struct {
	Go, Coq string
}

func example(goSrc, coqSrc string) goCoqExample {
	return goCoqExample{
		Go:  strings.TrimSpace(goSrc),
		Coq: strings.TrimSpace(coqSrc),
	}
}

func (s *EndToEndSuite) TestPositiveExamples(c *C) {
	for _, tt := range []goCoqExample{
		example(`
func DoNothing(){}
`, `
Definition DoNothing  : proc unit :=
  Ret tt.
`),
		example(`
func Add(x uint64, y uint64) uint64 {
  z := x + y
  return z
}
`, `
Definition Add (x:uint64) (y:uint64) : proc uint64 :=
  let z := x + y in
  Ret z.
`),
		example(`
import "github.com/tchajed/goose/machine"

// DecodeUInt64 is a Decoder(uint64)
func DecodeUInt64(p []byte) (uint64, uint64) {
	if len(p) < 8 {
		return 0, 0
	}
	n := machine.UInt64Get(p)
	return n, 8
}
`, `
(* DecodeUInt64 is a Decoder(uint64) *)
Definition DecodeUInt64 (p:slice.t byte) : proc (uint64 * uint64) :=
  if compare (slice.length p) (fromNum 8) == Lt
  then Ret (0, 0)
  else
    n <- Data.uint64Get p;
    Ret (n, fromNum 8).
`),
		example(`
import "github.com/tchajed/goose/machine/filesys"

var fs filesys.Filesys = filesys.Fs

// Entry represents a (key, value) pair.
type Entry struct {
	Key   uint64
	Value []byte
}

func DecodeEntry(data []byte) (Entry, uint64) {
   return Entry{Key: 0, Value: nil}, 0
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
			p := fs.ReadAt(f, buf.offset, 4096)
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
`, `
(* readTableIndex parses a complete table on disk into a key->offset index *)
Definition readTableIndex (f:Fd) (index:HashTable uint64) : proc unit :=
  Loop (fun buf =>
        let! (e, l) <- DecodeEntry buf.(lazyFileBuf.next);
        if compare l 0 == Gt
        then
          _ <- Data.hashTableAlter index e.(Entry.Key) (fun _ => Some (fromNum 8 + buf.(lazyFileBuf.offset)));
          Continue {| lazyFileBuf.offset := buf.(lazyFileBuf.offset) + 1;
                      lazyFileBuf.next := slice.skip l buf.(lazyFileBuf.next); |}
        else
          p <- Base.sliceReadAt f buf.(lazyFileBuf.offset) 4096;
          if slice.length p == 0
          then LoopRet tt
          else
            newBuf <- Data.sliceAppendSlice buf.(lazyFileBuf.next) p;
            Continue {| lazyFileBuf.offset := buf.(lazyFileBuf.offset);
                        lazyFileBuf.next := newBuf; |}) {| lazyFileBuf.offset := 0;
           lazyFileBuf.next := slice.nil _; |}.
`),
		example(`
func Skip(){}

func CountUp(n uint64) {
  for i := uint64(0);; {
    if i > n {
       break
    }
    Skip()
	i = i + 1
    continue
  }
}
`, `
Definition CountUp (n:uint64) : proc unit :=
  Loop (fun i =>
        if compare i n == Gt
        then LoopRet tt
        else
          _ <- Skip;
          Continue (i + 1)) 0.
`),
		example(`
import "github.com/tchajed/goose/machine/filesys"

var fs filesys.Filesys = filesys.Fs

// A Table provides cached access to a table file.
type Table struct {
	Index map[uint64]uint64
	File  filesys.File
}
`, `
Module Table.
  (* A Table provides cached access to a table file. *)
  Record t := mk {
    Index: HashTable uint64;
    File: Fd;
  }.
End Table.
`),
		example(`
import "github.com/tchajed/goose/machine/filesys"

var fs filesys.Filesys = filesys.Fs

// A Table provides access to an immutable copy of data on the filesystem, along
// with an index for fast random access.
type Table struct {
	Index map[uint64]uint64
	File  filesys.File
}

// CreateTable creates a new, empty table.
func CreateTable(p string) Table {
	index := make(map[uint64]uint64)
	f := fs.Create(p)
	fs.Close(f)
	f2 := fs.Open(p)
	return Table{Index: index, File: f2}
}
`, `
(* CreateTable creates a new, empty table. *)
Definition CreateTable (p:Path) : proc Table.t :=
  index <- Data.newHashTable uint64;
  f <- FS.create p;
  _ <- FS.close f;
  f2 <- FS.open p;
  Ret {| Table.Index := index;
         Table.File := f2; |}.
`),
		example(`
import "github.com/tchajed/goose/machine"

func PureDemo(p []byte) uint64 {
  x := uint64(len(p))
  y := uint64(2 + 3)
  z := machine.UInt64Get(p)
  return x + y + z
}
`, `
Definition PureDemo (p:slice.t byte) : proc uint64 :=
  let x := slice.length p in
  let y := fromNum 2 + fromNum 3 in
  z <- Data.uint64Get p;
  Ret (x + y + z).
`),
		example(`
import "github.com/tchajed/goose/machine/filesys"

var fs filesys.Filesys = filesys.Fs

type Table struct {
	Index map[uint64]uint64
	File  filesys.File
}

// CloseTable frees up the fd held by a table.
func CloseTable(t Table) {
	fs.Close(t.File)
}
`, `
(* CloseTable frees up the fd held by a table. *)
Definition CloseTable (t:Table.t) : proc unit :=
  FS.close t.(Table.File).
`),
		example(`
func SliceRet(p []byte) []byte {
	return p
}`, `
Definition SliceRet (p:slice.t byte) : proc (slice.t byte) :=
  Ret p.
`),
		example(`
func MapRead(t map[uint64][]byte) []byte {
	v, ok := t[1]
	if !ok {
		return nil
	}
	return v
}`, `
Definition MapRead (t:HashTable (slice.t byte)) : proc (slice.t byte) :=
  let! (v, ok) <- Data.goHashTableLookup t 1;
  if negb ok
  then Ret (slice.nil _)
  else Ret v.
`),
	} {
		decls, err := fileDecls(tt.Go)
		if !c.Check(err, IsNil) {
			continue
		}
		converted := decls[len(decls)-1].CoqDecl()
		c.Check(converted, Equals, tt.Coq)
	}
}

type negativeGoExample struct {
	GoSrc   string
	BadCode string
}

func badCode(goSrc string, snippet string) negativeGoExample {
	return negativeGoExample{GoSrc: strings.TrimSpace(goSrc), BadCode: strings.TrimSpace(snippet)}
}

func (s *EndToEndSuite) TestNegativeExamples(c *C) {
	for _, tt := range []negativeGoExample{
		badCode(`func Unnamed(byte){}`, ""),
		badCode(`func TakeArray(b [3]byte){}`, "[3]byte"),
		badCode(`
type S struct{
  Field1, Field2 string
}
`, ""), // sadly no attribution
		badCode(`type S string`, "S string"),
		badCode(`
func BadLoop() {
  for i := uint64(0); i < uint64(3); {
  }
}`, "i < uint64(3)"),
		badCode(`
func BadLoop() {
  for i := uint64(0);; i++ {
  }
}`, "i++"),
		badCode(`
func BadLoop() {
  for i := uint64(0);; {
    if i < 4 {
       // missing loop var assignment
       continue
    }
    break
  }
}`, "continue"),
		badCode(`
func BadLoop() {
	for i := uint64(0);; {
		if i < 4 {
			i = 0
			continue
		}
		// implicit continue
	}
}`, `
if i < 4 {
	i = 0
	continue
}`),
		badCode(`
func Skip(){}

func ComplexIfFlow(i uint64) {
	if i == 0 {
		return
	} else {
		Skip()
	}
	// this is too complicated
	Skip()
}`, `{
	Skip()
}`),
	} {
		_, err := fileDecls(tt.GoSrc)
		if err == nil {
			c.Errorf("expected conversion error due to %s", tt.BadCode)
			continue
		}
		cerr := err.(*ConversionError)
		if !c.Check(cerr.Category, Matches, "(unsupported|future|todo)") {
			c.Errorf("unexpected conversion error [%s] %s", cerr.Category, cerr.Message)
			continue
		}
		if !c.Check(strings.TrimSpace(cerr.GoCode), Equals, tt.BadCode) {
			c.Errorf("unexpected Go attribution for [%s] %s", cerr.Category, cerr.Message)
			continue
		}
	}
}
