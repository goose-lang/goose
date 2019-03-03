package mailserver

import (
	"github.com/tchajed/goose/machine"
	"github.com/tchajed/goose/machine/filesys"
)

type partialFile struct {
	off  uint64
	data []byte
}

func readMessage(name string) []byte {
	f := filesys.Open(name)
	fileContents := new([]byte)
	for pf := (partialFile{off: 0, data: nil}); ; {
		buf := filesys.ReadAt(f, pf.off, 4096)
		newData := append(pf.data, buf...)
		if uint64(len(buf)) < 4096 {
			*fileContents = newData
			break
		}
		pf = partialFile{off: pf.off, data: newData}
		continue
	}
	fileData := *fileContents
	return fileData
}

// Pickup reads all stored messages
func Pickup() [][]byte {
	names := filesys.List()
	messages := new([][]byte)
	initMessages := make([][]byte, 0)
	*messages = initMessages
	for i := uint64(0); ; {
		if i == uint64(len(names)) {
			break
		}
		name := names[i]
		msg := readMessage(name)
		oldMessages := *messages
		newMessages := append(oldMessages, msg)
		*messages = newMessages
		i = i + 1
		continue
	}
	msgs := *messages
	return msgs
}

func writeAll(fname string, data []byte) {
	f := filesys.Create(fname)
	for buf := data; ; {
		if len(buf) < 4096 {
			filesys.Append(f, buf)
			break
		}
		filesys.Append(f, buf[:4096])
		buf = buf[4096:]
		continue
	}
	filesys.Close(f)
}

// Deliver stores a new message
//
// tid should be a unique thread ID (used as a helper for spooling the message).
func Deliver(tid string, msg []byte) {
	writeAll(tid, msg)
	initID := machine.RandomUint64()
	for id := initID; ; {
		ok := filesys.Link(tid, "msg"+machine.UInt64ToString(id))
		if ok {
			break
		} else {
			newID := machine.RandomUint64()
			id = newID
			continue
		}
	}
}
