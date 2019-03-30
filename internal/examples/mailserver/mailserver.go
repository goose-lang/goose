package mailserver

import (
	"github.com/tchajed/goose/machine"
	"github.com/tchajed/goose/machine/filesys"
)

type partialFile struct {
	off  uint64
	data []byte
}

func getUserDir(user uint64) string {
	return "user" + machine.UInt64ToString(user)
}

func readMessage(userDir string, name string) []byte {
	f := filesys.Open(userDir, name)
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
func Pickup(user uint64) [][]byte {
	userDir := getUserDir(user)
	names := filesys.List(userDir)
	messages := new([][]byte)
	initMessages := make([][]byte, 0)
	*messages = initMessages
	for i := uint64(0); ; {
		if i == uint64(len(names)) {
			break
		}
		name := names[i]
		msg := readMessage(userDir, name)
		oldMessages := *messages
		newMessages := append(oldMessages, msg)
		*messages = newMessages
		i = i + 1
		continue
	}
	msgs := *messages
	return msgs
}

func createTmp() (filesys.File, string) {
	initID := machine.RandomUint64()
	finalFile := new(filesys.File)
	finalName := new(string)
	for id := initID; ; {
		fname := machine.UInt64ToString(id)
		f, ok := filesys.Create("tmp", fname)
		if ok {
			*finalFile = f
			*finalName = fname
			break
		} else {
			newID := machine.RandomUint64()
			id = newID
			continue
		}
	}
	f := *finalFile
	name := *finalName
	return f, name
}

func writeTmp(data []byte) string {
	f, name := createTmp()
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
	return name
}

// Deliver stores a new message
func Deliver(user uint64, msg []byte) {
	userDir := getUserDir(user)
	tmpName := writeTmp(msg)
	initID := machine.RandomUint64()
	for id := initID; ; {
		ok := filesys.Link("spool", tmpName,
			userDir, "msg"+machine.UInt64ToString(id))
		if ok {
			break
		} else {
			newID := machine.RandomUint64()
			id = newID
			continue
		}
	}
	filesys.Delete("spool", tmpName)
}

func Recover() {
	spooled := filesys.List("spool")
	for i := uint64(0); ; {
		if i == uint64(len(spooled)) {
			break
		}
		name := spooled[i]
		filesys.Delete("spool", name)
		i = i + 1
		continue
	}
}
