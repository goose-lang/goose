package mailboat

import (
	"sync"

	"github.com/tchajed/goose/machine"
	"github.com/tchajed/goose/machine/filesys"

	"github.com/tchajed/mailboat/globals"
)

type partialFile struct {
	off  uint64
	data []byte
}

func getUserDir(user uint64) string {
	return "user" + machine.UInt64ToString(user)
}

const SpoolDir = "spool"

const NumUsers uint64 = 100

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

type Message struct {
	Id       string
	Contents []byte
}

// Pickup reads all stored messages
func Pickup(user uint64) []Message {
	ls := globals.GetX()
	l := ls[user]
	l.Lock()
	userDir := getUserDir(user)
	names := filesys.List(userDir)
	messages := new([]Message)
	initMessages := make([]Message, 0)
	*messages = initMessages
	for i := uint64(0); ; {
		if i == uint64(len(names)) {
			break
		}
		name := names[i]
		msg := readMessage(userDir, name)
		oldMessages := *messages
		newMessages := append(oldMessages, Message{Id: name, Contents: msg})
		*messages = newMessages
		i = i + 1
		continue
	}
	msgs := *messages
	l.Unlock()
	return msgs
}

func createTmp() (filesys.File, string) {
	initID := machine.RandomUint64()
	finalFile := new(filesys.File)
	finalName := new(string)
	for id := initID; ; {
		fname := machine.UInt64ToString(id)
		f, ok := filesys.Create(SpoolDir, fname)
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
		ok := filesys.Link(SpoolDir, tmpName,
			userDir, "msg"+machine.UInt64ToString(id))
		if ok {
			break
		} else {
			newID := machine.RandomUint64()
			id = newID
			continue
		}
	}
	filesys.Delete(SpoolDir, tmpName)
}

func Delete(user uint64, msgID string) {
	ls := globals.GetX()
	l := ls[user]
	l.Lock()
	userDir := getUserDir(user)
	filesys.Delete(userDir, msgID)
	l.Unlock()
}

func initLocks() {
	locks := new([]*sync.RWMutex)
	for i := uint64(0); ; {
		if i == NumUsers {
			break
		}
		oldLocks := *locks
		l := new(sync.RWMutex)
		newLocks := append(oldLocks, l)
		*locks = newLocks
		i = i + 1
		continue
	}
	finalLocks := *locks
	globals.SetX(finalLocks)
}

func Recover() {
	initLocks()
	spooled := filesys.List(SpoolDir)
	for i := uint64(0); ; {
		if i == uint64(len(spooled)) {
			break
		}
		name := spooled[i]
		filesys.Delete(SpoolDir, name)
		i = i + 1
		continue
	}
}
