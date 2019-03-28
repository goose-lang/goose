package example

import "github.com/tchajed/goose/machine/filesys"

func UsingFs(p string) {
	filesys.Fs.Create("dir", p) // ERROR cannot call methods
	return
}
