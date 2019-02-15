package goose_test

import (
	"bytes"
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"io/ioutil"
	"os"
	"path"
	"testing"

	"golang.org/x/tools/go/expect"

	"github.com/tchajed/goose"
	"github.com/tchajed/goose/coq"
)

import . "gopkg.in/check.v1"

func Test(t *testing.T) { TestingT(t) }

type ExamplesSuite struct{}

var _ = Suite(&ExamplesSuite{})

func (s *ExamplesSuite) TestPositiveExamples(c *C) {
	f, err := os.Open("./examples")
	if err != nil {
		c.Fatal(err)
	}
	defer f.Close()
	names, err := f.Readdirnames(0)
	if err != nil {
		c.Fatal(err)
	}
	var conf goose.Config
	for _, srcDir := range names {
		srcPath := path.Join("examples", srcDir)
		info, _ := os.Stat(srcPath)
		if !info.IsDir() {
			continue
		}

		f, terr := conf.TranslatePackage(srcPath)
		if terr != nil {
			c.Errorf("%s translation failed (%s)", srcDir, terr.Message)
			fmt.Fprintln(os.Stderr, terr.Err)
			continue
		}

		var b bytes.Buffer
		f.Write(&b)
		actual := b.Bytes()

		goldFile := path.Join(srcPath, srcDir+".gold.v")
		expected, err := ioutil.ReadFile(goldFile)
		if err != nil {
			c.Errorf("could not load gold output %s", srcDir+".gold.v")
		}
		if !bytes.Equal(actual, expected) {
			actualFile := path.Join(srcPath, srcDir+".actual.v")
			c.Errorf("actual Coq output != gold output; see %s", actualFile)
			err := ioutil.WriteFile(actualFile, actual, 0644)
			if err != nil {
				panic(err)
			}
		} else {
			// when tests pass, clean up actual output
			_ = os.Remove(path.Join(srcPath, srcDir+".actual.v"))
		}
	}
}

func translateFile(filePath string) (coq.File, *expect.Note, error) {
	fset := token.NewFileSet()
	ctx := goose.NewCtx(fset, goose.Config{})
	f, err := parser.ParseFile(fset, filePath, nil, parser.ParseComments)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		panic("test code does not parse")
	}

	notes, err := expect.Extract(fset, f)
	if err != nil {
		panic("test code's expect notes do not parse")
	}
	var note *expect.Note
	if len(notes) > 0 {
		note = notes[0]
	}

	err = ctx.TypeCheck("example", []*ast.File{f})
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		panic("test code does not type check")
	}

	coqFile, err := ctx.File(f)
	return coqFile, note, err
}

func (s *ExamplesSuite) TestNegativeExamples(c *C) {
	f, err := os.Open("./testdata")
	if err != nil {
		c.Fatal(err)
	}
	defer f.Close()
	names, err := f.Readdirnames(0)
	if err != nil {
		c.Fatal(err)
	}
	for _, n := range names {
		_, note, rawErr := translateFile(path.Join("testdata", n))
		if rawErr == nil {
			c.Errorf("expected error while translating %s", n)
			continue
		}
		err := rawErr.(*goose.ConversionError)
		c.Check(err.Category, Matches, `(unsupported|future)`)
		if note != nil {
			c.Check(err.Message, Matches, note.Args[0].(string))
			if !(err.Pos <= note.Pos && note.Pos <= err.End) {
				c.Errorf("error is incorrectly attributed to %s", err.GoSrcFile)
			}
		}
	}
}
