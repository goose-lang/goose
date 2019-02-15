package goose_test

import (
	"bytes"
	"flag"
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"io/ioutil"
	"os"
	"path"
	"regexp"
	"strings"

	"github.com/tchajed/goose"
)

import . "gopkg.in/check.v1"

var updateGold = flag.Bool("update-gold",
	false,
	"update *.gold.v files in examples/ with current output")

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

		if *updateGold {
			expected, err := ioutil.ReadFile(goldFile)
			if err != nil || !bytes.Equal(actual, expected) {
				fmt.Fprintf(os.Stderr, "updated %s\n", goldFile)
			}
			err = ioutil.WriteFile(goldFile, actual, 0644)
			if err != nil {
				panic(err)
			}
			_ = os.Remove(path.Join(srcPath, srcDir+".actual.v"))
			continue
		}

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

type errorExpectation struct {
	Line  int
	Error string
}

type errorTestResult struct {
	Err        *goose.ConversionError
	ActualLine int
	Expected   errorExpectation
}

func getExpectedError(fset *token.FileSet, comments []*ast.CommentGroup) errorExpectation {
	errRegex := regexp.MustCompile(`ERROR ?(.*)`)
	for _, cg := range comments {
		for _, c := range cg.List {
			ms := errRegex.FindStringSubmatch(c.Text)
			if ms == nil {
				continue
			}
			expected := errorExpectation{
				Line: fset.Position(c.Pos()).Line,
			}
			// found a match
			if len(ms) > 1 {
				expected.Error = ms[1]
			}
			// only use the first ERROR
			return expected
		}
	}
	return errorExpectation{}
}

func translateErrorFile(filePath string) errorTestResult {
	fset := token.NewFileSet()
	ctx := goose.NewCtx(fset, goose.Config{})
	f, err := parser.ParseFile(fset, filePath, nil, parser.ParseComments)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		panic("test code does not parse")
	}

	err = ctx.TypeCheck("example", []*ast.File{f})
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		panic("test code does not type check")
	}

	_, err = ctx.File(f)
	if err == nil {
		return errorTestResult{Err: nil}
	}
	cerr := err.(*goose.ConversionError)
	test := errorTestResult{
		Err:        cerr,
		ActualLine: fset.Position(cerr.Pos).Line,
		Expected:   getExpectedError(fset, f.Comments),
	}
	return test
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
		tt := translateErrorFile(path.Join("testdata", n))
		if tt.Err == nil {
			c.Errorf("expected error while translating %s", n)
			continue
		}
		c.Check(tt.Err.Category, Matches, `(unsupported|future)`)
		if !strings.Contains(tt.Err.Message, tt.Expected.Error) {
			c.Errorf(`error message "%s" does not contain "%s"`,
				tt.Err.Message, tt.Expected.Error)
		}
		if tt.ActualLine > 0 && tt.ActualLine != tt.Expected.Line {
			c.Errorf("error is incorrectly attributed to %s", tt.Err.GoSrcFile)
		}
	}
}
