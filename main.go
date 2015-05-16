package main

import (
	"flag"
	"fmt"
	"go/ast"
	"go/build"
	"go/parser"
	"go/token"
	"os"
	"path/filepath"
	"strings"

	"golang.org/x/tools/go/ast/astutil"
	"golang.org/x/tools/go/loader"
	"golang.org/x/tools/go/pointer"
	"golang.org/x/tools/go/ssa"
	"golang.org/x/tools/go/types"
)

func fatalln(i ...interface{}) {
	fmt.Fprintln(os.Stderr, i...)
	os.Exit(1)
}

func main() {
	flag.Parse()
	if flag.NArg() != 1 {
		fatalln("need scope argument")
	}
	err := donoterase()
	if err != nil {
		fatalln(err)
	}
}

func donoterase() error {

	prog, err := parseProgram(flag.Args())
	if err != nil {
		fatalln(err)
	}

	var exprs []*queryExpr
	for _, pkg := range prog.packages {
		if len(pkg.annotations) > 0 {
			exprs, err = addinstrumentation(exprs, pkg, prog.fset)
		}
	}
	// addinstrumentation will have added a call to a function literal,
	// which is given the expression as a parameter. This makes it possible for us
	// to ignore stores which only happen strictly before the annotation
	// TODO: actually do this
	imp := importer{
		prog: prog,
		checker: types.Config{
			Packages: make(map[string]*types.Package),
		},
	}
	imp.checker.Import = imp.importfunc

	// because we disallow cyclic and unused imports, we can be sure that
	// by just typechecking the packages given on the flags that we end up with
	// a complete program
	//
	// Use the importfunc off the importer to bootstrap this
	for _, s := range flag.Args() {
		_, err := imp.importfunc(imp.checker.Packages, s)
		// TODO: figure out what to do when failing to typecheck an
		// instrumented package. Most likely invalid expression
		if err != nil {
			fatalln(err)
		}
	}
	sprog := ssa.NewProgram(prog.fset, ssa.GlobalDebug)
	for _, pkg := range prog.packages {
		if pkg.pkg.ImportPath != "unsafe" {
			sprog.CreatePackage(pkg.typesPkg, pkg.files, &pkg.info, true)
		}
	}
	sprog.BuildAll()

	return nil
}

type importer struct {
	prog    *program
	checker types.Config
}

// Load on demand rather than the fancy concurrent load in go/loader. This package is meant for
// non-interactive use anyway, so probably not a big deal (famous last words)
func (imp *importer) importfunc(impmap map[string]*types.Package, path string) (*types.Package, error) {
	if path == "unsafe" {
		return types.Unsafe, nil
	}
	if p, ok := impmap[path]; ok {
		return p, nil
	}
	pkg, ok := imp.prog.packages[path]
	if !ok {
		panic("unexpected package " + path)
	}
	if pkg.typesPkg == nil {
		pkg.info = types.Info{
			Types:      make(map[ast.Expr]types.TypeAndValue),
			Defs:       make(map[*ast.Ident]types.Object),
			Uses:       make(map[*ast.Ident]types.Object),
			Implicits:  make(map[ast.Node]types.Object),
			Scopes:     make(map[ast.Node]*types.Scope),
			Selections: make(map[*ast.SelectorExpr]*types.Selection),
		}
		pkg.typesPkg, pkg.err = imp.checker.Check(path, imp.prog.fset, pkg.files, &pkg.info)
		impmap[path] = pkg.typesPkg
		if pkg.err == nil {
			pkg.typesPkg.MarkComplete()
		}
		fmt.Println(path)
	}
	return pkg.typesPkg, pkg.err
}

// Create a pointer.Config whose scope is the initial packages of lprog
// and their dependencies.
func setupPTA(prog *ssa.Program, lprog *loader.Program) (*pointer.Config, error) {
	// TODO(adonovan): the body of this function is essentially
	// duplicated in all go/pointer clients.  Refactor.

	// DMO: HOORAY ANOTHER ONE

	// For each initial package (specified on the command line),
	// if it has a main function, analyze that,
	// otherwise analyze its tests, if any.
	var testPkgs, mains []*ssa.Package
	for _, info := range lprog.InitialPackages() {
		initialPkg := prog.Package(info.Pkg)

		// Add package to the pointer analysis scope.
		if initialPkg.Func("main") != nil {
			mains = append(mains, initialPkg)
		} else {
			testPkgs = append(testPkgs, initialPkg)
		}
	}
	if testPkgs != nil {
		if p := prog.CreateTestMainPackage(testPkgs...); p != nil {
			mains = append(mains, p)
		}
	}
	if mains == nil {
		return nil, fmt.Errorf("analysis scope has no main and no tests")
	}
	return &pointer.Config{
		Mains: mains,
	}, nil
}

const dne = "dne: "

// finds packages imported by initialpkg
func parseProgram(initialpkg []string) (*program, error) {
	pkgs := make(map[string]*build.Package)
	for _, s := range initialpkg {
		pkg, err := build.Import(s, "", 0)
		if err != nil {
			return nil, fmt.Errorf("couldn't import %s: %s", s, err.Error())
		}
		pkgs[s] = pkg
	}
	// Find all dependencies imported.
	// This is technically O(n^2) time, but it's easy
	// and n is small
	for {
		importAdded := false
		for _, pkg := range pkgs {
			for _, imp := range pkg.Imports {
				if _, found := pkgs[imp]; found {
					continue
				}
				// found an import that hasn't been pull in yet.
				pkg, err := build.Import(imp, "", 0)
				if err != nil {
					return nil, fmt.Errorf("couldn't import %s: %s", imp, err.Error())
				}
				pkgs[imp] = pkg
				importAdded = true
			}
		}
		if !importAdded {
			break
		}
	}
	ret := &program{
		packages: make(map[string]*pkg),
	}
	fset := token.NewFileSet()
	ret.fset = fset
	// ok found all the packages. Now scan them for dne comments
	for s, p := range pkgs {
		var ann pkg
		for _, s := range p.GoFiles {
			f, annotations, err := parseFile(filepath.Join(p.Dir, s), fset)
			if err != nil {
				return nil, fmt.Errorf("couldn't parse %s: %s", s, err.Error())
			}
			ann.files = append(ann.files, f)
			for _, a := range annotations {
				ann.annotations = append(ann.annotations, &annotation{f, a})
			}

		}
		for _, s := range p.CgoFiles {
			f, annotations, err := parseFile(filepath.Join(p.Dir, s), fset)
			if err != nil {
				return nil, err
			}
			ann.files = append(ann.files, f)
			for _, a := range annotations {
				ann.annotations = append(ann.annotations, &annotation{f, a})
			}
		}
		ann.pkg = p
		ret.packages[s] = &ann
	}
	return ret, nil
}

func parseFile(s string, fset *token.FileSet) (*ast.File, []*ast.CommentGroup, error) {
	var ann []*ast.CommentGroup
	f, err := parser.ParseFile(fset, s, nil, parser.ParseComments)
	if err != nil {
		return nil, nil, err
	}
	for _, c := range f.Comments {
		if strings.HasPrefix(c.Text(), dne) {
			ann = append(ann, c)
		}
	}
	return f, ann, nil
}

type program struct {
	// fileset used to parse this program
	fset *token.FileSet
	// entire set of packages in this program
	packages map[string]*pkg
}

type pkg struct {
	pkg         *build.Package
	files       []*ast.File
	err         error
	typesPkg    *types.Package
	info        types.Info
	annotations []*annotation
}

type annotation struct {
	file    *ast.File
	comment *ast.CommentGroup
}

type queryExpr struct {
	expr    ast.Expr
	funcLit *ast.FuncLit
	pos     token.Pos
	astpath []ast.Node
}

func addinstrumentation(queryExprs []*queryExpr, pkg *pkg, fset *token.FileSet) ([]*queryExpr, error) {
	for _, c := range pkg.annotations {
		ctext := c.comment.Text()
		path, _ := astutil.PathEnclosingInterval(c.file, c.comment.Pos(), c.comment.End())
		bstmt, ok := path[0].(*ast.BlockStmt)
		if !ok {
			return nil, fmt.Errorf("%s: comment is outside function", fset.Position(c.comment.Pos()).String())
		}
		// ok we have the block where we need to inject the statement
		// now find the statement where we need to add it
		closestIndex := 0
		for i, stmt := range bstmt.List {
			closestIndex = i
			if stmt.Pos() >= c.comment.Pos() {
				break
			}
		}
		cexpr, err := parser.ParseExpr(ctext[len(dne):])
		if err != nil {
			return nil, fmt.Errorf("%s: couldn't parse expression %s", fset.Position(c.comment.Pos()).String(), err.Error())
		}
		// make a call to a function literal
		functype := &ast.FuncType{
			Params: &ast.FieldList{
				List: []*ast.Field{
					&ast.Field{
						Type: &ast.InterfaceType{
							Methods: new(ast.FieldList),
						},
					},
				},
			},
		}
		funclit := &ast.FuncLit{
			Type: functype,
			Body: new(ast.BlockStmt),
		}
		funccall := &ast.CallExpr{
			Fun:  funclit,
			Args: []ast.Expr{cexpr},
		}
		newlist := make([]ast.Stmt, len(bstmt.List)+1)
		copy(newlist, bstmt.List[:closestIndex])
		newlist[closestIndex] = &ast.ExprStmt{X: funccall}
		copy(newlist[closestIndex+1:], bstmt.List[closestIndex:])
		bstmt.List = newlist
		queryExprs = append(queryExprs, &queryExpr{cexpr, funclit, c.comment.Pos(), path})
	}
	return queryExprs, nil
}
