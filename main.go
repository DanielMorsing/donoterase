package main

import (
	"fmt"
	"go/build"
	"go/parser"
	"go/token"
	"go/ast"
	"flag"
	"os"
	"strings"
	
	
	"golang.org/x/tools/go/ast/astutil"
	"golang.org/x/tools/go/loader"
	"golang.org/x/tools/go/ssa/ssautil"
	"golang.org/x/tools/go/ssa"
	"golang.org/x/tools/go/pointer"
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
	conf := loader.Config{
		Build:         &build.Default,
		ParserMode: parser.ParseComments,
	}

	// Use the initial packages from the command line.
	_, err := conf.FromArgs([]string{flag.Arg(0)}, true)
	if err != nil {
		return err
	}

	// Load, parse and type-check the whole program.
	lprog, err := conf.Load()
	if err != nil {
		return err
	}
	ssaprog := ssautil.CreateProgram(lprog, ssa.GlobalDebug)
	ssaprog.BuildAll()

	const dne = "dne: "
	
	var pins []*dnepin
	for tpkg, pkg := range lprog.AllPackages {
		for _, f := range pkg.Files {
			for _, c := range f.Comments {
				ctext := c.Text()
				if strings.HasPrefix(ctext, dne) {
					ctext = ctext[len(dne):len(ctext)-1]
					// TODO: replace with own visitor so can get dne comments
					// placed on function arguments
					path, _ := astutil.PathEnclosingInterval(f, c.Pos(), c.End())
					// path is always going to be a block. (rash assumptions. Love them)
					block := path[0].(*ast.BlockStmt)
					var closestIdent *ast.Ident
					// TODO: verify that this is a []byte
					for _, s := range block.List {
						closestIdent = findClosestAssignment(closestIdent, s, c.Pos(), ctext)
					}
					if closestIdent == nil {
						fmt.Printf("%s: not found\n", lprog.Fset.Position(c.Pos()))
						continue
					}
					ssapkg := ssaprog.Package(tpkg)
					ssafunc := ssa.EnclosingFunction(ssapkg, path)
					value, _ := ssafunc.ValueForExpr(closestIdent)
				
					pins = append(pins, &dnepin{closestIdent, value})
				}
			}
		}
	}
	pconfig, err := setupPTA(ssaprog, lprog)
	if err != nil {
		return err
	}
	for _, dp := range pins {
		pconfig.AddQuery(dp.val)
	}
	var stores []store
	allf := ssautil.AllFunctions(ssaprog)
	for f := range allf {
		for _, b := range f.Blocks {
			for _, i := range b.Instrs {
				if s, _ := i.(*ssa.Store); s != nil {
					// TODO: figure out if this is the best way to find the 
					// thing pointed at by dne comment
					// TODO: handle appends.
					if b, _ := s.Addr.(*ssa.IndexAddr); b != nil {
						stores = append(stores, store{b.X, i.Pos()})
						pconfig.AddQuery(b.X)
					}
				}
			}
		}
	}
	res, err := pointer.Analyze(pconfig)
	if err != nil {
		return err
	}
	for _, dp := range pins {
		ptr := res.Queries[dp.val]
		for _, s := range stores {
			// TODO: ignore stores that cannot happen before the 
			// the pins became valid. Might not be trivially possible because
			// of the ordering of SSA being only flow dependent.
			//
			// One possibility is to rewrite the AST of the package being
			// tested to have a store in it at the point on the comment.
			// Since stores are synchronized
			// with the environment, we can just ignore all instructions that
			// are not dominated by the store instruction.
			// Need to figure out if this is feasible since most of the 
			// go/* packages are based on doing this for files on disk rather
			// than inflight use.
			p := res.Queries[s.v]
			if ptr.MayAlias(p) {
				fmt.Printf("Store detected: %s\n", lprog.Fset.Position(s.pos))
			}
		}
	}
	
	return nil
}

type dnepin struct {
	ident *ast.Ident
	val ssa.Value
}

type store struct {
	v ssa.Value
	pos token.Pos
}

// todo, figure out how to find arguments, return variables and index stuff from 
// for loops. Might be that the codegen option is the best one.
func findClosestAssignment(ident *ast.Ident, stmt ast.Stmt, cpos token.Pos, name string) *ast.Ident {
	// if we're after the comment position, don't bother
	if stmt.Pos() > cpos {
		return ident
	}
	// if we have an identifier and it is closer to the comment position than the 
	// statement, don't bother either
	if ident != nil && cpos - ident.Pos() < cpos - stmt.Pos() {
		return ident
	}

	switch n := stmt.(type) {
	case *ast.AssignStmt:
		for _, l := range n.Lhs {
			if i, _ := l.(*ast.Ident); i != nil && i.Name == name {
				return i
			}
		}
	case *ast.DeclStmt:
		if d, _ := n.Decl.(*ast.GenDecl); d != nil && d.Tok == token.VAR {
			for _, s := range d.Specs {
				for _, n := range s.(*ast.ValueSpec).Names {
					if n.Name == name {
						return n
					}
				}
			}
		}
	}
	return ident
} 


func (d *dnepin) String() string {
	return d.ident.String() + "; " + d.val.String()
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
		Mains:      mains,
	}, nil
}