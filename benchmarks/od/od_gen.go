package main

import (
	"flag"
	"fmt"
)

var (
	pi    string
	n_in  int
	n_out int
	t     int
)

func print_forall() {
	for i := uint(0); i < 2; i++ {
		fmt.Printf("forall %v%v. ", pi, i)
	}
}

func main() {
	flag.StringVar(&pi, "pi", "x", "`varname`")
	flag.IntVar(&n_in, "in", 1, "`number` of atomic input propositions")
	flag.IntVar(&n_out, "out", 1, "`number` of atomic output propositions")
	flag.IntVar(&t, "t", 1, "`type` of observational determinism")
	flag.Parse()

	print_forall()
	switch t {
	case 1:
		fmt.Print("G")
		fallthrough
	case 2:
		fmt.Print("(")
		for i := 0; i < n_in; i++ {
			if i > 0 {
				fmt.Print(" & ")
			}
			fmt.Printf("(in%d_%v0 <-> in%d_%v1)", i, pi, i, pi)
		}
		fmt.Print(")=>G(")
		for i := 0; i < n_out; i++ {
			if i > 0 {
				fmt.Print(" & ")
			}
			fmt.Printf("(out%d_%v0 <-> out%d_%v1)", i, pi, i, pi)
		}
		fmt.Print(")")
	case 3:
		fmt.Print("(")
		for i := 0; i < n_out; i++ {
			if i > 0 {
				fmt.Print(" & ")
			}
			fmt.Printf("(out%d_%v0 <-> out%d_%v1)", i, pi, i, pi)
		}
		fmt.Print(") W (")
		for i := 0; i < n_in; i++ {
			if i > 0 {
				fmt.Print(" | ")
			}
			fmt.Printf("(~(in%d_%v0 <-> in%d_%v1))", i, pi, i, pi)
		}
		fmt.Print(")")
	}
}
