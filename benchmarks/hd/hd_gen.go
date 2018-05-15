package main

import (
	"flag"
	"fmt"
)

const ()

var (
	pi    string
	d     int
	n_in  uint
	n_out uint
)

func print_forall() {
	for i := uint(0); i < 2; i++ {
		fmt.Printf("forall %v%v. ", pi, i)
	}
}
func print_in_not_equiv() func() {
	return func() {
		fmt.Printf("(")
		for in := uint(0); in < n_in; in++ {
			if in > 0 {
				fmt.Printf(" | ")
			}
			fmt.Printf("!(in%v_%v%v <-> in%v_%v%v)", in, pi, 0, in, pi, 1)
		}
		fmt.Printf(")")
	}
}
func print_out_equiv() func() {
	return func() {
		fmt.Printf("(")
		for out := uint(0); out < n_out; out++ {
			if out > 0 {
				fmt.Printf(" & ")
			}
			fmt.Printf("(out%v_%v%v <-> out%v_%v%v)", out, pi, 0, out, pi, 1)
		}
		fmt.Printf(")")
	}
}
func print_out_not_equiv() func() {
	return func() {
		fmt.Printf("(")
		for out := uint(0); out < n_out; out++ {
			if out > 0 {
				fmt.Printf(" | ")
			}
			fmt.Printf("!(out%v_%v%v <-> out%v_%v%v)", out, pi, 0, out, pi, 1)
		}
		fmt.Printf(")")
	}
}
func print_next(f func()) func() {
	return func() {
		fmt.Printf("X(")
		f()
		fmt.Printf(")")
	}
}
func print_finally(f func()) func() {
	return func() {
		fmt.Printf("F(")
		f()
		fmt.Printf(")")
	}
}
func print_not(f func()) func() {
	return func() {
		fmt.Printf("!(")
		f()
		fmt.Printf(")")
	}
}
func print_impl(f, g func()) func() {
	return func() {
		fmt.Printf("(")
		f()
		fmt.Printf(" -> ")
		g()
		fmt.Printf(")")
	}
}
func print_and(f, g func()) func() {
	return func() {
		fmt.Printf("(")
		f()
		fmt.Printf(" & ")
		g()
		fmt.Printf(")")
	}
}
func print_weakuntil(f, g func()) func() {
	return func() {
		fmt.Printf("(")
		f()
		fmt.Printf(" W ")
		g()
		fmt.Printf(")")
	}
}

func print_ham(d int) func() {
	return func() {
		if d == -1 {
			fmt.Printf("False")
		} else {
			print_weakuntil(print_out_equiv(), print_and(print_out_not_equiv(), print_next(print_ham(d-1))))()
		}
	}
}

func main() {
	flag.StringVar(&pi, "pi", "x", "`varname`")
	flag.IntVar(&d, "d", 0, "`d`")
	flag.UintVar(&n_in, "in", 1, "`n_in`")
	flag.UintVar(&n_out, "out", 1, "`n_out`")
	flag.Parse()

	print_forall()
	print_impl(print_finally(print_in_not_equiv()), print_not(print_ham(d-1)))()
}
