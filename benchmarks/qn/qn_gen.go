package main

import (
	"flag"
	"fmt"
)

var (
	pi    string
	c     uint
	n_in  uint
	n_out uint
)

func print_forall() {
	for i := uint(0); i <= c; i++ {
		fmt.Printf("forall %v%v. ", pi, i)
	}
}
func print_in_equiv(i uint) func() {
	return func() {
		for in := uint(0); in < n_in; in++ {
			if in > 0 {
				fmt.Printf(" & ")
			}
			fmt.Printf("(in%v_%v%v <-> in%v_%v%v)", in, pi, i, in, pi, 0)
		}
	}
}
func print_out_not_equiv(i, j uint) func() {
	return func() {
		for out := uint(0); out < n_out; out++ {
			if out > 0 {
				fmt.Printf(" | ")
			}
			fmt.Printf("!(out%v_%v%v <-> out%v_%v%v)", out, pi, i, out, pi, j)
		}
	}
}
func print_finally(f func()) func() {
	return func() {
		fmt.Printf("F(")
		f()
		fmt.Printf(")")
	}
}
func print_glob(f func()) func() {
	return func() {
		fmt.Printf("G(")
		f()
		fmt.Printf(")")
	}
}
func print_not(f func()) func() {
	return func() {
		fmt.Printf("~(")
		f()
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
func print_left() func() {
	return func() {
		for i := uint(0); i <= c; i++ {
			if i > 0 {
				fmt.Printf(" & ")
			}
			print_glob(print_in_equiv(i))()
		}
	}
}
func print_right() func() {
	return func() {
		for i := uint(0); i <= c; i++ {
			for j := uint(0); j <= c; j++ {
				if i == j {
					continue
				}
				if !(i == 0 && j == 1) {
					fmt.Printf(" & ")
				}
				print_finally(print_out_not_equiv(i, j))()
			}
		}
	}
}
func main() {
	flag.StringVar(&pi, "pi", "x", "`varname`")
	flag.UintVar(&c, "c", 0, "`c`")
	flag.UintVar(&n_in, "in", 1, "`n_in`")
	flag.UintVar(&n_out, "out", 1, "`n_out`")
	flag.Parse()

	print_forall()
	print_not(print_and(print_left(), print_right()))()
}
