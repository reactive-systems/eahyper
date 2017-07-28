# EAHyper - A Satisfiability Solver for Hyperproperties

*EAHyper* is a satisfiability solver for hyperproperties expressed in the decidable fragment of HyperLTL.

See also https://www.react.uni-saarland.de/tools/eahyper/.

Copyright © 2017 Christopher Hahn, Marvin Stenger ([Reactive Systems Group](https://www.react.uni-saarland.de/) @ [Saarland University](http://www.uni-saarland.de/nc/en/home.html))

### Background
Hyperproperties generalize properties of individual computation traces in that they relate such traces to each other. This is needed to express information flow security policies, such as observational determinism: A systems behavior should appear to be deterministic to an external observer, i.e., there should be no information leakage of certain secrets into the public domain.

HyperLTL, which extends linear-time temporal logic (LTL) with explicit trace quantification, is a recently introduced temporal logic capable of formalizing many hyperproperties of interest. However, formalizing hyperproperties in HyperLTL can be error-prone, since we have to consider multiple traces at the same time.

### Applications
*EAHyper* can be used to automatically detect specifications which are vacuously true or inconsistent and
to check implication and equivalence between multiple formalizations of the same requirement.

With *EAHyper*, an overhead in verification processes, such as model checking (check out [MCHyper](https://www.react.uni-saarland.de/tools/mchyper/)) or monitoring, may be avoided by detecting erroneous or redundant specifications reliably and easily at an early stage during the verification process. *EAHyper* can also be used to understand formalized hyperproperties better, for example, the many different variations of information flow policies considered by the security community.

#### Demo
Try *EAHyper* directly in our [online interface](https://www.react.uni-saarland.de/tools/online/EAHyper/).

### Download and Install

#### Binary Distribution

We preinstalled *EAHyper* on a [virtual machine](https://www.dropbox.com/s/cs0el0013b9z4ms/eahyper_ubuntu.ova?dl=0) including the corresponding benchmarks given in [[FHS17]](https://www.react.uni-saarland.de/publications/FHS17.html).
You can import this virtual machine by using [VirtualBox](https://www.virtualbox.org/).

#### Install from Source

1. Fulfill dependencies:
	- [Git](https://git-scm.com/)
	- [OCaml](https://ocaml.org/)
	- [Menhir](http://gallium.inria.fr/~fpottier/menhir/)
	- [zlib (dev version)](https://zlib.net/)
	- [Go (only needed if you intend to run our benchmarks)](https://golang.org)
2. Clone this repository:
	```
	git clone https://github.com/reactive-systems/eahyper
	```

4. Build *EAHyper*:
	```
	cd eahyper
	make
	```
5. (Optional) Build benchmarks:
	```
	make benchmarks
	```
6. (Optional) Run demo to see if everything works properly:
	```
	make demo
	```
