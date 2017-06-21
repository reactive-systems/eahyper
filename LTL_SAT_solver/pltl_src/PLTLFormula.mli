exception PLTLException of string

type formula =
  | TRUE
  | FALSE
  | AP of string
  | NOT of formula
  | X of formula
  | EV of formula
  | AW of formula
  | EQU of formula * formula
  | IMP of formula * formula
  | OR of formula * formula
  | AND of formula * formula
  | UN of formula * formula 
  | BF of formula * formula

val numberOfTypes : int
val getTypeFormula : formula -> int
val generateCompare : int list -> (formula -> formula -> int)
val aRanking : int list

val exportFormula : formula -> string
val importFormula : string -> formula
val importFormula_ic : in_channel -> formula

val sizeFormula : formula -> int

val substFormula : (string * formula) list -> formula -> formula

val nnfNeg : formula -> formula
val nnf : formula -> formula

val simplifyFormula : formula -> formula

val dest_ap : formula -> string
val dest_not : formula -> formula
val dest_x : formula -> formula
val dest_ev : formula -> formula
val dest_aw : formula -> formula
val dest_equ : formula -> formula * formula
val dest_imp : formula -> formula * formula
val dest_or : formula -> formula * formula
val dest_and : formula -> formula * formula
val dest_un : formula -> formula * formula
val dest_bf : formula -> formula * formula

val is_true : formula -> bool
val is_false : formula -> bool
val is_ap : formula -> bool
val is_not : formula -> bool
val is_x : formula -> bool
val is_ev : formula -> bool
val is_aw : formula -> bool
val is_equ : formula -> bool
val is_imp : formula -> bool
val is_or : formula -> bool
val is_and : formula -> bool
val is_un : formula -> bool
val is_bf : formula -> bool
        
val const_true : formula
val const_false : formula
val const_ap : string -> formula
val const_not : formula -> formula
val const_x : formula -> formula
val const_ev : formula -> formula
val const_aw : formula -> formula
val const_equ : formula -> formula -> formula
val const_imp : formula -> formula -> formula
val const_or : formula -> formula -> formula
val const_and : formula -> formula -> formula
val const_un : formula -> formula -> formula
val const_bf : formula -> formula -> formula

val detClosure : (formula -> formula -> int) -> formula -> formula list

type hcFormula = (hcFormula_node, formula) HashConsing.hash_consed
and hcFormula_node =
  | HCTRUE
  | HCFALSE
  | HCAP of string
  | HCNOT of string
  | HCX of hcFormula
  | HCOR of hcFormula * hcFormula
  | HCAND of hcFormula * hcFormula
  | HCUN of hcFormula * hcFormula
  | HCBF of hcFormula * hcFormula

module HcFormula : (HashConsing.S with type nde = hcFormula_node and type fml = formula)

module HcFHt : (Hashtbl.S with type key = hcFormula)

val detClosureHc : formula -> hcFormula list * hcFormula * HcFormula.t
