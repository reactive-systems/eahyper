val arrayType : (int array) ref
val arrayDest1 : (int array) ref
val arrayDest2 : (int array) ref
val arrayNeg : (int array) ref

val nodecount : int ref
val pathlength : int ref
val getNewId : unit -> int
val cacherun : int ref
val postfixcount : int ref

module FSet : Set.S with type elt = int
module FMap : Map.S with type key = int

val nrFormulae : int ref
val lposEX : int ref
val hposEX : int ref
val lposAX : int ref
val hposAX : int ref
val bsfalse : int ref
val bstrue : int ref

type bitset
val dummyBS : bitset
val makeBS : unit -> bitset
val blitBS : bitset -> bitset -> unit
val copyBS : bitset -> bitset
val emptyBS : bitset -> unit
val compareBS : bitset -> bitset -> int
val hashBS : bitset -> int
val memBS : bitset -> int -> bool
val remBS : bitset -> int -> unit
val addBS : bitset -> int -> bool
val addBSNoChk : bitset -> int -> unit
val addBSc : bitset -> bitset -> int -> bool

type annbitset
val absNotIn : int
val absUnAnn : int
val absAnn1 : int
val absAnn2 : int
val dummyABS : annbitset
val makeABS : unit -> annbitset
val blitABS : annbitset -> annbitset -> unit
val copyABS : annbitset -> annbitset
val emptyABS : annbitset -> unit
val compareABS : annbitset -> annbitset -> int
val hashABS : annbitset -> int
val getAnnABS : annbitset -> int -> int
val setAnnABS : annbitset -> int -> int -> unit
val memABS : annbitset -> int -> bool
val remABS : annbitset -> int -> unit
val addABS : annbitset -> int -> bool
val addBSa : bitset -> annbitset -> int -> bool
val blitBSa : annbitset -> bitset -> unit
val getPFinclEX : bitset -> int
val getPFexclEX : bitset -> int

val mkEXList : bitset -> int list
val mkEXListAnn : annbitset -> int list

val exportAsSet : string -> ('a -> string list) -> 'a -> string
val exportFSet : (int -> string) -> bitset -> string list
val exportAnnFSet : (int -> string) -> annbitset -> string list

val initMisc : int -> int -> int -> int -> int -> int -> unit
