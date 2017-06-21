(** Common functions and data structures (e.g. bitsets)
    which are shared by most of the decision procedures.
    @author Florian Widmann
 *)


(** This value must be (smaller than or) equal to the bit width
    of the architecture on which this code is running.
 *)
let bitwidth = Sys.word_size


(** This table maps formulae (represented as integers)
    to their "types" (i.e. and, or, <>, etc;
    represented as integers).
 *)
let arrayType = ref (Array.make 0 (-1))

(** These lookup tables map formulae (represented as integers)
    to their decompositions (represented as integers).
    This is done according to the rules of the tableau procedure
    and depends on the type of the formulae.
 *)
let arrayDest1 = ref (Array.make 0 (-1))
let arrayDest2 = ref (Array.make 0 (-1))

(** This lookup table maps formulae (represented as integers)
    to their negation (in negation normal form).
 *)
let arrayNeg = ref (Array.make 0 (-1))


(** The number of nodes in a tableau.
 *)
let nodecount = ref 0

(** The longest path in a tableau.
 *)
let pathlength = ref 0

(** Counter that is used to assign unique id numbers to nodes.
 *)
let idcount = ref 0

(** Returns an unused id number.
 *)
let getNewId () =
  if !idcount < max_int then begin incr idcount; !idcount end
  else raise (Failure "Id overflow!")

(** A running number which is increased for each invocation of some functions.
    Hence each such invocation is mapped to a unique value of this variable.
    The variable is used to determine
    whether a function (e.g. detPrsEntry) has already been invoked
    with the same arguments under the same invocation of detStatusSpecial.
 *) 
let cacherun = ref 0

(** Counter that is used to assign time stamps
    reflecting the postfix order of the nodes.
 *)
let postfixcount = ref 0


(** An instantiation of a set (of the standard library)
    for formulae (in integer representation).
 *)
module FSet = Set.Make(
  struct
    type t = int
    let compare (i1 : int) i2 = compare i1 i2
  end
 )

(** An instantiation of a map (of the standard library)
    for formulae (in integer representation).
 *)
module FMap = Map.Make(
  struct
    type t = int
    let compare (i1 : int) i2 = compare i1 i2
  end
 )


(** The number of formulae which must be positive.
    The formulae are represented by the integers 0..(nrFormulae-1).
    It is assumed that formulae of the same type are grouped together
    (e.g. EX-formulae are exactly the formulae with index in [lposEX..hposEX]).
    It is further assumed that all principal formulae (e.g. or-formulae) come first,
    then come the EX-formulae, then the AX-formulae, and finally all remaining formulae.
 *)
let nrFormulae = ref (-1)

(** The lowest integer representing an EX-formula.
    If there are no EX-formulae, we distinguish two cases:
    1) If there are no principal formulae
    then it must hold lposEX = 0 and hposEX = (-1).
    2) If idx is the greatest index of a principal formulae
    then it must hold lposEX = idx + 1 and hposEX = idx.
 *)
let lposEX = ref (-1)

(** The greatest integer representing an EX-formula (see also lposEX).
 *)
let hposEX = ref (-1)

(** The greatest index in the bit vector
    that contains an EX-formula or a principal formula.
    It must be (-1) if no such formula exists.
 *)
let idxPF = ref (-1)

(** The lowest integer representing an AX-formula.
    The AX-formulae have to follow the EX-formulae directly,
    that is lposAX = hposEX + 1, even when there does not exists an AX-formula.
 *)
let lposAX = ref (-1)

(** The greatest integer representing an AX-formula.
    If there are no AX-formulae then it must hold hposAX = lposAX - 1.
 *)
let hposAX = ref (-1)

(** The integer representing the formula False.
    It must hold that !arrayNeg.(bsfalse) = bstrue.
 *)
let bsfalse = ref (-1)

(** The integer representing the formula True.
    It must hold that !arrayNeg.(bstrue) = bsfalse.
 *)
let bstrue = ref (-1)


(** Represents a set of formulae as a bit vector.
    All sets contain the formula True, that is bstrue,
    which is needed to detect whether False, that is bsfalse,
    is inserted.
 *)
type bitset = int array

(** The number of elements that are stored in one integer of the array.
    It has to be strictly smaller than the bit width of the system
    (due to the way ocaml handles integers).
 *)
let bsintsize = bitwidth - 1

(** The size of the arrays implementing the bitsets.
 *)
let bssize = ref (-1)

(** The greatest index of the arrays implementing the bitsets.
    It must hold that bssize = bsindex + 1.
 *)
let bsindex = ref (-1)

(** A dummy bitset that can be used if a bitset is needed
    before this module is initialised.
    It must never been actually used.
 *)
let dummyBS = Array.make 0 0

(** Copies the content of one bitset to another bitset.
    @param src The source bitset.
    @param trg The target bitset.
 *)
let blitBS (src : bitset) trg = Array.blit src 0 trg 0 !bssize

(** Creates a clone of a bitset.
    @param bs A bitset.
    @return A new bitset with the same content as bs.
 *)
let copyBS (bs : bitset) = Array.copy bs

(** Compares two bitsets. The order is (more or less) lexicographic.
    @param bs1 The first bitset.
    @param bs2 The second bitset.
    @param i The current index of the array.
    @return -1 if bs1 is smaller than bs2, 1 if bs1 is greater than bs2,
    and 0 if the sets are equal.
 *)
let rec intern_compBS (bs1 : bitset) bs2 i =
  if i >= 0 then
    let n1 = bs1.(i) in
    let n2 = bs2.(i) in
    if n1 = n2 then intern_compBS bs1 bs2 (pred i)
    else if n1 < n2 then (-1) else 1
  else 0

let compareBS (bs1 : bitset) bs2 = intern_compBS bs1 bs2 !bsindex

(** Computes a hash value for a bitset.
    It implements the One-at-a-Time hash invented by Bob Jenkins.
    @param bs A bitset.
    @param acc The hash value computed so far.
    @param i The current index of the array.
    @return The hash value of bs.
 *)
let rec intern_hashBS bs acc i =
  if i >= 0 then
    let acc1 = acc + bs.(i) in
    let acc2 = acc1 + (acc1 lsl 10) in
    let acc3 = acc2 lxor (acc2 lsr 6) in
    intern_hashBS bs acc3 (pred i)
  else
    let acc1 = acc + (acc lsl 3) in
    let acc2 = acc1 lxor (acc1 lsr 11) in
    acc2 + (acc lsl 15)

let hashBS bs = intern_hashBS bs 0 !bsindex

(** Tests whether a formula is an element of a set of formulae.
    @param bs A bitset of formulae.
    @param f The integer representation of a formula.
    @return True iff f is an element of bs.
 *)
let memBS bs f =
  let idx = f / bsintsize in
  let pos = f mod bsintsize in
  (bs.(idx) land (1 lsl pos)) <> 0

(** Removes a formula from a bitset.
    @param bs A bitset of formulae.
    @param f The integer representation of a formula
    which must not be bstrue.
 *)
let remBS bs f =
  let idx = f / bsintsize in
  let pos = f mod bsintsize in
  let pset = bs.(idx) in
  let pattern = (-1) lxor (1 lsl pos) in
  let npset = pset land pattern in
  if npset <> pset then bs.(idx) <- npset else ()

(** Adds a formula to a set of formulae.
    @param bs A bitset of formulae.
    @param f The integer representation of a formula that is to be added to bs.
    @return True iff inserting f leads to a new contradiction.
 *)
let addBS bs f =
  let idx = f / bsintsize in
  let pos = f mod bsintsize in
  let pset = bs.(idx) in
  let pattern = 1 lsl pos in
  let npset = pset lor pattern in
  if npset <> pset then begin
    bs.(idx) <- npset;
    let f1 = !arrayNeg.(f) in
    f1 >= 0 && f1 < !nrFormulae && memBS bs f1
  end
  else false

(** Adds a formula to a set of formulae.
    @param bs A bitset of formulae.
    @param f The integer representation of a formula that is to be added to bs.
 *)
let addBSNoChk bs f =
  let idx = f / bsintsize in
  let pos = f mod bsintsize in
  let pset = bs.(idx) in
  let pattern = 1 lsl pos in
  let npset = pset lor pattern in
  if npset <> pset then bs.(idx) <- npset else ()

(** Adds a formula to two sets of formulae
    if it is not already contained in the second one.
    @param bs A bitset of formulae.
    @param bsc The saturated bitset of bs.
    @param f The integer representation of a formula that is to be added to bs and bsc.
    @return True iff inserting f into bsc leads to a new contradiction.
 *)
let addBSc bs bsc f =
  let idx = f / bsintsize in
  let pos = f mod bsintsize in
  let psetc = bsc.(idx) in
  let pattern = 1 lsl pos in
  let npsetc = psetc lor pattern in
  if npsetc <> psetc then begin
    bsc.(idx) <- npsetc;
    bs.(idx) <- bs.(idx) lor pattern;
    let f1 = !arrayNeg.(f) in
    f1 >= 0 && f1 < !nrFormulae && memBS bsc f1
  end
  else false

(** Creates an "empty" bitset.
    @return A bitset which only contains bstrue.
 *)
let makeBS () =
  let bs = Array.make !bssize 0 in
  addBSNoChk bs !bstrue;
  bs

(** "Empties" a bitset such that it only contains bstrue.
    @param bs A bitset.
 *)
let emptyBS bs =
  Array.fill bs 0 !bssize 0;
  addBSNoChk bs !bstrue


(** Represents a set of annotated formulae as a bit vector.
    All sets contain the formula True, that is bstrue,
    which is needed to detect whether False, that is bsfalse,
    is inserted.
 *)
type annbitset = int array

(** The number of elements that are stored in one integer of the array.
    It has to be strictly smaller than the bitsize of the system
    divided by two since we need two bits per entry
    (the "strictly" is due to the way ocaml handles integers).
 *)
let annbsintsize = bsintsize / 2

(** Constant for "element not contained in annotated bitset".
 *)
let absNotIn = 0

(** Constant for "element contained but not annotated in annotated bitset".
 *)
let absUnAnn = 3

(** Constant for "element contained and annotated with 1 in annotated bitset".
 *)
let absAnn1 = 1

(** Constant for "element contained and annotated with 2 in annotated bitset".
 *)
let absAnn2 = 2

(** The size of the arrays implementing the annotated bitsets.
 *)
let abssize = ref (-1)

(** The greatest index of the arrays implementing the annotated bitsets.
    It must hold that abssize = absindex + 1.
 *)
let absindex = ref (-1)

(** A dummy annotated bitset that can be used if an annotated bitset is needed
    before this module is initialised.
    It must never been actually used.
 *)
let dummyABS = Array.make 0 0

(** Copies the content of one annotated bitset to another annotated bitset.
    @param src The source annotated bitset.
    @param trg The target annotated bitset.
 *)
let blitABS (src : annbitset) trg = Array.blit src 0 trg 0 !abssize

(** Creates a clone of an annotated bitset.
    @param abs An annotated bitset.
    @return A new annotated bitset with the same content as abs.
 *)
let copyABS (abs : annbitset) = Array.copy abs

(** Compares two annotated bitsets. The order is (more or less) lexicographic.
    @param abs1 The first annotated bitset.
    @param abs2 The second annotated bitset.
    @param i The current index of the array.
    @return -1 if abs1 is smaller than abs2, 1 if abs1 is greater than abs2,
    and 0 if the sets are equal.
 *)
let rec intern_compABS (abs1 : annbitset) abs2 i =
  if i >= 0 then
    let n1 = abs1.(i) in
    let n2 = abs2.(i) in
    if n1 = n2 then intern_compABS abs1 abs2 (pred i)
    else if n1 < n2 then (-1) else 1
  else 0

let compareABS (abs1 : annbitset) abs2 = intern_compABS abs1 abs2 !absindex

(** Computes a hash value for an annotated bitset.
    It implements the One-at-a-Time hash invented by Bob Jenkins.
    @param abs An annotated bitset.
    @param acc The hash value computed so far.
    @param i The current index of the array.
    @return The hash value of bs.
 *)
let rec intern_hashABS abs acc i =
  if i >= 0 then
    let acc1 = acc + abs.(i) in
    let acc2 = acc1 + (acc1 lsl 10) in
    let acc3 = acc2 lxor (acc2 lsr 6) in
    intern_hashABS abs acc3 (pred i)
  else
    let acc1 = acc + (acc lsl 3) in
    let acc2 = acc1 lxor (acc1 lsr 11) in
    acc2 + (acc lsl 15)

let hashABS abs = intern_hashABS abs 0 !absindex

(** Tests whether a formula is an element of an annotated set of formulae
    and, if yes, determines its annotation.
    @param abs An annotated bitset of formulae.
    @param f The integer representation of a formula.
    @return The appropriate return code
    (one of absNotIn, absUnAnn, absAnn1, absAnn2).
 *)
let getAnnABS abs f =
  let idx = f / annbsintsize in
  let pos = (f mod annbsintsize) lsl 1 in
  (abs.(idx) lsr pos) land 3

(** Sets the annotation status of a formula in an annotated set of formulae.
    The old annotation status is overridden.
    @param abs An annotated bitset of formulae.
    @param f The integer representation of a formula
    whose annotation status is to be set.
    @param ann The (new) annotation status of f
    (must be one of absNotIn, absUnAnn, absAnn1, absAnn2).
 *)
let setAnnABS abs f ann =
  let idx = f / annbsintsize in
  let pos = (f mod annbsintsize) lsl 1 in
  let pset = abs.(idx) in
  let pset1 = pset land ((-1) lxor (3 lsl pos)) in
  let pattern = (ann land 3) lsl pos in
  let npset = pset1 lor pattern in
  if npset <> pset then abs.(idx) <- npset else ()

(** Tests whether a formula is an element of an annotated set of formulae.
    @param abs An annotated bitset of formulae.
    @param f The integer representation of a formula.
    @return True iff f is an element of abs (annotated or not).
 *)
let memABS abs f =
  let idx = f / annbsintsize in
  let pos = (f mod annbsintsize) lsl 1 in
  (abs.(idx) land (3 lsl pos)) <> 0

(** Removes a formula from an annotated bitset.
    @param abs An annotated bitset of formulae.
    @param f The integer representation of a formula
    which must not be bstrue.
 *)
let remABS abs f =
  let idx = f / annbsintsize in
  let pos = (f mod annbsintsize) lsl 1 in
  let pset = abs.(idx) in
  let pattern = (-1) lxor (3 lsl pos) in
  let npset = pset land pattern in
  if npset <> pset then abs.(idx) <- npset else ()

(** Adds a formula without annotation to an annotated set of formulae
    if it is not already contained in the set (annotated or not).
    @param abs An annotated bitset of formulae.
    @param f The integer representation of a formula that is to be added to abs.
    @return True iff inserting f leads to a new contradiction.
 *)
let addABS abs f =
  let idx = f / annbsintsize in
  let pos = (f mod annbsintsize) lsl 1 in
  let pset = abs.(idx) in
  let pattern = 3 lsl pos in
  if (pset land pattern) = 0 then begin
    abs.(idx) <- pset lor pattern;
    let f1 = !arrayNeg.(f) in
    f1 >= 0 && f1 < !nrFormulae && memABS abs f1
  end
  else false

(** Adds a formula to two sets of formulae
    if it is not already contained in the second one.
    @param bs A bitset of formulae.
    @param abs An annotated bitset of formulae.
    @param f The integer representation of a formula that is to be added to bs and abs.
    @return True iff inserting f into abs leads to a new contradiction.
 *)
let addBSa bs abs f =
  let idx = f / annbsintsize in
  let pos = (f mod annbsintsize) lsl 1 in
  let apset = abs.(idx) in
  let pattern = 3 lsl pos in
  if (apset land pattern) = 0 then begin
    abs.(idx) <- apset lor pattern;
    addBSNoChk bs f;
    let f1 = !arrayNeg.(f) in
    f1 >= 0 && f1 < !nrFormulae && memABS abs f1
  end
  else false

(** Creates an "empty" annotated bitset.
    @return An annotated bitset which only contains bstrue (unannotated).
 *)
let makeABS () =
  let abs = Array.make !abssize 0 in
  setAnnABS abs !bstrue absUnAnn;
  abs

(** "Empties" an annotated bitset such that it only contains bstrue (unannotated).
    @param abs An annotated bitset.
 *)
let emptyABS abs =
  Array.fill abs 0 !abssize 0;
  setAnnABS abs !bstrue absUnAnn

(** Copies the content of an annotated bitset to a bitset.
    @param src The annotated source bitset.
    @param trg The target bitset.
 *)
let blitBSa (src : annbitset) (trg : bitset) =
  for i = 0 to pred !nrFormulae do
    if memABS src i then addBSNoChk trg i else ()
  done


(** Selects a principal formula from a set of formulae if possible.
    @param bs A bitset of formulae.
    @param maxpf The greatest integer that represents a principal formula.
    @param bnd The greatest index in the array that contains a principal formula.
    @param i The current index of the array.
    @return -1 iff no principal formula is found,
    the principal formula otherwise.
 *)
let rec intern_getPF bs maxpf bnd i =
  if i <= bnd then
    let n = bs.(i) in
    if n = 0 then intern_getPF bs maxpf bnd (succ i)
    else
      let j = ref 0 in
      let notfound = ref true in
      let _ =
        while !notfound do
          if (n land (1 lsl !j)) = 0 then incr j
          else notfound := false
        done
      in
      let res = i * bsintsize + !j in
      if res <= maxpf then res else (-1)
  else (-1)

let getPFinclEX bs = intern_getPF bs !hposEX !idxPF 0

let getPFexclEX bs = intern_getPF bs (pred !lposEX) !idxPF 0


(** Constructs a list of all EX-formulae of a set of formulae.
    @param bs The bitset of formulae.
    @param bnd The greatest integer representing an EX-formula.
    @param acc A list of EX-formulae gathered till now.
    @param i The current index of the array.
    @return A list of all EX-formulae f (in decreasing order) in bs.
 *)
let rec intern_mkEXList bs bnd acc i =
  if i >= bnd then
    if memBS bs i then intern_mkEXList bs bnd (i::acc) (pred i) 
    else intern_mkEXList bs bnd acc (pred i)
  else acc

let mkEXList bs = intern_mkEXList bs !lposEX [] !hposEX

(** Constructs a list of all EX-formulae of a set of annotated formulae.
    @param abs The annotated bitset of formulae.
    @param bnd The greatest integer representing an EX-formula.
    @param acc A list of EX-formulae gathered till now.
    @param i The current index of the array.
    @return A list of all EX-formulae f (in decreasing order) in abs.
 *)
let rec intern_mkEXListAnn abs bnd acc i =
  if i >= bnd then
    if memABS abs i then intern_mkEXListAnn abs bnd (i::acc) (pred i) 
    else intern_mkEXListAnn abs bnd acc (pred i)
  else acc

let mkEXListAnn abs = intern_mkEXListAnn abs !lposEX [] !hposEX


(** Prints a "collection" as a set.
    @param ps A string prefixing the set.
    @param f A function converting the collection c into a list of strings.
    @param c A "collection".
    @return If f c = [a1, ..., an] then the resulting string
    will be "ps { a1, ..., an }".
 *)
let exportAsSet ps f c =
  let rec fold acc = function
    | [] -> acc
    | [h] -> acc ^ h
    | h::t -> fold (acc ^ h ^ ", ") t
  in
  ps ^ "{ " ^ (fold "" (f c)) ^ " }"

(** Converts a set of formulae into a list of strings
    where each string represents one formula of the set.
    @param expF A function which converts the formula in integer
    representations into a readable string.
    @param bs A bitset of formulae.
    @return A list of string representations of the formulae in bs.
 *)
let exportFSet expF bs =
  let res = ref [] in
  for i = 0 to pred !nrFormulae do
    if memBS bs i then res := (expF i)::!res else ()
  done;
  !res

(** Converts an annotated set of formulae into a list of strings
    where each string represents one formula of the set and its annotation.
    @param expF A function which converts the formula in integer
    representations into a readable string.
    @param abs An annotated bitset of formulae.
    @return A list of string representations of the formulae in abs
    and their annotation.
 *)
let exportAnnFSet expF abs =
  let res = ref [] in
  for i = 0 to pred !nrFormulae do
    let ann = getAnnABS abs i in
    if ann <> absNotIn then
      let fstr = expF i in
      let afstr =
        if ann = absAnn1 then fstr ^ "(1)"
        else if ann = absAnn2 then fstr ^ "(2)"
        else fstr
      in
      res := afstr::!res
    else ()
  done;
  !res


(** Initialises the global fields of this module
    with the exception of the tables.
    This procedure must only be invoked once.
    @param size The number of formulae which must be positive (cf. nrFormulae).
    @param bsf cf. bsfalse
    @param bst cf. bstrue
    @param lEX cf. lposEX
    @param nrEX The number of EX-formulae.
    @param nrAX The number of AX-formulae.
 *)
let initMisc size bsf bst lEX nrEX nrAX =
  assert (size > 0);
  nrFormulae := size;
  bssize := (size - 1) / bsintsize + 1;
  assert (!bssize <= Sys.max_array_length);
  bsindex := pred !bssize;
  abssize := (size - 1) / annbsintsize + 1;
  assert (!abssize <= Sys.max_array_length);
  absindex := pred !abssize;
  bsfalse := bsf;
  bstrue := bst;
  lposEX := lEX;
  hposEX := !lposEX + nrEX - 1;
  idxPF := if !hposEX >= 0 then !hposEX / bsintsize else (-1);
  lposAX := succ !hposEX;
  hposAX := !lposAX + nrAX - 1;
  nodecount := 0;
  pathlength := 0;
  idcount := 0;
  cacherun := 0;
  postfixcount := 0
