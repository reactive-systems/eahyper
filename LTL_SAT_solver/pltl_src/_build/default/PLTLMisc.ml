(** Common functions and data structures
    which are shared by the decision procedures for PLTL-satisfiability.
    @author Florian Widmann
 *)


module P = PLTLFormula
module HC = HashConsing


open MiscSolver


(** The integer representation of EX True.
 *)
let fxtrue = ref (-1)

(** This lookup table maps integers (representing formulae)
    to their corresponding formulae.
 *)
let arrayFormula = ref (Array.make 0 P.TRUE)

(** This lookup table stores for each integer (representing a formula)
    whether the formula is an eventuality,
    that is of the form (f1 U f2) or X(f1 U f2).
 *)
let arrayEventuality = ref (Array.make 0 false)


(** The lowest integer representing a UN-formula.
 *)
let lposUN = ref (-1)

(** The greatest integer representing a UN-formula.
 *)
let hposUN = ref (-1)


(** Tests whether a formula is an element of a set of formulae.
    An and-like formula is considered to be in the set
    if both direct subformulae are in the set.
    An or-like formula is considered to be in the set
    if some direct subformulae is in the set.
    This applies recursively.
    @param fsc A bitset of formulae.
    @param f The integer representation of a formula.
    @return True iff f is an element of fsc.
 *)
let rec containsFormula fsc f = 
  match !arrayType.(f) with
  | 6
  | 9
  | 8 ->
      (containsFormula fsc !arrayDest1.(f) &&
       containsFormula fsc !arrayDest2.(f))
  | 5
  | 7 ->
      (memBS fsc f ||
      containsFormula fsc !arrayDest1.(f) ||
      containsFormula fsc !arrayDest2.(f))
  | _ -> memBS fsc f


(** Adds a formula to a set of formulae.
    For and-like formulae the corresponding decompositions
    are inserted instead (this is done recursively).
    @param fs A bitset containing all formulae in fsc
    which still might have to be decomposed.
    @param fsc A bitset of formulae.
    @param f The integer representation of a formula which is to be added to fsc.
    @return True iff inserting f or one of its decompositions (if applicable)
    into fsc causes a contradiction.
    In this case, the states of fs and fsc are undefined.
 *)
let rec intern_insertFormula fs fsc f =
  match !arrayType.(f) with
  | 6
  | 9
  | 8 ->
      (intern_insertFormula fs fsc !arrayDest1.(f) ||
      intern_insertFormula fs fsc !arrayDest2.(f))
  | _ -> addBSc fs fsc f

let insertFormula fs fsc f =
  if intern_insertFormula fs fsc f then true
  else
    let fneg = !arrayNeg.(f) in
    (fneg >= 0 && containsFormula fsc fneg)

(** Adds a formula to a set of formulae.
    For and-like formulae the corresponding decompositions
    are inserted instead (this is done recursively).
    @param fs A bitset of formulae.
    @param f The integer representation of a formula which is to be added to fs.
    @return True iff inserting f or one of its decompositions (if applicable)
    into fs causes a contradiction.
    In this case, the state of fs is undefined.
 *)
let rec intern_insertFormulaNS fs f =
  match !arrayType.(f) with
  | 6
  | 9
  | 8 ->
      (intern_insertFormulaNS fs !arrayDest1.(f) ||
      intern_insertFormulaNS fs !arrayDest2.(f))
  | _ -> addBS fs f

let insertFormulaNS fs f =
  if intern_insertFormulaNS fs f then true
  else
    let fneg = !arrayNeg.(f) in
    (fneg >= 0 && containsFormula fs fneg)


(** Adds all X-formulae of a set to another set
    after stripping the outermost X.
    @param fsX The bitset of formulae containing the X-formulae.
    @param fs A bitset containing all formulae in fsc
    which still might have to be decomposed.
    @param fsc The bitset to which the stripped X-formulae are added.
    @param bnd The greatest integer representing an X-formula.
    @param i The current index of the array.
    @return True iff adding the formulae to fsc caused a contradiction.
    In this case, fsc may not contain all stripped X-formulae.
 *)
let rec intern_mkXSet fsX fs fsc bnd i =
  if i <= bnd then
    if memBS fsX i then
      if insertFormula fs fsc !arrayDest1.(i) then true
      else intern_mkXSet fsX fs fsc bnd (succ i)
    else intern_mkXSet fsX fs fsc bnd (succ i)
  else false

let mkXSet fsX fs fsc = intern_mkXSet fsX fs fsc !hposEX !lposEX

(** Adds all X-formulae of a set to another set
    after stripping the outermost X.
    @param fsX The bitset of formulae containing the X-formulae.
    @param fs The bitset to which the stripped X-formulae are added.
    @param bnd The greatest integer representing a []-formula.
    @param i The current index of the array.
    @return True iff adding the formulae to fs caused a contradiction.
    In this case, fs may not contain all stripped [ap]-formulae.
 *)
let rec intern_mkXSetNS fsX fs bnd i =
  if i <= bnd then
    if memBS fsX i then
      if insertFormulaNS fs !arrayDest1.(i) then true
      else intern_mkXSetNS fsX fs bnd (succ i)
    else intern_mkXSetNS fsX fs bnd (succ i)
  else false

let mkXSetNS fsX fs = intern_mkXSetNS fsX fs !hposEX !lposEX


(** Initialises the arrays for a formula and its integer representation.
    @param ht A hashtable that maps formulae to their integer representation.
    @param f A formula in negation normal form.
    @param n The integer representation of f.
    @raise P.PLTLException if f is not in negation normal form.
 *)
let initTables ht f n = 
  let fneg = P.nnfNeg f in
  !arrayFormula.(n) <- f;
  if Hashtbl.mem ht fneg then !arrayNeg.(n) <- Hashtbl.find ht fneg else ();
  match f with
  | P.TRUE -> !arrayType.(n) <- 0
  | P.FALSE -> !arrayType.(n) <- 1
  | P.AP _ -> !arrayType.(n) <- 2;
  | P.NOT (P.AP _) -> !arrayType.(n) <- 3;
  | P.X f1 ->
      !arrayType.(n) <- 4;
      !arrayDest1.(n) <- Hashtbl.find ht f1;
      !arrayEventuality.(n) <- P.is_un f1
  | P.AW f1 ->
      !arrayType.(n) <- 9;
      !arrayDest1.(n) <- Hashtbl.find ht f1;
      !arrayDest2.(n) <- Hashtbl.find ht (P.X f)
  | P.OR (f1, f2) ->
      !arrayType.(n) <- 5;
      !arrayDest1.(n) <- Hashtbl.find ht f1;
      !arrayDest2.(n) <- Hashtbl.find ht f2
  | P.AND (f1, f2) ->
      !arrayType.(n) <- 6;
      !arrayDest1.(n) <- Hashtbl.find ht f1;
      !arrayDest2.(n) <- Hashtbl.find ht f2
  | P.UN (f1, f2) ->
      !arrayType.(n) <- 7;
      !arrayDest1.(n) <- Hashtbl.find ht f2;
      !arrayDest2.(n) <- Hashtbl.find ht (P.AND (f1, P.X f));
      !arrayEventuality.(n) <- true
  | P.BF (f1, f2) ->
      !arrayType.(n) <- 8;
      !arrayDest1.(n) <- Hashtbl.find ht (P.nnfNeg f2);
      !arrayDest2.(n) <- Hashtbl.find ht (P.OR (f1, P.X f))
  | _ -> raise (P.PLTLException "Formula is not in negation normal form.")

(** Initialises the arrays for a formula and its integer representation.
    @param hcF A hash-cons table.
    @param ht A hashtable that maps formulae to their integer representation.
    @param f A hash-consed formula (in negation normal form).
    @param n The integer representation of f.
 *)
let initTablesHc hcF ht f n =
  !arrayFormula.(n) <- f.HC.fml;
  let fneg = f.HC.neg in
  if P.HcFHt.mem ht fneg then
    !arrayNeg.(n) <- P.HcFHt.find ht fneg;
  match f.HC.node with
  | P.HCTRUE -> !arrayType.(n) <- 0
  | P.HCFALSE -> !arrayType.(n) <- 1
  | P.HCAP _ -> !arrayType.(n) <- 2
  | P.HCNOT _ -> !arrayType.(n) <- 3
  | P.HCX f1 ->
      !arrayType.(n) <- 4;
      !arrayDest1.(n) <- P.HcFHt.find ht f1;
      !arrayEventuality.(n) <- P.is_un f1.HC.fml
  | P.HCOR (f1, f2) ->
      !arrayType.(n) <- 5;
      !arrayDest1.(n) <- P.HcFHt.find ht f1;
      !arrayDest2.(n) <- P.HcFHt.find ht f2
  | P.HCAND (f1, f2) ->
      !arrayType.(n) <- 6;
      !arrayDest1.(n) <- P.HcFHt.find ht f1;
      !arrayDest2.(n) <- P.HcFHt.find ht f2
  | P.HCUN (f1, f2) ->
      !arrayType.(n) <- 7;
      !arrayDest1.(n) <- P.HcFHt.find ht f2;
      let f3 = P.HcFormula.hashconsNeg hcF (P.HCX f) in
      let f4 = P.HcFormula.hashconsNeg hcF (P.HCAND (f1, f3)) in
      !arrayDest2.(n) <- P.HcFHt.find ht f4;
      !arrayEventuality.(n) <- true
  | P.HCBF (f1, f2) ->
      !arrayType.(n) <- 8;
      !arrayDest1.(n) <- P.HcFHt.find ht f2.HC.neg;
      let f3 = P.HcFormula.hashconsNeg hcF (P.HCX f) in
      let f4 = P.HcFormula.hashconsNeg hcF (P.HCOR (f1, f3)) in
      !arrayDest2.(n) <- P.HcFHt.find ht f4

(** Converts a formula in negation normal form
    and initialises the internal tables of this module.
    @param f The initial formula that is to be tested for satisfiability.
    @param rankingF A complete ranking of the different types of formulae.
    @param noty The number of types in rankingF,
    starting from the beginning of the list,
    whose formulae are stored in the bitsets explicitly.
    @return A triple (nnf, intnnf, nrf) where:
    nnf is in negation normal form and "satisfiable equivalent" to f;
    intnnf is the integer representation of nnf;
    nrf is the size of the closure.
 *)
let ppFormula f rankingF noty =
  let nnf = P.nnf f in
  let nnf = P.simplifyFormula nnf in
(*
  let flist = P.detClosure (P.generateCompare P.aRanking) nnf in
  let getFml f = f in
  let module Ht = Hashtbl in
*)
  let (flist, hcnnf, hcF) = P.detClosureHc nnf in
  let getFml f = f.HC.fml in
  let module Ht = P.HcFHt in
  let noF = Array.make P.numberOfTypes 0 in
  let liter f =
    let ty = P.getTypeFormula (getFml f) in
    noF.(ty) <- succ noF.(ty)
  in
  List.iter liter flist;
  let idxF = Array.make P.numberOfTypes 0 in
  let len = List.fold_left (fun idx ty -> idxF.(ty) <- idx; idx + noF.(ty)) 0 rankingF in
  let countSize (size, idx) ty =
    let nsize = if idx > 0 then size + noF.(ty) else size in
    (nsize, pred idx)
  in
  let (size, _) = List.fold_left countSize (0, noty) rankingF in
  let tyX = P.getTypeFormula (P.X P.TRUE) in
  let idxX = idxF.(tyX) in
  let noX = noF.(tyX) in
  let tyUN = P.getTypeFormula (P.UN (P.TRUE, P.TRUE)) in
  lposUN := idxF.(tyUN);
  hposUN := !lposUN + noF.(tyUN) - 1;
  arrayFormula := Array.make len P.TRUE;
  arrayType := Array.make len (-1);
  arrayDest1 := Array.make len (-1);
  arrayDest2 := Array.make len (-1);
  arrayNeg := Array.make len (-1);
  arrayEventuality := Array.make len false;
  let htF = Ht.create (2 * size) in
  let fillHt f =
    let ty = P.getTypeFormula (getFml f) in
    Ht.add htF f idxF.(ty);
    idxF.(ty) <- succ idxF.(ty)
  in
  List.iter fillHt flist;
(*
  let ff = P.FALSE in
  let tt = P.TRUE in
  let xt = P.X P.TRUE in
  let nnf2 = nnf in
  let initTbl = initTables htF in
*)
  let ff = P.HcFormula.hashconsNeg hcF P.HCFALSE in
  let tt = P.HcFormula.hashconsNeg hcF P.HCTRUE in
  let xt = P.HcFormula.hashconsNeg hcF (P.HCX tt) in
  let nnf2 = hcnnf in
  let initTbl = initTablesHc hcF htF in
  Ht.iter initTbl htF;
  fxtrue := Ht.find htF xt;
  initMisc size (Ht.find htF ff) (Ht.find htF tt) idxX noX 0;
  (nnf, Ht.find htF nnf2)


(** Converts a formula into a string.
    @param f A formula in integer representation.
    @return A string representing f.
 *)
let exportF f = P.exportFormula !arrayFormula.(f)


(** A ranking of formulae where the and-like formulae,
    with the exception of [*]-formulae,
    are not stored in the bitsets explicitly.
 *)
let rankingNoAnd = [ P.getTypeFormula (P.OR (P.TRUE, P.TRUE));
                     P.getTypeFormula (P.UN (P.TRUE, P.TRUE));
                     P.getTypeFormula (P.X P.TRUE);
                     P.getTypeFormula P.TRUE;
                     P.getTypeFormula P.FALSE;
                     P.getTypeFormula (P.AP "");
                     P.getTypeFormula (P.NOT P.TRUE);
                     P.getTypeFormula (P.AND (P.TRUE, P.TRUE));
                     P.getTypeFormula (P.BF (P.TRUE, P.TRUE));
                     P.getTypeFormula (P.AW P.TRUE);
                     P.getTypeFormula (P.EQU (P.TRUE, P.TRUE));
                     P.getTypeFormula (P.IMP (P.TRUE, P.TRUE));
                     P.getTypeFormula (P.EV P.TRUE) ]

(** The number of types in rankingFNoAnd,
    starting from the beginning of the list,
    whose formulae are stored in the bitsets explicitly.
 *)
let notyNoAnd = 7
