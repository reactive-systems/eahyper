(** A one-pass tree-tableau-based decision procedure for PLTL-satisfiability
    which blocks on ancestor core-nodes and caches unsatisfiable core-nodes.
    It is in EXPSPACE, that is it is not optimal.
    @author Florian Widmann
 *)


module P = PLTLFormula

type formula = P.formula


open PLTLMisc
open MiscSolver


(** An instantiation of a hash table (of the standard library) for bitsets.
 *)
module GHt = Hashtbl.Make(
  struct
    type t = bitset
    let equal (bs1 : t) bs2 = compareBS bs1 bs2 = 0
    let hash (bs : t) = hashBS bs
  end
 )


(** Defines the history Chn which can be seen as a partial function
    mapping UN-formulae to positive ints.
    It is implemented as an array that is indexed by UN-formulae
    (i.e. their integer representation shifted by an offset).
    UN-formulae for which Chn is undefined are mapped to naught.
    The array has size #{UN-formulae}.
 *)
type hchn = int array

(** The size of the arrays representing Chns
    (i.e. the number of UN-formulae).
 *)
let sizeChn = ref (-1)

(** Defines a new value for a UN-formula in a Chn.
    The old value is overridden.
    @param chn A Chn.
    @param f The UN-formula that is to be mapped to a new value in chn.
    @param n The new value that is assigned to f in chn.
    @raise Invalid_argument If f is not a UN-formula.
 *)
let setChn (chn : hchn) f n = chn.(f - !lposUN) <- n

(** Gets a value in a Chn for a UN-formula.
    @param chn A Chn.
    @param f A UN-formula.
    @return The value of f in chn.
    @raise Invalid_argument If f is not a UN-formula.
 *)
let getChn (chn : hchn) f = chn.(f - !lposUN)

(** Constructs the Chn for the X-rule.
    @param fs A bitset containing the formulae of the new core-node.
    @param lvl The level of the new core-node.
    @param chn The old Chn.
    @return The resulting Chn for the new core-node.
 *)
let newChn fs lvl chn = 
  let nchn = Array.make !sizeChn 0 in
  let offset = !lposUN in
  for i = offset to !hposUN do
    if memBS fs i then begin
      let ioffs = i - offset in
      let inhlvl = chn.(ioffs) in
      let nlvl = if inhlvl > 0 then inhlvl else lvl in
      nchn.(ioffs) <- nlvl
    end
  done;
  nchn


(** Defines the variable Uev which can be seen as a partial function
    mapping UN-formulae to positive ints.
    It is implemented as an array that is indexed by UN-formula
    (i.e. their integer representation shifted by an offset).
    UN-formulae for which Uev is undefined are mapped to naught.
    The array has size #{UN-formulae}.
 *)
type vuev = int array

(** The size of the arrays representing Uevs
    (i.e. the number of UN-formulae).
 *)
let sizeUev = ref (-1)

(** The greatest index of the Uevs.
    It must hold indexUev = sizeUev - 1.
 *)
let indexUev = ref (-1)

(** Tests whether a Uev is undefined for every formula.
    @param uev A Uev.
    @param i The current index of the array.
    @return True iff uev is undefined everywhere.
 *)
let rec intern_is_undef uev i =
  if i >= 0 then
    if uev.(i) = 0 then intern_is_undef uev (pred i)
    else false
  else true

let is_undefinedUev uev = intern_is_undef uev !indexUev

(** This functions "intersects" two Uevs.
    The result is returned in the first Uev.
    @param uev1 The first Uev.
    @param uev2 The second Uev.
    @param i The current index of the array.
    @return A Uev that is defined exactly for the formulae that are defined in uev1 and uev2.
    Each of these formulae is mapped to the smaller value of its mappings in uev1 and uev2.
 *)
let rec intern_minUev (uev1 : vuev) uev2 i =
  if i >= 0 then
    let h1 = uev1.(i) in
    let h2 = uev2.(i) in
    if h2 < h1 then uev1.(i) <- h2 else ();
    intern_minUev uev1 uev2 (pred i)
  else uev1

let minUev uev1 uev2 = intern_minUev uev1 uev2 !indexUev

(** This function checks whether there is a bad loop in the tableau,
    i.e. it checks whether there is a UN-formula
    that is defined in the Uev
    and has a value greater than or equal to the given bound.
    @param n A bound.
    @param uev A Uev.
    @return True iff a UN-formula f is defined in uev with uev(f) >= n.
 *)
let isSubloop (n : int) uev =
  let j = ref !indexUev in
  let res = ref false in
  while not !res && !j >= 0 do
    if uev.(!j) >= n then res := true else decr j
  done;
  !res

(** This function calculates the Uev of an X-node.
    @param lvl A level.
    @param fs Only UN-formulae that are contained in the bitset fs
    can potentially be defined in the resulting Uev.
    @param chn A Chn.
    @return The resulting Uev uev.
    That is for every procrastinating UN-formula f in fs
    we have uev(f) = lvl and uev is undefined everywhere else.
 *)
let mk_Uev lvl fs chn =
  let uev = Array.make !sizeUev 0 in
  let offset = !lposUN in
  for i = offset to !hposUN do
    if memBS fs i then
      let ioffs = i - offset in
      let n = chn.(ioffs) in
      if n > 0 && n <= lvl then uev.(ioffs) <- lvl else ()
    else ()
  done;
  uev


(** Gets a tableau node (i.e. its formula set and histories)
    and builds the sub-tableau rooted at the given node.
    @param fset A bitset containing all formulae in fsetc
    which still might have to be decomposed.
    @param fsetc A bitset of formulae.
    @param hc The history HCore of the given node.
    @param chn The history Chn of the given node.
    @param dp The depth of the given node in the tableau.
    It must be greater or equal than one.
    @param ht A hash table storing unsatisfiable core-nodes.
    @return None if the node is marked,
    Some uev otherwise where uev is the Uev of the node.
 *)
let rec intern_isSat fset fsetc hc chn dp ht =
  let pf = getPFinclEX fset in
  if pf >= 0 then
    let pftype = !arrayType.(pf) in
    match pftype with
    | 5
    | 7 ->
        remBS fset pf;
        let lvl = if pftype = 5 then 0 else getChn chn pf in
        let f1 = !arrayDest1.(pf) in
        let f2 = !arrayDest2.(pf) in
        if containsFormula fsetc f1 || (lvl = 0 && containsFormula fsetc f2) then
          if lvl = 0 then intern_isSat fset fsetc hc chn dp ht
          else begin
            setChn chn pf 0;
            let res = intern_isSat fset fsetc hc chn dp ht in
            setChn chn pf lvl;
            res
          end
        else begin
          incr nodecount;
          let fset2 = copyBS fset in
          let fsetc2 = copyBS fsetc in
          let cntr = insertFormula fset fsetc f1 in
          let mrk1 =
            if not cntr then
              if lvl = 0 then intern_isSat fset fsetc hc chn (succ dp) ht
              else begin
                setChn chn pf 0;
                let res = intern_isSat fset fsetc hc chn (succ dp) ht in
                setChn chn pf lvl;
                res
              end
            else None
          in
          match mrk1 with
          | Some uev1 when is_undefinedUev uev1 -> mrk1
          | _ ->
              let cntr = insertFormula fset2 fsetc2 f2 in
              let mrk2 =
                if not cntr then intern_isSat fset2 fsetc2 hc chn (succ dp) ht
                else begin
                  if dp > !pathlength then pathlength := dp;
                  None
                end
              in
              match (mrk1, mrk2) with
              | (None, None) -> None
              | (Some _, None) -> mrk1
              | (None, Some _) -> mrk2
              | (Some uev1, Some uev2) -> Some (minUev uev1 uev2)
        end
    | _ -> (* must be 4 *)
        incr nodecount;
        emptyBS fset;
        let hcfsetc = makeBS () in
        let cntr = mkXSet fsetc fset hcfsetc in
        if not cntr && not (GHt.mem ht hcfsetc) then
          let j =
            try
              GHt.find hc hcfsetc
            with Not_found -> 0
          in
          if j > 0 then
            let uev = mk_Uev j hcfsetc chn in
            if dp > !pathlength then pathlength := dp else ();
            Some uev
          else begin
            blitBS hcfsetc fsetc;
            GHt.add hc hcfsetc dp;
            let nchn = newChn hcfsetc dp chn in
            let mrk = intern_isSat fset fsetc hc nchn (succ dp) ht in
            GHt.remove hc hcfsetc;
            match mrk with
            | None ->
                GHt.add ht hcfsetc ();
                None
            | Some uev ->
                if isSubloop dp uev then begin
                  GHt.add ht hcfsetc ();
                  None
                end
                else mrk
          end
        else begin
          if dp > !pathlength then pathlength := dp;
          None
        end
  else
    let cntr = insertFormula fset fsetc !fxtrue in
    if not cntr then intern_isSat fset fsetc hc chn dp ht
    else begin
      if pred dp > !pathlength then pathlength := pred dp;
      None
    end


(** A one-pass tree-tableau-based decision procedure for PLTL-satisfiability
    which blocks on ancestor core-nodes and caches unsatisfiable core-nodes.
    It is in EXPSPACE, that is it is not optimal.
    @param verbose An optional switch which determines
    whether the procedure shall print some information on the standard output.
    The default is false.
    @param f The input formula that is tested for satisfiability.
    @return True if f is satisfiable, false otherwise.
 *)
let isSat ?(verbose = false) f = 
  let start = if verbose then Unix.gettimeofday () else 0. in
  let (nnf, fi) = ppFormula f rankingNoAnd notyNoAnd in
  sizeChn := !hposUN - !lposUN + 1;
  sizeUev := !hposUN - !lposUN + 1;
  indexUev := pred !sizeUev;
  let fset = makeBS () in
  let fsetc = makeBS () in
  let cntr = insertFormula fset fsetc fi in
  let sat =
    if cntr then false
    else
      let hc = (GHt.create 1024 : int GHt.t) in
      let chn = Array.make !sizeChn 0 in
      let ht = (GHt.create 1024 : unit GHt.t) in
      intern_isSat fset fsetc hc chn 1 ht <> None
  in
  if verbose then begin
    let stop = Unix.gettimeofday () in
    print_newline ();
    print_endline ("Input formula: " ^ (P.exportFormula f));
    print_endline ("Size: " ^ (string_of_int (P.sizeFormula f)));
    print_endline ("Negation Normal Form: " ^ (P.exportFormula nnf));
    print_endline ("Size: " ^ (string_of_int (P.sizeFormula nnf)));
    print_endline ("Result: Formula is " ^ (if not sat then "not " else "") ^ "satisfiable.");
    print_endline ("Time: " ^ (string_of_float (stop -. start)));
    print_endline ("Generated nodes: " ^ (string_of_int !nodecount));
    print_endline ("Longest path: " ^ (string_of_int !pathlength));
    print_newline ()
  end else ();
  sat
