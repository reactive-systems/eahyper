(** An on-the-fly graph-tableau-based decision procedure for PLTL-satisfiability
    which blocks on all nodes, does not focus on a single formula,
    and uses variables to track unfulfilled eventualties on-the-fly.
    Its runs in EXPTIME (PLTL-satisfiability is PSPACE-complete,
    but I am not aware of an efficient PSPACE implementation).
    @author Florian Widmann
 *)


module P = PLTLFormula

type formula = P.formula


open PLTLMisc
open MiscSolver


(** An instantiation of a map (of the standard library)
    for formulae (in integer representation).
 *)
module CMap = FMap

(** An instantiation of a hash table (of the standard library) for bitsets.
 *)
module GHt = Hashtbl.Make(
  struct
    type t = bitset
    let equal (bs1 : t) bs2 = compareBS bs1 bs2 = 0
    let hash (bs : t) = hashBS bs
  end
 )


module rec A :
    sig
      (** Defines a partial function Prs for a node nde
          which maps each eventuality ev of nde
          to the set of potential rescuers of ev.
          If Prs(ev) is undefined then ev can currently be fulfilled
          in the part of the graph which is older than nde
          (that is the graph consisting of all nodes
          whose initial status was set before that of nde).
          If Prs(ev) is defined, it is a set of node-formula pairs (n, f)
          where n is a node whose initial status of n is set after that of nde
          and f is an eventuality in n.
          The only chance for ev to be fulfilled in the graph
          is through one of these potential rescuers.
       *)
      type vprs = PSet.t FMap.t

      (** Indicates whether a node with defined status is an or-node or a state.
          For an or-node the following information is stored:
          (a) the principal formula of the or-node;
          (b) some relevant children of the or-node and
          their successor eventualities of ev
          if ev is defined and the child does not fulfil it directly (else -1);
          (c) -2 if the second child of the or-node has already been expanded,
          else the successor eventualities of ev in the second (yet unexpanded) child
          if ev is defined and the child does not fulfil it directly (else -1).
          For a state the following information is stored:
          (a) the child of the state.
       *)
      and kindDef =
        | DOr of int * (node * int) list ref * int ref
        | DState of node

      (** Indicates whether a node with undefined status is an or-node or a state.
          For an or-node the following information is stored:
          (a) see kindDef;
          (b) see kindDef;
          (c) the number of remaining decompositions of the principal formula
          of the or-node which still have to be processed.
          For a state no information is stored.
       *)
      and kindUndef =
        | UOr of int * (node * int) list ref * int ref
        | UState

      (** The status of a node.
          Sat: The node is satisfiable.
          Unsat: The node is unsatisfiable.
          Undef: The node has not been fully processed yet.
          (a) the set of formulae of the node;
          (b) a singleton list containing the parent of the node,
          (if the node is the root node then the list is empty);
          (c) all relevant nodes which point to this node via bw- or upd-edges;
          (d) see kindUndef.
          Unknwn: The node has been fully processed
          but it is not known yet whether or not the node is satisfiable.
          (a) see Undef;
          (b) see Undef;
          (c) see Undef;
          (d) a time stamp showing when the node got its initial status;
          (e) the cache of the node;
          (f) the current Prs of the node;
          (g) see kindDef.
       *)
      and status =
        | Sat
        | Unsat
        | Undef of bitset * node list * NSet.t ref * kindUndef
        | Unknwn of bitset * node list * NSet.t ref * int * cache ref * vprs ref * kindDef

      (** Stores for each eventuality ev
          whether detPrsEntry has already been invoked for the node and ev
          under the latest invocation of detStatusState or detStatusOr.
          In this case the corresponding result is remembered too.
       *)
      and cache = (int * PSet.t) CMap.t

      (** Some information about a node which is stored in the graph:
          (a) a unique id number for each node; and
          (b) the current status of the node.
       *)
      and node = { id : int; mutable status : status }

      type t = node * int
      val compare: t -> t -> int
    end
    = struct
      type vprs = PSet.t FMap.t

      and kindDef =
        | DOr of int * (node * int) list ref * int ref
        | DState of node

      and kindUndef =
        | UOr of int * (node * int) list ref * int ref
        | UState

      and status =
        | Sat
        | Unsat
        | Undef of bitset * node list * NSet.t ref * kindUndef
        | Unknwn of bitset * node list * NSet.t ref * int * cache ref * vprs ref * kindDef

      and cache = (int * PSet.t) CMap.t

      and node = { id : int; mutable status : status }

      type t = node * int

      let comparePrsEntry ((n1, f1) : node * int) (n2, f2) =
        if f1 < f2 then (-1)
        else if f1 > f2 then 1
        else
          let id1 = n1.id in
          let id2 = n2.id in
          if id1 < id2 then (-1)
          else if id1 > id2 then 1
          else 0

      let compare: t -> t -> int = comparePrsEntry
    end
and B :
    sig
      type t = A.node
      val compare: t -> t -> int
    end
      = struct
        open A

        type t = node

        let compareNode (n1 : node) n2 =
          let id1 = n1.id in
          let id2 = n2.id in
          if id1 < id2 then (-1)
          else if id1 > id2 then 1
          else 0

        let compare: t -> t -> int = compareNode
      end
and PSet : Set.S with type elt = A.t = Set.Make(A)
and NSet : Set.S with type elt = B.t = Set.Make(B)

open A


(** The cache of a node which can be seen as a partial function
    from formulae to pairs (ts, ps) where
    ts is a time stamp indicating the invocation of detStatusState or detStatusOr
    for which the cache is valid, and ps is a set of potential rescuers.
 *)
type cache = (int * PSet.t) CMap.t

(** An empty cache
 *)
let (emptyCache : cache) = CMap.empty

(** Caches the result for an invocation of detPrsEntry for a node-formula pair
    under a specific invocation of detStatusState or detStatusOr.
    @param cache The cache of the node.
    @param ev An eventuality of the node.
    @param crun The number corresponding
    to the invocation of detStatusState or detStatusOr.
    @param ps The result of the invocation of detPrsEntry for the node and ev.
    @return An updated cache where ev is mapped to ps for cacherun.
    Older results for ev are overridden as they are not needed any longer.
 *)
let addCache (cache : cache) ev crun ps = CMap.add ev (crun, ps) cache

(** Checks whether an invocation of detPrsEntry for a node-formula pair
    under a specific invocation of detStatusState or detStatusOr
    has already been executed before.
    @param cache The cache of the node.
    @param ev An eventuality of the node.
    @param crun The number corresponding
    @return None if not, Some res if yes
    where res is the result of the first invocation.
 *)
let memCache (cache : cache) ev crun =
  try
    let (run, ps) = CMap.find ev cache in
    if run = crun then Some ps else None
  with Not_found -> None


(** A prototype unsatisfiable node.
 *)
let unsatNode = { id = 0; status = Unsat }

(** A prototype satisfiable node.
 *)
let satNode = { id = 0; status = Sat }


(** Compares two Prs.
    @param prs1 The first Prs.
    @param prs2 The second Prs.
    @return true iff they are not equal.
 *)
let isNotEqualPrs (prs1 : vprs) prs2 = FMap.compare PSet.compare prs1 prs2 <> 0

(** A Prs which is undefined for every eventuality.
 *)
let undefinedPrs = (FMap.empty : vprs)

(** Tests whether all eventualities in a Prs can be fulfilled.
    @param prs A Prs.
    @return True iff prs is undefined everywhere.
 *)
let isUndefinedPrs (prs : vprs) = FMap.is_empty prs

(** Retrieves the Prs of a node.
    @param nde A node with status "Unknwn (prs, _)".
    @return prs.
 *)
let getPrs nde = 
  match nde.status with
  | Unknwn (_, _, _, _, _, prs, _) -> !prs
  | _ -> raise (P.PLTLException "This should not happen. It is a bug in \"getPrs\"!")

(** Retrieves a set of potential rescuers for an eventuality in a Prs.
    @param prs A Prs.
    @param ev An eventuality.
    @return The set of potential rescuers of ev in prs if defined.
    @raise Not_found if evopt can currently be fulfilled in the graph.
 *)
let getPrsEntry (prs : vprs) ev = FMap.find ev prs

(** Adds a set of potential rescuers for an eventuality to a Prs.
    @param prs A Prs.
    @param ev An eventuality.
    @param ps A set of potential rescuers.
    @return Prs' such that Prs'(ev') = Prs(ev') for ev' <> ev and Prs'(ev) = ps.
 *)
let addPrsEntry (prs : vprs) ev ps = FMap.add ev ps prs


(** Imports the Prs entry of an eventuality of a child to a node.
    It also updates the update-edges accordingly.
    @param crun The current value of cacherun.
    @param basenode A node.
    @param bnts The time stamp of basenode.
    @param cacher The cache of a node nde which has status Unknwn
    and whose initial status was set before that of basenode.
    @param ev An eventuality in nde
    which must have a defined set of potential rescuers in nde.
    @param ps The set of potential rescuers of ev in nde.
    @return The resulting Prs entry nps if defined
    where nps is the set of all potential rescuers (n, f)
    such that n is in the branch of basenode and ev can reach (n, f).
    @raise Not_found if ev can currently be fulfilled in the graph.
 *)
let rec intern_detPrsEntry crun basenode bnts cacher ev ps =
  match memCache !cacher ev crun with
  | Some res -> res
  | None ->
      let updCr ((n, f) as p) acc =
        match n.status with
        | Unknwn (_, _, bwupd1r, ts1, cacher1r, prs1r, _) when bnts < 0 || ts1 < bnts ->
            let bwupd1 = !bwupd1r in
            if not (NSet.mem basenode bwupd1) then bwupd1r := NSet.add basenode bwupd1 else ();
            let ps1 = getPrsEntry !prs1r f in
            let nps = intern_detPrsEntry crun basenode bnts cacher1r f ps1 in
            PSet.union acc nps
        | Unsat -> acc
        | Sat -> raise Not_found
        | _ -> PSet.add p acc
      in
      let res = PSet.fold updCr ps PSet.empty in
      cacher := addCache !cacher ev crun res;
      res

let detPrsEntry crun basenode bnts nde ev =
  match nde.status with
  | Unknwn (_, _, _, ts, cacher, prsr, _) when bnts < 0 || ts < bnts ->
      let ps = getPrsEntry !prsr ev in
      intern_detPrsEntry crun basenode bnts cacher ev ps
  | _ -> PSet.singleton (nde, ev)


(** Determines the initial Prs of a node from a child.
    @param crun The current value of cacherun.
    @param nde An or-node.
    @param nfs The set of formulae belonging to nde.
    @param nts The time stamp of nde.
    @param pfopt The principal formula of nde if it is an eventuality (else -1).
    @param chld A child of nde whose status is either Undef or Unknwn.
    @param evoptc The successor eventuality of pfopt in chld
    if chld does not fulfil pfopt directly (else -1).
    The value evoptc is only used if pfopt is defined.
    @return The imported potential rescuers for all eventualities in nde.
 *)
let detPrsOr crun nde nfs nts pfopt chld evoptc =
  match chld.status with
  | Unknwn (_, _, _, cts, ccacher, cprsr, _) when nts < 0 || cts < nts ->
      let prsFld ev ps acc =
        if memBS nfs ev then
          try
            let nps = intern_detPrsEntry crun nde nts ccacher ev ps in
            addPrsEntry acc ev nps
          with Not_found -> acc
        else acc
      in
      let prs1 = FMap.fold prsFld !cprsr undefinedPrs in
      if pfopt < 0 || evoptc < 0 then prs1
      else begin
        try
          let nps = detPrsEntry crun nde nts chld evoptc in
          addPrsEntry prs1 pfopt nps
        with Not_found -> prs1
      end
  | _ ->
      let res = ref undefinedPrs in
      for i = 0 to pred !nrFormulae do
        if !arrayEventuality.(i) && memBS nfs i then
          if i = pfopt then
            if evoptc >= 0 then
              let psi = PSet.singleton (chld, evoptc) in
              res := addPrsEntry !res i psi
            else ()
          else
            let psi = PSet.singleton (chld, i) in
            res := addPrsEntry !res i psi
        else ()
      done;
      !res

(** This function "intersects" a preliminary Prs of an or-node
    with another Prs which is imported from a child of the or-node.
    @param crun The current value of cacherun.
    @param nde An or-node.
    @param nts The time stamp of nde.
    @param nprs A preliminary Prs for nde.
    @param pfopt The principal formula of nde if it is an eventuality (else -1).
    @param chld A child of nde.
    @param evoptc The successor eventuality of pfopt in chld
    if chld does not fulfil pfopt directly (else -1).
    The value evoptc is only used if pfopt is defined.
    @return An updated Prs prs' for nde.
    Let prs2 be the imported Prs from chld.
    Then prs' is defined for an eventuality ev
    iff ev is defined in prs and prs2.
    In this case prs'(ev) := prs(ev) \cup prs2(ev).
 *)
let minPrsOr crun nde nts nprs pfopt chld evoptc =
  let prsFld ev ps1 acc =
    let ev2 = if ev = pfopt then evoptc else ev in
    if ev2 >= 0 then
      try
        let ps2 = detPrsEntry crun nde nts chld ev2 in
        let nps = PSet.union ps1 ps2 in
        addPrsEntry acc ev nps
      with Not_found -> acc
    else acc
  in
  FMap.fold prsFld nprs undefinedPrs


(** "Expands" a Prs entry for an eventuality ev,
    which is not passed as argument, of a given node.
    @param nde A node.
    @param prs A preliminary Prs of nde.
    @param excl A list of all eventualities
    which have already been expanded while dealing with ev.
    The list is used to prevent non-termination.
    @param ps The set of potential rescuers of ev.
    @param initset The set with which the result is joined.
    @return The union of initset
    and the set of potential rescuers of ev, which might be empty.
    @raise Not_found iff the expansion indicates
    that ev can currently be fulfilled in the graph.
 *)
let rec expPs nde prs excl ps initset =
  let expFld ((n, ev) as p) acc =
    if n != nde then PSet.add p acc
    else if List.mem ev excl then acc
    else
      let evps = getPrsEntry prs ev in
      expPs nde prs (ev::excl) evps acc
  in
  PSet.fold expFld ps initset

(** Is thrown if an eventuality cannot be fulfilled.
 *)
exception Bad_loop

(** "Filters" a Prs in a given node and tests
    whether some eventuality cannot be fulfilled.
    @param nde A node.
    @param prs A preliminary Prs of nde.
    @return The "expanded" prs.
    @raise Bad_loop if there exists an eventuality in nde
    which cannot be fulfilled.
 *)
let filterPrs nde (prs : vprs) =
  let expFld ev ps acc =
    try
      let nps = expPs nde prs [ev] ps PSet.empty in
      if not (PSet.is_empty nps) then addPrsEntry acc ev nps else raise Bad_loop
    with Not_found -> acc
  in
  FMap.fold expFld prs undefinedPrs


(** Represents a graph. The nodes are indexed by sets of formulae.
 *)
type graph = node GHt.t

(** Empties a graph.
    @param grph A graph.
 *)
let emptyGraph (grph : graph) = GHt.clear grph

(** Returns the node which is assigned to a set of formulae in a graph
    if it exists.
    @param grph A graph.
    @param fs A bitset of formulae.
    @return None if no node with fs is contained in grph,
    Some n otherwise where n is the node with fs in grph.
 *)
let memGraph (grph : graph) fs =
  try
    Some (GHt.find grph fs)
  with Not_found -> None

(** Adds a set of formulae and its node to a graph.
    @param grph A graph.
    @param fs A bitset of formulae.
    @param nde The node with fs as its set of formulae.
 *)
let addGraph (grph : graph) fs nde = GHt.add grph fs nde

(** Returns the size of a graph.
    @param grph A graph.
    @return The number of nodes in grph.
 *)
let sizeGraph (grph : graph) = GHt.length grph

(** The graph of the decision procedure.
 *)
let grph = (GHt.create 1024 : graph)


(** Converts a node into a string.
    @param n A node.
    @return The id number of n as string.
 *)
let exportN n = string_of_int n.id

(** Prints a Prs.
    @param ind A string prefixing the output.
    @param A Prs.
 *)
let printPrs ind prs =
  let expSetFld (n, f) acc =
    let pstr = "(" ^ (exportN n) ^ ", " ^ (exportF f) ^ ")" in
    pstr::acc
  in
  let expMapFld ev ps acc =
    let fstr = exportF ev in
    let expSet ps = PSet.fold expSetFld ps [] in
    let estr = exportAsSet (fstr ^ " -> ") expSet ps in
    estr::acc
  in
  let expPrs p = FMap.fold expMapFld p [] in
  print_endline (exportAsSet (ind ^ "Prs: ") expPrs prs)

(** Prints a list of children and their successor eventuality if defined.
    @param nl A list of pairs (n, ev) where n is a node
    and ev is an eventuality of undefined (-1).
 *)
let printChildren nel =
  let expP (n, evopt) = "(" ^ (exportN n) ^ ", " ^
    (if evopt >= 0 then exportF evopt else "---") ^ ")"
  in
  print_endline (exportAsSet "     children: " (List.map expP) nel)

(** Prints information about type kindDef.
 *)
let printKindDef = function
  | DOr (pf, nelr, evopt2r) ->
      print_endline "DOr:";
      print_endline ("     PF: " ^ (exportF pf));
      printChildren !nelr;
      if !evopt2r > (-2) then print_endline "     second branch skipped" else ()
  | DState chld -> print_endline ("DState: " ^ (exportN chld))

(** Prints information about type kindUndef.
 *)
let printKindUndef = function
  | UOr (pf, nelr, nor) ->
      print_endline "UOr:";
      print_endline ("     PF: " ^ (exportF pf));
      printChildren !nelr;
      print_endline ("     todo no.: " ^ (string_of_int !nor))
  | UState -> print_endline "UState"

(** Prints information about a node.
    @param nde A node.
 *)
let printNode (nde : node) =
  print_newline ();
  print_endline ("Id: " ^ (exportN nde));
  let expP = function
    | [] -> "---"
    | prnt::_ -> exportN prnt
  in
  let expBwupd bwupd =
    NSet.fold (fun n acc -> (exportN n)::acc) bwupd []
  in
  print_string "Status: ";
  match nde.status with
  | Sat -> print_endline "Sat"
  | Unsat -> print_endline "Unsat"
  | Undef (fs, prntl, bwupdr, kind) ->
      print_endline (exportAsSet "FSet: " (exportFSet exportF) fs);
      print_endline ("Parent: " ^ (expP prntl));
      print_endline (exportAsSet "Bw/Upd: " expBwupd !bwupdr);
      print_string "Undef: ";
      printKindUndef kind
  | Unknwn (fs, prntl, bwupdr, ts, cacher, prsr, kind) ->
      print_endline (exportAsSet "FSet: " (exportFSet exportF) fs);
      print_endline ("Parent: " ^ (expP prntl));
      print_endline (exportAsSet "Bw/Upd: " expBwupd !bwupdr);
      print_endline ("Timestamp: " ^ (string_of_int ts));
      print_string "Unknown: ";
      printKindDef kind;
      printPrs "     " !prsr

(** Prints a graph.
    @param str A string which is printed first.
    @param grph A graph.
 *)
let printGraph str grph =
  let arrayGrph = Array.make (GHt.length grph) satNode in
  GHt.iter (fun _ n -> arrayGrph.(pred n.id) <- n) grph;
  Array.iter (fun n -> printNode n) arrayGrph;
  print_newline ();
  print_endline str


(** The result type for the two following functions.
 *)
type result = RSat | RUnsat | RPrs of vprs

(** Determines the status of an or-node.
    @param crun The current value of cacherun.
    @param nde A node.
    @param fs The set of formulae belonging to nde.
    @param ts The time stamp of nde.
    @param pfopt The principal formula of nde if it is an eventuality (else -1).
    @param allUnsat True iff all children examined so far were unsatisfiable.
    @param prs The (preliminary) Prs of nde.
    It is only used if allUnsat is false.
    @param nel A list of pairs (c, evopt) where c is a child of nde and
    evopt is the successor eventuality of pfopt in chld
    if pf is an eventuality and chld does not fulfil it directly (else -1).
    @return RSat if the node is satisfiable;
    RUnsat if the node is unsatisfiable; and
    RPrs prs if the status of the node is unknown
    and the Prs of the node is prs.
 *)
let rec intern_detStatusOr crun nde fs ts pfopt allUnsat prs nel =
  match nel with
  | (chldi, evopti)::tl -> begin
      match chldi.status with
      | Unknwn _
      | Undef _ ->
          let nprs =
            if allUnsat then detPrsOr crun nde fs ts pfopt chldi evopti
            else minPrsOr crun nde ts prs pfopt chldi evopti
          in
          intern_detStatusOr crun nde fs ts pfopt false nprs tl
      | Unsat -> intern_detStatusOr crun nde fs ts pfopt allUnsat prs tl
      | Sat -> RSat
  end
  | [] ->
      if allUnsat then RUnsat 
      else
        try
          let nprs = filterPrs nde prs in
          RPrs nprs
        with Bad_loop -> RUnsat

let detStatusOr nde fs ts pf nel =
  incr cacherun;
  let pfopt = if !arrayEventuality.(pf) then pf else (-1) in
  intern_detStatusOr !cacherun nde fs ts pfopt true undefinedPrs nel

(** Determines the status of a state.
    @param nde A state.
    @param fs The set of formulae belonging to nde.
    @param ts The time stamp of nde.
    @param chld The child of nde.
    @return RSat if the node is satisfiable;
    RUnsat if the node is unsatisfiable; and
    RPrs prs if the status of the node is unknown
    and the Prs of the node is prs.
 *)
let detStatusState nde fs ts chld =
  incr cacherun;
  let crun = !cacherun in
  match chld.status with
  | Unknwn _
  | Undef _ -> begin
      let res = ref undefinedPrs in
      for i = !lposEX to !hposEX do
        if !arrayEventuality.(i) && memBS fs i then
          try
            let evchld = !arrayDest1.(i) in
            let nps = detPrsEntry crun nde ts chld evchld in
            res := addPrsEntry !res i nps
          with Not_found -> ()
        else ()
      done;
      try
        let nprs = filterPrs nde !res in
        RPrs nprs
      with Bad_loop -> RUnsat
  end
  | Unsat -> RUnsat
  | Sat -> RSat


(** Propagates the status of nodes in a graph.
    @param queue A list of nodes in the graph which must be updated.
    @raise Queue.Empty if queue is empty.
 *)
let rec propagate queue =
  let nde = Queue.take queue in
  match nde.status with
  | Unknwn (fs, prntl, bwupdr, ts, _, oldprsr, kind) ->
      let res =
        match kind with
        | DState chld -> detStatusState nde fs ts chld
        | DOr (pf, nelr, evopt2r) ->
            let rsts = detStatusOr nde fs ts pf !nelr in
            if !evopt2r = (-2) then rsts
            else
              let notExpandOr =
                match rsts with
                | RUnsat -> false
                | RPrs nprs when not (isUndefinedPrs nprs) -> false
                | _ -> true
              in
              if notExpandOr then rsts
              else
                let fseti = copyBS fs in
                remBS fseti pf;
                let cntri = insertFormulaNS fseti !arrayDest2.(pf) in
                if not cntri then ignore (isSat_create [nde] fseti) else ();
                evopt2r := (-2);
                detStatusOr nde fs ts pf !nelr
      in
      let prop =
        match res with
        | RPrs prs ->
            if isNotEqualPrs !oldprsr prs then begin
              oldprsr := prs;
              true
          end
          else false
        | RUnsat ->
            nde.status <- Unsat;
            true
        | RSat ->
            nde.status <- Sat;
            true
      in
      if prop then begin
        assert (prntl <> []);
        Queue.add (List.hd prntl) queue;
        let bwupd = !bwupdr in
        if not (NSet.is_empty bwupd) then
          NSet.iter (fun x -> Queue.add x queue) bwupd
        else ()
      end
      else ();
      propagate queue
  | _ -> propagate queue (* Must be Sat or Unsat *)


(** Sets the initial status of a node and propagates accordingly.
    @param nde A node whose current status is undefined.
    @param prntl A singleton list containing the parent of nde.
    If nde is the root node then prntl is empty.
    @param bwupdr All relevant nodes which point to nde via bw- or upd-edges.
    @param sts The initial status of nde.
    @return True iff the initial formula is satisfiable.
 *)
and contSetStatus nde prntl bwupdr sts =
  nde.status <- sts;
  if prntl <> [] then
    let () =
      match sts with
      | Sat
      | Unsat ->
          let bwupd = !bwupdr in
          if not (NSet.is_empty bwupd) then
            let queue = Queue.create () in
            NSet.iter (fun x -> Queue.add x queue) bwupd;
            try
              propagate queue
            with Queue.Empty -> ()
          else ()
      | _ -> ()
    in
    isSat_continue (List.hd prntl) nde
  else sts <> Unsat

(** Sets up information about the current child of an or-node
    and invokes the creation of the child
    (unless there is an immediate contradiction).
    @param nde The or-node which is partly processed.
    @param fs The set of formulae belonging to nde.
    @param prntl A singleton list containing the parent of nde.
    If nde is the root node then prntl is empty.
    @param bwupdr All relevant nodes which point to nde via bw- or upd-edges.
    @param pf The principal formula of nde.
    @param nelr A list of pairs (c, evopt) where c is a child of nde and
    evopt is the successor eventuality of pfopt in chld
    if pf is an eventuality and chld does not fulfil it directly (else -1).
    @param nor The number of remaining decompositions
    of the principal formula of nde which still have to be processed.
    @return True iff the initial formula is satisfiable.
 *)
and contOr nde fs prntl bwupdr pf nelr nor =
  match !nor with
  | 0 -> begin
      let res = detStatusOr nde fs (-1) pf !nelr in
      match res with
      | RPrs prs ->
          let sts =
            incr postfixcount;
            Unknwn (fs, prntl, bwupdr, !postfixcount, ref emptyCache,
                    ref prs, DOr (pf, nelr, ref (-2)))
          in
          contSetStatus nde prntl bwupdr sts
      | RUnsat -> contSetStatus nde prntl bwupdr Unsat
      | RSat -> assert (1 = 0); contSetStatus nde prntl bwupdr Sat
  end
  | n ->
      decr nor;
      let fseti = copyBS fs in
      remBS fseti pf;
      let fi = if n = 2 then !arrayDest1.(pf) else !arrayDest2.(pf) in
      let cntri = insertFormulaNS fseti fi in
      if not cntri then isSat_create [nde] fseti
      else isSat_continue nde unsatNode

(** Gets a node which has been partly processed and a child of the node
    which has been fully processed and updates the node status accordingly.
    It then starts processing the next child or
    - if there is none or the status of the node is already determined -
    sets the status of the node and continues processing its parent.
    @param nde The node which is partly processed.
    @param chld The child which just has been finished processing.
    @return True iff the initial formula is satisfiable.
 *)
and isSat_continue nde chld =
(*
  printGraph ("continue graph: " ^ (exportN nde) ^ " " ^ (exportN chld)) grph;
 *)
  match nde.status with
  | Undef (fs, prntl, bwupdr, kind) -> begin
      match kind with
      | UOr (pf, nelr, nor) -> begin
          match chld.status with
          | Unknwn _
          | Undef _ ->
              let evpf = !arrayEventuality.(pf) in
              let evopti = if evpf && !nor = 0 then !arrayDest2.(!arrayDest2.(pf)) else (-1) in
              nelr := (chld, evopti)::!nelr;
              if !nor = 1 then
                let pfopt = if evpf then pf else (-1) in
                incr cacherun;
                let prs = detPrsOr !cacherun nde fs (-1) pfopt chld (-1) in
                if isUndefinedPrs prs then
                  let evopt2 = if evpf then !arrayDest2.(!arrayDest2.(pf)) else (-1) in
                  let sts =
                    incr postfixcount;
                    Unknwn (fs, prntl, bwupdr, !postfixcount, ref emptyCache,
                            ref prs, DOr (pf, nelr, ref evopt2))
                  in
                  contSetStatus nde prntl bwupdr sts
                else contOr nde fs prntl bwupdr pf nelr nor
              else contOr nde fs prntl bwupdr pf nelr nor
          | Unsat -> contOr nde fs prntl bwupdr pf nelr nor
          | Sat -> contSetStatus nde prntl bwupdr Sat
      end
      | UState -> begin
          let res = detStatusState nde fs (-1) chld in
          match res with
          | RPrs prs ->
              let sts =
                incr postfixcount;
                Unknwn (fs, prntl, bwupdr, !postfixcount, ref emptyCache, ref prs, DState chld)
              in
              contSetStatus nde prntl bwupdr sts
          | RUnsat -> contSetStatus nde prntl bwupdr Unsat
          | RSat -> contSetStatus nde prntl bwupdr Sat
      end
  end
  | Unknwn (_, _, _, _, _, _, DOr (_, nelr, evopt2r)) ->
      nelr := (chld, !evopt2r)::!nelr;
      false
  | _ -> raise (P.PLTLException "This should not happen. It is a bug in \"isSat_continue\"!")

(** Creates a new node if it does not already exist
    and initialises the creation of its first child
    (unless there is an immediate contradiction).
    @param prntl A singleton list containing the parent of the new node
    Iff the new node is the root node then the list is empty.
    @param fset The bitset of formulae of the new node.
    It is assumed that only this invocation can modify it.
    @return True iff the initial formula is satisfiable.
 *)
and isSat_create prntl fset =
(*
  printGraph "create graph: " grph;
 *)
  match memGraph grph fset with
  | None ->
      let pf = getPFinclEX fset in
      if pf >= 0 then
        match !arrayType.(pf) with
        | 4 ->
            let fsetX = makeBS () in
            let cntr = mkXSetNS fset fsetX in
            if not cntr then
              let bwupdr = ref NSet.empty in
              let sts = Undef (fset, prntl, bwupdr, UState) in
              let nde = { id = getNewId (); status = sts } in
              addGraph grph fset nde;
              isSat_create [nde] fsetX
            else
              if prntl <> [] then isSat_continue (List.hd prntl) unsatNode
              else false
        | _ -> (* Must be 5 or 7. *)
            if
              containsFormula fset !arrayDest1.(pf) ||
              (not !arrayEventuality.(pf) && containsFormula fset !arrayDest2.(pf))
            then begin
              remBS fset pf;
              isSat_create prntl fset
            end
            else
              let nelr = ref [] in
              let nor = ref 2 in
              let bwupdr = ref NSet.empty in
              let sts = Undef (fset, prntl, bwupdr, UOr (pf, nelr, nor)) in
              let nde = { id = getNewId (); status = sts } in
              addGraph grph fset nde;
              contOr nde fset prntl bwupdr pf nelr nor
      else
        let cntr = insertFormulaNS fset !fxtrue in
        if not cntr then isSat_create prntl fset
        else
          if prntl <> [] then isSat_continue (List.hd prntl) unsatNode
          else false
  | Some nde ->
      let prnt = List.hd prntl in
      let _ =
        match nde.status with
        | Undef (_, _, bwupdr, _)
        | Unknwn (_, _, bwupdr, _, _, _, _) -> bwupdr := NSet.add prnt !bwupdr;
        | _ -> ()
      in
      isSat_continue prnt nde


(** An on-the-fly graph-tableau-based decision procedure for PLTL-satisfiability
    which blocks on all nodes, does not focus on a single formula,
    and uses variables to track unfulfilled eventualties on-the-fly.
    Its runs in EXPTIME (PLTL-satisfiability is PSPACE-complete,
    but I am not aware of an efficient PSPACE implementation).
    @param verbose An optional switch which determines
    whether the procedure shall print some information on the standard output.
    The default is false.
    @param f The initial formula that is to be tested for satisfiability.
    @return True if f is satisfiable, false otherwise.
 *)
let isSat ?(verbose = false) f = 
  let start = if verbose then Unix.gettimeofday () else 0. in
  let (nnf, fi) = ppFormula f rankingNoAnd notyNoAnd in
  let fset = makeBS () in
  let cntr = insertFormulaNS fset fi in
  emptyGraph grph;
  let sat = 
    if cntr then false
    else isSat_create [] fset
  in
(*
  printGraph "final graph: " grph;
 *)
  if verbose then begin
    let stop = Unix.gettimeofday () in
    print_newline ();
    print_endline ("Input formula: " ^ (P.exportFormula f));
    print_endline ("Size: " ^ (string_of_int (P.sizeFormula f)));
    print_endline ("Negation Normal Form: " ^ (P.exportFormula nnf));
    print_endline ("Size: " ^ (string_of_int (P.sizeFormula nnf)));
    print_endline ("Result: Formula is " ^ (if not sat then "not " else "") ^ "satisfiable.");
    print_endline ("Time: " ^ (string_of_float (stop -. start)));
    print_endline ("Generated nodes: " ^ (string_of_int (sizeGraph grph)));
    print_newline ();
  end else ();
  sat
