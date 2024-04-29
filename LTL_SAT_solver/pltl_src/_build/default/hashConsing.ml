(** This module implements hash-consing with an emphasis on using it for formulae.
    It is inspired by the paper "Type-Safe Modular Hash-Consing"
    and by the OCaml implementation of hash tables.
    @author Florian Widmann
 *)


(** The elements of this type represent elements of another structure.
    However, it is guaranteed that structural equality and physical equality coincide.
    Hence the elements can only be constructed by smart constructors.
    An element e has the following information.
    (a) the first level of the original structure of e;
    (b) the hash value of e which is also the hash value of node;
    (c) the unique tag corresponding to e;
    (d) some data associated with e (e.g. the original structure corresponding to e);
    (e) the "negation" of e if "negation" is defined, or e itself otherwise;
    the "negation" must be a bijection such that no element is mapped onto itself,
    and the "negation" of the "negation" of an element is the element itself.
    An element and its negation are always created at the same time.
 *)
type ('a, 'b) hash_consed =
    { node : 'a; hkey : int; tag : int; fml : 'b; mutable neg : ('a, 'b) hash_consed }


(** The input signature of the functor Make.
 *)
module type HashedTyped =
  sig
    (** This type represents the first level of the original structure.
        Its elements are called nodes to distinguish them from the final elements.
     *)
    type nde

    (** Some data associated with elements of type nde.
     *)
    type fml
    
    (** Determines whether two nodes are structurally equal.
        @param The first node.
        @param The second node.
        @return True iff both nodes are structurally equal.
     *)
    val equal : nde -> nde -> bool

    (** Computes the hash value of a node.
        Elements which are structurally equal must have the same hash value.
        @param A node.
        @return The hash value of the node.
     *)
    val hash : nde -> int

    (** Computes the data which is associated to a node.
        @param A node.
        @return The data associated with the node.
     *)
    val toFml : nde -> fml

    (** Determines the "negation" of a node.
        If the "negation" is not defined and used,
        this can be a dummy function (e.g. the identity).
        @param A node.
        @return The negation of the node.
     *)
    val negNde : nde -> nde
  end


(** The output signature of the functor Make.
    See functor Make for further information.
 *)
module type S =
  sig
    type t
    type nde
    type fml
    val create : int -> t
    val hashcons : t -> nde -> (nde, fml) hash_consed
    val hashconsNeg : t -> nde -> (nde, fml) hash_consed
  end

module Make(H : HashedTyped) : (S with type nde = H.nde and type fml = H.fml) =
  struct
    (** This type represents the first level of the original structure.
        Its elements are called nodes to distinguish them from the final elements.
        Each element basically represents its node
        and all nodes which are structurally equal.
     *)
    type nde = H.nde

    (** Some data associated with the elements (their corresponding nodes).
     *)
    type fml = H.fml

    (** Basically a degenerated hash table (i.e. only keys, no data)
        which stores all elements so that structurally uniqueness can be enforced.
        (a) the number of elements in the hash table;
        (b) the hash table.
     *)
    type t = { mutable size: int; mutable data: bucket array }

    (** A list of all elements which have the same hash value.
     *)
    and bucket =
      | Empty
      | Cons of (nde, fml) hash_consed * bucket

    (** Computes a non-negative hash value for an element.
        It is indirectly computed via the corresponding node,
        which has the same hash value.
        @param nde A node.
        @return The non-negative hash value for nde.
     *)
    let realhash nde = (H.hash nde) land max_int

    (** Creates a hash-cons table.
        @param datasize The initial size of the hash-cons table.
        @return A hash-cons table.
     *)
    let create datasize =
      let ds =
        if datasize < 1 then 1
        else
          let maxds = Sys.max_array_length in
          if datasize >= maxds then maxds else datasize
      in
      { size = 0; data = Array.make ds Empty }

    (** Resizes a hash-cons table.
        @param hc A hash-cons table.
     *)
    let resize hc =
      let odata = hc.data in
      let ods = Array.length odata in
      let nds1 = 2 * ods + 1 in
      let maxds = Sys.max_array_length in
      let nds = if nds1 > maxds then maxds else nds1 in
      if nds > ods then
        let ndata = Array.make nds Empty in
        let rec insert_bucket = function
          | Empty -> ()
          | Cons (d, rest) ->
              let nidx = d.hkey mod nds in
              ndata.(nidx) <- Cons (d, ndata.(nidx));
              insert_bucket rest
        in
        for i = 0 to pred ods do
          insert_bucket odata.(i)
        done;
        hc.data <- ndata
      else ()

    (** Recursively searches for an element in a bucket.
        @param nde A node.
        @param bucket The remaining bucket.
        @return The element whose node is structurally equal to nde.
        @raise Not_found if such an element does not exist (yet).
     *)
    let rec find_rec nde bucket =
      match bucket with
      | Empty -> raise Not_found
      | Cons (d, rest) ->
          if H.equal nde d.node then d else find_rec nde rest

    (** Searches for an element in a bucket.
        @param nde A node.
        @param bucket A bucket.
        @return The element whose node is structurally equal to nde.
        @raise Not_found if such an element does not exist (yet).
     *)
    let find nde bucket =
      match bucket with
      | Empty -> raise Not_found
      | Cons (d1, rest1) ->
          if H.equal nde d1.node then d1 else
          match rest1 with
          | Empty -> raise Not_found
          | Cons (d2, rest2) ->
              if H.equal nde d2.node then d2 else
              match rest2 with
              | Empty -> raise Not_found
              | Cons (d3, rest3) ->
                  if H.equal nde d3.node then d3 else find_rec nde rest3

    (** Retrieves the element in a hash-cons table
        whose node is structurally equal to nde.
        If such an element does not exist yet, it will be created.
        The concept of "negation" is not used.
        @param hc A hash-cons table.
        @param nde A node.
        @return An element in hc whose node is structurally equal to nde.
     *)
    let hashcons hc nde =
      let data = hc.data in
      let ds = Array.length data in
      let hkey = realhash nde in
      let idx = hkey mod ds in
      let bucket = data.(idx) in
      try
        find nde bucket
      with Not_found ->
        let fml = H.toFml nde in
        let osize = hc.size in
        let rec nd = { node = nde; hkey = hkey; tag = osize; fml = fml; neg = nd } in
        data.(idx) <- Cons (nd, bucket);
        hc.size <- succ osize;
        if hc.size > ds lsl 1 then resize hc else ();
        nd

    (** Retrieves the element in a hash-cons table
        whose node is structurally equal to nde.
        If such an element does not exist yet, it (and its negation) will be created.
        @param hc A hash-cons table.
        @param nde A node.
        @return An element in hc whose node is structurally equal to nde.
     *)
    let hashconsNeg hc nde =
      let data = hc.data in
      let ds = Array.length data in
      let hkey = realhash nde in
      let idx = hkey mod ds in
      let bucket = data.(idx) in
      try
        find nde bucket
      with Not_found ->
        let fml = H.toFml nde in
        let osize = hc.size in
        let rec nd = { node = nde; hkey = hkey; tag = osize; fml = fml; neg = nd } in
        data.(idx) <- Cons (nd, bucket);
        let ndeN = H.negNde nde in
        let hkeyN = realhash ndeN in
        let fmlN = H.toFml ndeN in 
        let ndN = { node = ndeN; hkey = hkeyN; tag = succ osize; fml = fmlN; neg = nd } in
        nd.neg <- ndN;
        let idxN = hkeyN mod ds in
        data.(idxN) <- Cons (ndN, data.(idxN));
        hc.size <- osize + 2;
        if hc.size > ds lsl 1 then resize hc else ();
        nd
  end
