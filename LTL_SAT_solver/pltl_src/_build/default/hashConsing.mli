type ('a, 'b) hash_consed =
    private { node : 'a; hkey : int; tag : int; fml : 'b; mutable neg : ('a, 'b) hash_consed }

module type HashedTyped =
  sig
    type nde
    type fml
    val equal : nde -> nde -> bool
    val hash : nde -> int
    val toFml : nde -> fml
    val negNde : nde -> nde
  end

module type S =
  sig
    type t
    type nde
    type fml
    val create : int -> t
    val hashcons : t -> nde -> (nde, fml) hash_consed
    val hashconsNeg : t -> nde -> (nde, fml) hash_consed
  end

module Make(H : HashedTyped) : (S with type nde = H.nde and type fml = H.fml)
