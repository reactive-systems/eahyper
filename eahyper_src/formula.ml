open Printf

type ltl_formula =
    LTLTrue
  | LTLFalse
  | LTLVar of string
  | LTLNot of ltl_formula
  | LTLOr of ltl_formula * ltl_formula
  | LTLAnd of ltl_formula * ltl_formula
  | LTLImpl of ltl_formula * ltl_formula
  | LTLEquiv of ltl_formula * ltl_formula
  | LTLNext of ltl_formula
  | LTLUntil of ltl_formula * ltl_formula
  | LTLWeakUntil of ltl_formula * ltl_formula
  | LTLRelease of ltl_formula * ltl_formula
  | LTLFinally of ltl_formula
  | LTLGlobally of ltl_formula

type formula =
    True
  | False
  | Var of string * string
  | Not of formula
  | Or of formula * formula
  | And of formula * formula
  | Impl of formula * formula
  | Equiv of formula * formula
  | Next of formula
  | Until of formula * formula
  | WeakUntil of formula * formula
  | Release of formula * formula
  | Finally of formula
  | Globally of formula

type hyperltl_formula =
    Body of formula
  | Exists of string * hyperltl_formula
  | Forall of string * hyperltl_formula

exception Identifier_notunique of string
exception Identifier_rebound of string
exception Identifier_unbound of string
exception Error of string

let rec aalta_ltl_str_ buf f =
  let addb = Buffer.add_string buf in
  let rec_ = aalta_ltl_str_ buf in
  match f with
    LTLTrue -> addb "True"
  | LTLFalse -> addb "False"
  | LTLVar s -> addb s
  | LTLNot f -> addb "(~ "; rec_ f; addb ")"
  | LTLOr (f, g) -> addb "("; rec_ f; addb " | "; rec_ g; addb ")"
  | LTLAnd (f, g) -> addb "("; rec_ f; addb " & "; rec_ g; addb ")"
  | LTLImpl (f, g) -> addb "("; rec_ f; addb " -> "; rec_ g; addb ")"
  | LTLEquiv (f, g) -> addb "("; rec_ f; addb " <-> "; rec_ g; addb ")"
  | LTLNext f -> addb "(X "; rec_ f; addb ")"
  | LTLUntil (f, g) -> addb "("; rec_ f; addb " U "; rec_ g; addb ")"
  | LTLWeakUntil (f, g) -> rec_ (LTLRelease (g, LTLOr (f, g)))
  | LTLRelease (f, g) -> addb "("; rec_ f; addb " R "; rec_ g; addb ")"
  | LTLFinally f -> addb "(F "; rec_ f; addb ")"
  | LTLGlobally f -> addb "(G "; rec_ f; addb ")"

let aalta_ltl_str f =
  let buf = Buffer.create 0 in
  aalta_ltl_str_ buf f; let str = Buffer.contents buf in Buffer.reset buf; str

let rec pltl_ltl_str_ buf f =
  let addb = Buffer.add_string buf in
  let rec_ = pltl_ltl_str_ buf in
  match f with
    LTLTrue -> addb "True"
  | LTLFalse -> addb "False"
  | LTLVar s -> addb s
  | LTLNot f -> addb "(~ "; rec_ f; addb ")"
  | LTLOr (f, g) -> addb "("; rec_ f; addb " | "; rec_ g; addb ")"
  | LTLAnd (f, g) -> addb "("; rec_ f; addb " & "; rec_ g; addb ")"
  | LTLImpl (f, g) -> addb "("; rec_ f; addb " => "; rec_ g; addb ")"
  | LTLEquiv (f, g) -> addb "("; rec_ f; addb " <=> "; rec_ g; addb ")"
  | LTLNext f -> addb "(X "; rec_ f; addb ")"
  | LTLUntil (f, g) -> addb "("; rec_ f; addb " U "; rec_ g; addb ")"
  | LTLWeakUntil (f, g) -> rec_ (LTLOr (LTLUntil (f, g), LTLGlobally f))
  | LTLRelease (f, g) -> rec_ (LTLNot (LTLUntil (LTLNot f, LTLNot g)))
  | LTLFinally f -> addb "(F "; rec_ f; addb ")"
  | LTLGlobally f -> addb "(G "; rec_ f; addb ")"

let pltl_ltl_str f =
  let buf = Buffer.create 0 in
  pltl_ltl_str_ buf f; let str = Buffer.contents buf in Buffer.reset buf; str

let ltl_str = aalta_ltl_str

let rec str_ buf f =
  let addb = Buffer.add_string buf in
  let rec_ = str_ buf in
  match f with
    True -> addb "True"
  | False -> addb "False"
  | Var (a, x) -> addb a; addb "_"; addb x
  | Not f -> addb "(~ "; rec_ f; addb ")"
  | Or (f, g) -> addb "("; rec_ f; addb " | "; rec_ g; addb ")"
  | And (f, g) -> addb "("; rec_ f; addb " & "; rec_ g; addb ")"
  | Impl (f, g) -> addb "("; rec_ f; addb " -> "; rec_ g; addb ")"
  | Equiv (f, g) -> addb "("; rec_ f; addb " <-> "; rec_ g; addb ")"
  | Next f -> addb "(X "; rec_ f; addb ")"
  | Until (f, g) -> addb "("; rec_ f; addb " U "; rec_ g; addb ")"
  | WeakUntil (f, g) -> addb "("; rec_ f; addb " W "; rec_ g; addb ")"
  | Release (f, g) -> addb "("; rec_ f; addb " R "; rec_ g; addb ")"
  | Finally f -> addb "(F "; rec_ f; addb ")"
  | Globally f -> addb "(G "; rec_ f; addb ")"

let rec hyperltl_str_ buf f =
  let addb = Buffer.add_string buf in
  let rec_ = hyperltl_str_ buf in
  match f with
    Exists (v, f) -> addb "exists "; addb v; addb ". "; rec_ f
  | Forall (v, f) -> addb "forall "; addb v; addb ". "; rec_ f
  | Body f -> str_ buf f

let hyperltl_str f =
  let buf = Buffer.create 0 in
  hyperltl_str_ buf f; let str = Buffer.contents buf in Buffer.reset buf; str

let rec nnf_ f =
  match f with
    Not f ->
      let rec nnnf f =
        match f with
          True -> False
        | False -> True
        | Var (_, _) -> Not f
        | Not f -> nnf_ f
        | Or (f, g) -> And (nnnf f, nnnf g)
        | And (f, g) -> Or (nnnf f, nnnf g)
        | Impl (f, g) -> nnnf (Or (Not f, g))
        | Equiv (f, g) -> nnnf (And (Impl (f, g), Impl (g, f)))
        | Next f -> Next (nnnf f)
        | Finally f -> nnnf (Until (True, f))
        | Globally f -> nnnf (Release (False, f))
        | Until (f, g) -> Release (nnnf f, nnnf g)
        | WeakUntil (f, g) ->
            let (f, g) = nnnf f, nnnf g in Until (g, And (f, g))
        | Release (f, g) -> Until (nnnf f, nnnf g)
      in
      nnnf f
  | Or (f, g) -> Or (nnf_ f, nnf_ g)
  | And (f, g) -> And (nnf_ f, nnf_ g)
  | Impl (f, g) -> nnf_ (Or (Not f, g))
  | Equiv (f, g) ->
      let (f, g) = nnf_ f, nnf_ g in And (Impl (f, g), Impl (g, f))
  | Next f -> Next (nnf_ f)
  | Finally f -> nnf_ (Until (True, f))
  | Globally f -> nnf_ (Release (False, f))
  | Until (f, g) -> Until (nnf_ f, nnf_ g)
  | WeakUntil (f, g) -> let (f, g) = nnf_ f, nnf_ g in Release (g, Or (f, g))
  | Release (f, g) -> Release (nnf_ f, nnf_ g)
  | f -> f

let rec nnf =
  function
    Body f -> Body (nnf_ f)
  | Exists (id, f) -> Exists (id, nnf f)
  | Forall (id, f) -> Forall (id, nnf f)
