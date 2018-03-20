open Formula
open Printf

let verbose = ref false

(* parse a hyperltl_formula out of string `s` *)
let formula_of_string s =
  Parser.parse_hyperltl_formula Lexer.lex (Lexing.from_string s)

(* parse a hyperltl_formula out of file `file` *)
let formula_of_file file =
  let ic = open_in file in
  let f = Parser.parse_hyperltl_formula Lexer.lex (Lexing.from_channel ic) in
  close_in ic; f

(* return body of hyperltl_formula `f` *)
let rec discard_prefix f =
  match f with
    Body f -> f
  | Exists (_, f) | Forall (_, f) -> discard_prefix f

(*
 * existentially quantified trace variables are saved in first list
 * universally quantified trace variables are saved in second list
 *)
let rec get_trace_variable_lists_ f xs ys =
  match f with
    Body _ -> List.rev xs, List.rev ys
  | Exists (v, f) -> get_trace_variable_lists_ f (v :: xs) ys
  | Forall (v, f) -> get_trace_variable_lists_ f xs (v :: ys)

(* wrapper for get_trace_variable_lists_ *)
let get_trace_variable_lists f = get_trace_variable_lists_ f [] []

(* return list of bound/quantified trace variables of hyperltl_formula `f` *)
let rec get_trace_variables_in_prefix f =
  let (xs, ys) = get_trace_variable_lists f in xs @ ys

(* return list of atomic propositions of formula `f` *)
let rec get_atomic_props_ f =
  match f with
    True | False -> []
  | Var (x, _) -> [x]
  | Not f | Next f | Finally f | Globally f -> get_atomic_props_ f
  | And (f, g) | Impl (f, g) | Equiv (f, g) | Or (f, g) | Until (f, g) |
    WeakUntil (f, g) | Release (f, g) ->
      get_atomic_props_ f @ get_atomic_props_ g

let cons_uniq xs x = if List.mem x xs then xs else x :: xs
(* dedupliate list xs *)
let remove_from_left xs = List.rev (List.fold_left cons_uniq [] xs)

(* return list of atomic propositions of hyperltl_formula `f` *)
let rec get_atomic_props f =
  remove_from_left (get_atomic_props_ (discard_prefix f))

(* return list of used trace variables of formula `f` *)
let rec get_trace_variables_in_body_ f =
  match f with
    True | False -> []
  | Var (_, y) -> [y]
  | Not f | Next f | Finally f | Globally f -> get_trace_variables_in_body_ f
  | And (f, g) | Or (f, g) | Impl (f, g) | Equiv (f, g) | Until (f, g) |
    WeakUntil (f, g) | Release (f, g) ->
      get_trace_variables_in_body_ f @ get_trace_variables_in_body_ g

(* return list of used trace variables of hyperltl_formula `f` *)
let rec get_trace_variables_in_body f =
  get_trace_variables_in_body_ (discard_prefix f)


(* checks if trace variables are unique *)
let rec check_unique xs =
  match xs with
    [] -> ()
  | x :: xs ->
      if List.mem x xs then raise (Identifier_notunique x); check_unique xs

(* checks if atomic propositions and trace variables are disjunct *)
let rec check_membership xs ys =
  let hlp x = if List.mem x ys then raise (Identifier_rebound x) in
  List.iter hlp xs

(* checks if every trace variable is actually bound by a quantifier *)
let rec check_not_membership xs ys =
  let hlp x = if not (List.mem x ys) then raise (Identifier_unbound x) in
  List.iter hlp xs

(* (true, true) -> exists-forall formula
   (true, false) -> exists only formula
   (false, true) -> forall only formula
   (false, false) -> no quantifiers
*)
let rec check_quantifier_structure_ exists_seen forall_seen f =
  match f with
    Body _ -> exists_seen, forall_seen
  | Exists (_, f) ->
      if forall_seen then
        raise
          (Error
             "at most one quantifier alternation, starting with exist, allowed")
      else check_quantifier_structure_ true false f
  | Forall (_, f) -> check_quantifier_structure_ exists_seen true f

(* wrapper for check_quantifier_structure_ *)
let check_quantifier_structure = check_quantifier_structure_ false false

(* check for sanity of hyperltl_formula `f` *)
let elab f =
  let trace_variables = get_trace_variables_in_prefix f in
  begin try check_unique trace_variables with
    Identifier_notunique x ->
      raise
        (Error
           ("Trace identifier " ^ x ^
            " was not unique. Try to run with --make-unique ."))
  end;
  check_membership (get_atomic_props f) trace_variables;
  check_not_membership (get_trace_variables_in_body f) trace_variables

(* transform an only forall-quantified formula `f` into an equisatisfiable ltl_formula *)
let rec transform_forall f =
  match f with
    True -> LTLTrue
  | False -> LTLFalse
  | Var (x, _) -> LTLVar x
  | And (f, g) -> LTLAnd (transform_forall f, transform_forall g)
  | Or (f, g) -> LTLOr (transform_forall f, transform_forall g)
  | Impl (f, g) -> LTLImpl (transform_forall f, transform_forall g)
  | Equiv (f, g) -> LTLEquiv (transform_forall f, transform_forall g)
  | Until (f, g) -> LTLUntil (transform_forall f, transform_forall g)
  | WeakUntil (f, g) -> LTLWeakUntil (transform_forall f, transform_forall g)
  | Release (f, g) -> LTLRelease (transform_forall f, transform_forall g)
  | Not f -> LTLNot (transform_forall f)
  | Next f -> LTLNext (transform_forall f)
  | Finally f -> LTLFinally (transform_forall f)
  | Globally f -> LTLGlobally (transform_forall f)

(* transform an only exists-quantified formula `f` into an equisatisfiable ltl_formula *)
let rec transform_exists f =
  match f with
    True -> LTLTrue
  | False -> LTLFalse
  | Var (x, y) -> LTLVar (x ^ "_" ^ y)
  | And (f, g) -> LTLAnd (transform_exists f, transform_exists g)
  | Or (f, g) -> LTLOr (transform_exists f, transform_exists g)
  | Impl (f, g) -> LTLImpl (transform_exists f, transform_exists g)
  | Equiv (f, g) -> LTLEquiv (transform_exists f, transform_exists g)
  | Until (f, g) -> LTLUntil (transform_exists f, transform_exists g)
  | WeakUntil (f, g) -> LTLWeakUntil (transform_exists f, transform_exists g)
  | Release (f, g) -> LTLRelease (transform_exists f, transform_exists g)
  | Not f -> LTLNot (transform_exists f)
  | Next f -> LTLNext (transform_exists f)
  | Finally f -> LTLFinally (transform_exists f)
  | Globally f -> LTLGlobally (transform_exists f)

(* return a list with every permutation of `xs` with length `n` *)
let rec every_selection xs n =
  match n with
    0 -> [[]]
  | n ->
      let selections = every_selection xs (n - 1) in
      let add_elem_to_each_selection acc x =
        List.map (fun s -> x :: s) selections @ acc
      in
      List.fold_left add_elem_to_each_selection [] xs

(* replaces trace variable `a` with trace variable `b` in formula `f` *)
let rec replace f a b =
  let rplc f = replace f a b in
  match f with
    True -> True
  | False -> False
  | Var (x, y) -> if y = a then Var (x, b) else Var (x, y)
  | And (f, g) -> And (rplc f, rplc g)
  | Or (f, g) -> Or (rplc f, rplc g)
  | Impl (f, g) -> Impl (rplc f, rplc g)
  | Equiv (f, g) -> Equiv (rplc f, rplc g)
  | Until (f, g) -> Until (rplc f, rplc g)
  | WeakUntil (f, g) -> WeakUntil (rplc f, rplc g)
  | Release (f, g) -> Release (rplc f, rplc g)
  | Not f -> Not (rplc f)
  | Next f -> Next (rplc f)
  | Finally f -> Finally (rplc f)
  | Globally f -> Globally (rplc f)

(* add `s` to every trace variable of hyperltl_formula `f` in order to make return a unique new hyperltl_formula *)
let rec uniquify_ f s =
  match f with
    Body f ->
      let rec uniquify__ f =
        match f with
          True -> True
        | False -> False
        | Var (x, y) -> Var (x, y ^ "_" ^ s)
        | And (f, g) -> And (uniquify__ f, uniquify__ g)
        | Or (f, g) -> Or (uniquify__ f, uniquify__ g)
        | Impl (f, g) -> Impl (uniquify__ f, uniquify__ g)
        | Equiv (f, g) -> Equiv (uniquify__ f, uniquify__ g)
        | Until (f, g) -> Until (uniquify__ f, uniquify__ g)
        | WeakUntil (f, g) -> WeakUntil (uniquify__ f, uniquify__ g)
        | Release (f, g) -> Release (uniquify__ f, uniquify__ g)
        | Not f -> Not (uniquify__ f)
        | Next f -> Next (uniquify__ f)
        | Finally f -> Finally (uniquify__ f)
        | Globally f -> Globally (uniquify__ f)
      in
      Body (uniquify__ f)
  | Exists (x, f) -> Exists (x ^ "_" ^ s, uniquify_ f s)
  | Forall (x, f) -> Forall (x ^ "_" ^ s, uniquify_ f s)

(* return new version of hyperltl_formulas `f` and `g` with unique trace variables *)
let uniquify f g = uniquify_ f "0", uniquify_ g "1"

(* return conjunction of elements in `fs` *)
let rec construct_conjunction fs =
  match fs with
    [f] -> f
  | f :: fr -> And (f, construct_conjunction fr)
  | _ -> raise (Error "This should never happen.")

(* transform exists-forall-quantified hyperltl_formula `formula` into equisatisfiable ltl_formula *)
let transform_exists_forall formula =
  let body = discard_prefix formula in
  let (exists_list, forall_list) = get_trace_variable_lists formula in
  let selections = every_selection exists_list (List.length forall_list) in
  let replace_with_selection = List.fold_left2 replace body forall_list in
  let replacements = List.map replace_with_selection selections in
  let new_formula = construct_conjunction replacements in
  if !verbose then
    begin let new_hyperltl_formula =
      let add_exists id f = Exists (id, f) in
      List.fold_right add_exists exists_list (Body new_formula)
    in
      printf "Equisatisfiable HyperLTL formula:\n%s\n\n%!"
        (hyperltl_str new_hyperltl_formula)
    end;
  transform_exists new_formula

let bool2sat_str sat = if sat then "sat" else "unsat"

let formula_string = ref ""
let formula_string2 = ref ""
let formula_file = ref ""
let formula_file2 = ref ""
let from_file = ref true
let from_file2 = ref true
let write_intermediate = ref false
let intermediate = ref ""
let make_unique = ref false
let enable_nnf = ref false
let dir = ref "."

(* helper function to invoke an LTL-SAT solver *)
let invoke_tool name cmd formula analyse_output =
  if !verbose then printf "%s check...\n%!" name;
  if !write_intermediate then
    begin let oc = open_out !intermediate in
      output_string oc formula; close_out oc
    end;
  let (ic, oc) = Unix.open_process (!dir ^ "/" ^ cmd) in
  output_string oc formula;
  close_out oc;
  let buf = Buffer.create 16 in
  (try while true do Buffer.add_channel buf ic 1 done with End_of_file -> ());
  let _ = Unix.close_process (ic, oc) in
  let output = Buffer.contents buf in
  if !verbose then print_string output;
  let sat = analyse_output output in
  if !verbose then printf "...result: %s\n\n%!" (bool2sat_str sat); sat

let str_contains s1 s2 =
  let re = Str.regexp_string s2 in
  try ignore (Str.search_forward re s1 0); true with Not_found -> false

(* invoke pltl on ltl_formula `f` *)
let invoke_pltl f =
  invoke_tool "pltl" "pltl tree verbose" (pltl_ltl_str f)
    (fun o -> str_contains o "is sat")

(* invoke aalta on ltl_formula `f` *)
let invoke_aalta f =
  invoke_tool "Aalta_v2.0" "aalta" (aalta_ltl_str f)
    (fun o -> not (str_contains o "unsat"))

(* transform hyperltl_formula `f` into an equisatisfiable ltl_formula depending on `f`'s quantifier structure *)
let transform formula =
  let quantifier_structure = check_quantifier_structure formula in
  elab formula;
  let formula = if !enable_nnf then nnf formula else formula in
  let plain_body = discard_prefix formula in
  match quantifier_structure with
    false, _ -> transform_forall plain_body
  | true, false -> transform_exists plain_body
  | true, true -> transform_exists_forall formula

let invoke_ref = ref invoke_aalta

let default_mode () =
  let f =
    if !from_file then formula_of_file !formula_file
    else formula_of_string !formula_string
  in
  if !verbose then printf "HyperLTL formula:\n%s\n\n%!" (hyperltl_str f);
  let sat =
    let ltl_formula = transform f in
    if !verbose then
      printf "Equisatisfiable LTL formula:\n%s\n\n%!" (ltl_str ltl_formula);
    !invoke_ref ltl_formula
  in
  if !verbose then
    match sat with
      true -> printf "%s\nis satisfiable\n%!" (hyperltl_str f)
    | false -> printf "%s\nis not satisfiable\n%!" (hyperltl_str f)
  else print_endline (bool2sat_str sat)

let get_lines file =
  let lines = ref [] in
  let chan = open_in !formula_file in
  try while true do lines := input_line chan :: !lines done; [] with
    End_of_file -> close_in chan; List.rev !lines

let c_ref = ref 0
let only_one = ref false
let show_number = ref false

let multi_mode () =
  from_file := false;
  let i = ref 0 in
  let handle_line line =
    match line with
      "" -> ()
    | _ ->
        i := !i + 1;
        if !show_number && not !only_one then printf "formula(%d):\n%!" !i;
        if not !only_one || !only_one && !c_ref == !i then
          begin formula_string := line; default_mode () end
  in
  List.iter handle_line (get_lines !formula_file)

let check_impl f g =
  if !verbose then
    printf "Check if\n%s\nimplies\n%s\n\n%!" (hyperltl_str f)
      (hyperltl_str g);
  elab f;
  elab g;
  let (f, g) = if not !make_unique then f, g else uniquify f g in
  let (f_exists_list, f_forall_list) = get_trace_variable_lists f in
  let (g_exists_list, g_forall_list) = get_trace_variable_lists g in
  if List.length f_exists_list > 0 && List.length f_forall_list > 0 ||
     List.length g_exists_list > 0 && List.length g_forall_list > 0
  then
    raise
      (Error
         "only alternation-free HyperLTL formulas allowed for implication or equivalence checking");
  let neg_impl =
    let neg_impl_body =
      Body (And (discard_prefix f, Not (discard_prefix g)))
    in
    let add_forall id f = Forall (id, f) in
    let add_exists id f = Exists (id, f) in
    let tmp = List.fold_right add_forall f_forall_list neg_impl_body in
    let tmp = List.fold_right add_forall g_exists_list tmp in
    let tmp = List.fold_right add_exists g_forall_list tmp in
    List.fold_right add_exists f_exists_list tmp
  in
  if !verbose then
    printf "Check if\n%s\nis unsatisfiable\n\n%!" (hyperltl_str neg_impl);
  let sat =
    let ltl_formula = transform neg_impl in
    if !verbose then
      printf "Equisatisfiable LTL formula:\n%s\n\n%!" (ltl_str ltl_formula);
    !invoke_ref ltl_formula
  in
  not sat

let impl_mode () =
  let f =
    if !from_file then formula_of_file !formula_file
    else formula_of_string !formula_string
  in
  let g =
    if !from_file2 then formula_of_file !formula_file2
    else formula_of_string !formula_string2
  in
  (* check for empty exists_lists *)
  let sat = check_impl f g in
  match sat with
    true ->
      if !verbose then
        printf "%s\ndoes imply\n%s\n\n%!" (hyperltl_str f) (hyperltl_str g);
      printf "does imply\n%!"
  | false ->
      if !verbose then
        printf "%s\ndoes not imply\n%s\n\n%!" (hyperltl_str f)
          (hyperltl_str g);
      printf "does not imply\n%!"

let equiv_mode () =
  let f =
    if !from_file then formula_of_file !formula_file
    else formula_of_string !formula_string
  in
  let g =
    if !from_file2 then formula_of_file !formula_file2
    else formula_of_string !formula_string2
  in
  if !verbose then
    printf "Check if\n%s\nis equivalent to\n%s\n\n%!" (hyperltl_str f)
      (hyperltl_str g);
  let sat = check_impl f g && check_impl g f in
  match sat with
    true ->
      if !verbose then
        printf "%s\nis equivalent to\n%s\n\n%!" (hyperltl_str f)
          (hyperltl_str g);
      printf "is equivalent\n%!"
  | false ->
      if !verbose then
        printf "%s\nis not equivalent to\n%s\n\n%!" (hyperltl_str f)
          (hyperltl_str g);
      printf "is not equivalent\n%!"

let mode_ref = ref default_mode

let spec_list =
  ["-f", Arg.String (fun f -> formula_file := f; from_file := true),
   "The file containing the formula to check.";
   "-fs", Arg.String (fun f -> formula_string := f; from_file := false),
   "The formula to check.";
   "-m", Arg.String (fun f -> formula_file := f; mode_ref := multi_mode),
   "The file containing multiple formulae to check.";
   "-c", Arg.Int (fun c -> c_ref := c; only_one := true),
   "The number of the formula to check in multi mode.";
   "--cv", Arg.Set show_number, "Show number in multi mode. (default: false)";
   "--pltl", Arg.Unit (fun () -> invoke_ref := invoke_pltl),
   "Check with pltl.";
   "--aalta", Arg.Unit (fun () -> invoke_ref := invoke_aalta),
   "Check with aalta.";
   "-v", Arg.Set verbose, "Be verbose.";
   "--verbose", Arg.Set verbose, "Be verbose.";
   "-i", Arg.String (fun i -> formula_file2 := i; mode_ref := impl_mode),
   "The file containing the formula to imply.";
   "-is",
   Arg.String
     (fun i ->
        formula_string2 := i; from_file2 := false; mode_ref := impl_mode),
   "The formula to imply.";
   "-e", Arg.String (fun e -> formula_file2 := e; mode_ref := equiv_mode),
   "The file containing the formula to equal.";
   "-es",
   Arg.String
     (fun e ->
        formula_string2 := e; from_file2 := false; mode_ref := equiv_mode),
   "The formula to equal.";
   "-wi", Arg.String (fun f -> intermediate := f; write_intermediate := true),
   "The file to write intermediate LTL formula in.";
   "--make-unique", Arg.Set make_unique,
   "Make trace variables of different formulae unique. (default: false)";
   "--nnf", Arg.Set enable_nnf,
   "Enable negated normal form representation. (default: false)";
   "-d", Arg.Set_string dir,
   "The directory where the LTL-SAT solvers are located. (default: .)"]
let arg_failure arg = raise (Arg.Bad ("Bad argument: " ^ arg))
let usage_msg =
  "./eahyper.native ((-f formula_file| -fs formula) [(-i formula_file|-is formula)|(-e formula_file|-es formula)] | -m formulae_file [-c n][--cv]) [-d directory] [--aalta|--pltl] [--nnf] [--make-unique] [-v|--verbose] [-wi file]"

let main = Arg.parse spec_list arg_failure usage_msg; !mode_ref ()
