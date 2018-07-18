open Formula
open Printf

let verbose = ref false

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
let rec get_trace_variables_prefix f =
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

(* return list of atomic propositions of hyperltl_formula `f` *)
let rec get_atomic_props f =
  let deduplicate xs =
    let cons_uniq xs x = if List.mem x xs then xs else x :: xs in
    List.rev (List.fold_left cons_uniq [] xs)
  in
  deduplicate (get_atomic_props_ (discard_prefix f))

(* return list of used trace variables of formula `f` *)
let rec get_trace_variables_body_ f =
  match f with
    True | False -> []
  | Var (_, y) -> [y]
  | Not f | Next f | Finally f | Globally f -> get_trace_variables_body_ f
  | And (f, g) | Or (f, g) | Impl (f, g) | Equiv (f, g) | Until (f, g) |
    WeakUntil (f, g) | Release (f, g) ->
      get_trace_variables_body_ f @ get_trace_variables_body_ g

(* return list of used trace variables of hyperltl_formula `f` *)
let rec get_trace_variables_body f =
  get_trace_variables_body_ (discard_prefix f)

(* return list of duplicates in `xs` *)
let rec duplicates_ acc xs =
  match xs with
    [] -> acc
  | x :: xs ->
      if List.mem x xs then
        duplicates_ (x :: acc) (List.filter (fun y -> x != y) xs)
      else duplicates_ acc xs

(* wrapper for duplicates_ *)
let duplicates = duplicates_ []

(* return intersection of `xs` and `ys` *)
let intersection xs ys = List.filter (fun x -> List.mem x ys) xs

(* return difference of `xs` and `ys` *)
let difference xs ys = List.filter (fun x -> not (List.mem x ys)) xs

(* check syntax of hyperltl_formula `f` *)
let check_syntax f =
  let error = ref false in
  let trace_variables = get_trace_variables_prefix f in
  (* check if trace variables are unique *)
  let xs = duplicates trace_variables in
  List.iter
    (fun x ->
       error := true; eprintf "trace identifier %S is not unique\n%!" x)
    xs;
  (* check if atomic propositions and trace variables are disjunct *)
  let xs = intersection (get_atomic_props f) trace_variables in
  List.iter
    (fun x ->
       error := true;
       eprintf
         "identifier %S is used as trace identifier and as atomic proposition\n%!"
         x)
    xs;
  (* check if every trace variable is actually bound by a quantifier *)
  let xs = difference (get_trace_variables_body f) trace_variables in
  List.iter
    (fun x ->
       error := true; eprintf "trace identifier %S is not defined\n%!" x)
    xs;
  if !error then exit 1

type inputT =
    String of string
  | File of string
  | Stdin

let formula_of_input input =
  let f =
    let formula_of_channel ic =
      (* parse a hyperltl_formula from channel `ic` *)
      let f =
        Parser.parse_hyperltl_formula Lexer.lex (Lexing.from_channel ic)
      in
      close_in ic; f
    in
    match input with
      File file -> formula_of_channel (open_in file)
    | String str ->
        Parser.parse_hyperltl_formula Lexer.lex (Lexing.from_string str)
    | Stdin -> formula_of_channel stdin
  in
  check_syntax f; f

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
    [] -> True
  | [f] -> f
  | f :: fr -> And (f, construct_conjunction fr)

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

let input = ref (File "")
let input2 = ref (File "")
let do_reflexive = ref false
let do_symmetric = ref false
let do_transitive = ref false
let write_intermediate = ref false
let intermediate = ref ""
let enable_nnf = ref false
let solver_dir = ref ""

(* helper function to invoke an LTL-SAT solver *)
let invoke_tool name cmd formula analyse_output =
  if !verbose then printf "%s check...\n%!" name;
  if !write_intermediate then
    begin let oc = open_out !intermediate in
      output_string oc formula; close_out oc
    end;
  let (ic, oc) = Unix.open_process (!solver_dir ^ "/" ^ cmd) in
  output_string oc formula;
  close_out oc;
  let buf = Buffer.create 16 in
  (try while true do Buffer.add_channel buf ic 1 done with End_of_file -> ());
  let status = Unix.close_process (ic, oc) in
  begin match status with
    Unix.WEXITED 0 -> ()
  | _ -> eprintf "failure calling LTL-SAT solver %s\n%!" name; exit 1
  end;
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

type q_structure =
  None | ExistsOnly | ForallOnly | ExistsForall | ForallExist | Alternating

(* return the quantifier structure of hyperltl_formula `f` *)
let rec quantifier_structure f =
  match f with
    Body _ -> None
  | Exists (_, f) ->
      let qs = quantifier_structure f in
      begin match qs with
        None -> ExistsOnly
      | ExistsOnly -> ExistsOnly
      | ForallOnly -> ExistsForall
      | ExistsForall -> ExistsForall
      | ForallExist -> Alternating
      | Alternating -> Alternating
      end
  | Forall (_, f) ->
      let qs = quantifier_structure f in
      match qs with
        None -> ForallOnly
      | ExistsOnly -> ForallExist
      | ForallOnly -> ForallOnly
      | ExistsForall -> Alternating
      | ForallExist -> ForallExist
      | Alternating -> Alternating

(* transform hyperltl_formula `f` into an equisatisfiable ltl_formula depending on `f`'s quantifier structure *)
let transform formula =
  check_syntax formula;
  let formula = if !enable_nnf then nnf formula else formula in
  let plain_body = discard_prefix formula in
  match quantifier_structure formula with
    None | ForallOnly -> transform_forall plain_body
  | ExistsOnly -> transform_exists plain_body
  | ExistsForall -> transform_exists_forall formula
  | _ ->
      eprintf
        "at most one quantifier alternation, starting with exists, allowed\n%!";
      exit 1

let invoke_ref = ref invoke_aalta

let check_sat f =
  let ltl_formula = transform f in
  if !verbose then
    printf "Equisatisfiable LTL formula:\n%s\n\n%!" (ltl_str ltl_formula);
  !invoke_ref ltl_formula

let sat_mode () =
  let f = formula_of_input !input in
  if !verbose then
    printf "Check satisfiability of HyperLTL formula:\n%s\n\n%!"
      (hyperltl_str f);
  let sat = check_sat f in
  if !verbose then
    match sat with
      true -> printf "%s\nis satisfiable\n%!" (hyperltl_str f)
    | false -> printf "%s\nis not satisfiable\n%!" (hyperltl_str f)
  else printf "%s\n%!" (bool2sat_str sat)

let c_ref = ref 0
let only_one = ref false
let show_number = ref false

let multi_mode () =
  let ic =
    match !input with
      File file -> open_in file
    | Stdin -> stdin
    | _ -> eprintf "multi mode expects input via file or stdin\n%!"; exit 1
  in
  let lines =
    let lines_ref = ref [] in
    try while true do lines_ref := input_line ic :: !lines_ref done; [] with
      End_of_file -> close_in ic; List.rev !lines_ref
  in
  let i = ref 0 in
  let handle_line line =
    match line with
      "" -> ()
    | _ ->
        i := !i + 1;
        if !show_number && not !only_one then printf "formula(%d):\n%!" !i;
        if not !only_one || !only_one && !c_ref == !i then
          begin input := String line; sat_mode () end
  in
  List.iter handle_line lines

let check_impl f g =
  if !verbose then
    printf "Check if\n%s\nimplies\n%s\n\n%!" (hyperltl_str f)
      (hyperltl_str g);
  let (f, g) =
    match
      intersection (get_trace_variables_prefix f)
        (get_trace_variables_prefix g)
    with
      [] -> f, g
    | _ -> uniquify f g
  in
  let (f_exists_list, f_forall_list) = get_trace_variable_lists f in
  let (g_exists_list, g_forall_list) = get_trace_variable_lists g in
  if List.length f_exists_list > 0 && List.length f_forall_list > 0 ||
     List.length g_exists_list > 0 && List.length g_forall_list > 0
  then
    begin
      eprintf
        "only alternation-free HyperLTL formulas allowed for implication or equivalence checking";
      exit 1
    end;
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
  not (check_sat neg_impl)

let impl_mode () =
  let f = formula_of_input !input in
  let g = formula_of_input !input2 in
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
  let f = formula_of_input !input in
  let g = formula_of_input !input2 in
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

let check_reflexive f =
  if !verbose then
    printf "Check reflexivity of HyperLTL formula:\n%s\n\n%!"
      (hyperltl_str f);
  let modified_f =
    let (_, forall_list) = get_trace_variable_lists f in
    let body = discard_prefix f in
    let x = List.hd forall_list in
    let replaced_body =
      let rplc f y = replace f y ("_" ^ x) in
      List.fold_left rplc body forall_list
    in
    Exists ("_" ^ x, Body (Not replaced_body))
  in
  if !verbose then
    printf "Check if\n%s\nis unsatisfiable\n\n%!" (hyperltl_str modified_f);
  not (check_sat modified_f)

let check_symmetric f =
  if !verbose then
    printf "Check symmetry of HyperLTL formula:\n%s\n\n%!" (hyperltl_str f);
  let modified_f =
    let (_, forall_list) = get_trace_variable_lists f in
    let exists_list = List.map (fun x -> "_" ^ x) forall_list in
    let body = discard_prefix f in
    let replaced_body =
      List.fold_left2 replace body forall_list exists_list
    in
    let transposed_symm =
      let transposed_body =
        let transpose_1_2 =
          function
            x :: y :: xs -> y :: x :: xs
          | xs -> xs
        in
        List.fold_left2 replace body forall_list (transpose_1_2 exists_list)
      in
      Impl (replaced_body, transposed_body)
    in
    let symm_body =
      if List.length forall_list == 2 then transposed_symm
      else
        let cycled_symm =
          let n_cycled_body =
            let rotate_1 =
              function
                x :: xs -> xs @ [x]
              | xs -> xs
            in
            List.fold_left2 replace body forall_list (rotate_1 exists_list)
          in
          Impl (replaced_body, n_cycled_body)
        in
        And (transposed_symm, cycled_symm)
    in
    let add_exists id f = Exists (id, f) in
    List.fold_right add_exists exists_list (Body (Not symm_body))
  in
  if !verbose then
    printf "Check if\n%s\nis unsatisfiable\n\n%!" (hyperltl_str modified_f);
  not (check_sat modified_f)

let check_transitive f =
  if !verbose then
    printf "Check transitivity of HyperLTL formula:\n%s\n\n%!"
      (hyperltl_str f);
  let (_, forall_list) = get_trace_variable_lists f in
  if List.length forall_list != 2 then
    begin
      eprintf "transitivity only defined for two forall quantifiers\n%!";
      exit 1
    end;
  let modified_f =
    let (x, y) = List.nth forall_list 0, List.nth forall_list 1 in
    let body = discard_prefix f in
    let left = replace (replace body x "_x") y "_y" in
    let middle = replace (replace body x "_y") y "_z" in
    let right = replace (replace body x "_x") y "_z" in
    Exists
      ("_x",
       Exists
         ("_y", Exists ("_z", Body (Not (Impl (And (left, middle), right))))))
  in
  if !verbose then
    printf "Check if\n%s\nis unsatisfiable\n\n%!" (hyperltl_str modified_f);
  not (check_sat modified_f)

let check_relations f =
  if !do_reflexive then
    begin match check_reflexive f with
      false ->
        if !verbose then printf "%s\nnot reflexive\n\n%!" (hyperltl_str f)
        else printf "not reflexive\n%!"
    | true ->
        if !verbose then printf "%s\nreflexive\n\n%!" (hyperltl_str f)
        else printf "reflexive\n%!"
    end;
  if !do_symmetric then
    begin match check_symmetric f with
      false ->
        if !verbose then printf "%s\nnot symmetric\n\n%!" (hyperltl_str f)
        else printf "not symmetric\n%!"
    | true ->
        if !verbose then printf "%s\nsymmetric\n\n%!" (hyperltl_str f)
        else printf "symmetric\n%!"
    end;
  if !do_transitive then
    match check_transitive f with
      false ->
        if !verbose then printf "%s\nnot transitive\n\n%!" (hyperltl_str f)
        else printf "not transitive\n%!"
    | true ->
        if !verbose then printf "%s\ntransitive\n\n%!" (hyperltl_str f)
        else printf "transitive\n%!"

let relations_mode () =
  let f = formula_of_input !input in
  if !verbose then printf "HyperLTL formula:\n%s\n\n%!" (hyperltl_str f);
  begin match quantifier_structure f with
    ForallOnly -> ()
  | _ ->
      eprintf "only forall quantifiers allowed for relation analysis\n%!";
      exit 1
  end;
  check_relations f


let print_usage = ref true
let mode_ref = ref sat_mode

let spec_list =
  ["-f", Arg.String (fun f -> input := File f; print_usage := false),
   "The file containing the formula to check.";
   "-fs", Arg.String (fun f -> input := String f; print_usage := false),
   "The formula to check.";
   "--stdin", Arg.Unit (fun () -> input := Stdin; print_usage := false),
   "Read formula from stdin.";
   "-m",
   Arg.String
     (fun f -> input := File f; mode_ref := multi_mode; print_usage := false),
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
   "-i", Arg.String (fun i -> input2 := File i; mode_ref := impl_mode),
   "The file containing the formula to imply.";
   "-is", Arg.String (fun i -> input2 := String i; mode_ref := impl_mode),
   "The formula to imply.";
   "-e", Arg.String (fun e -> input2 := File e; mode_ref := equiv_mode),
   "The file containing the formula to equal.";
   "-es", Arg.String (fun e -> input2 := String e; mode_ref := equiv_mode),
   "The formula to equal.";
   "-r",
   Arg.Unit (fun () -> mode_ref := relations_mode; do_reflexive := true),
   "Test for reflexivity.";
   "--reflexive",
   Arg.Unit (fun () -> mode_ref := relations_mode; do_reflexive := true),
   "Test for reflexivity.";
   "-s",
   Arg.Unit (fun () -> mode_ref := relations_mode; do_symmetric := true),
   "Test for symmetry.";
   "--symmetric",
   Arg.Unit (fun () -> mode_ref := relations_mode; do_symmetric := true),
   "Test for symmetricy.";
   "-t",
   Arg.Unit (fun () -> mode_ref := relations_mode; do_transitive := true),
   "Test for transitivity.";
   "--transitive",
   Arg.Unit (fun () -> mode_ref := relations_mode; do_transitive := true),
   "Test for transitivity.";
   "-wi", Arg.String (fun f -> intermediate := f; write_intermediate := true),
   "The file to write intermediate LTL formula in.";
   "--nnf", Arg.Set enable_nnf,
   "Enable negated normal form representation. (default: false)"]
let arg_failure arg = raise (Arg.Bad ("Bad argument: " ^ arg))
let usage_msg =
  "./eahyper.native ((-f formula_file|-fs formula) ([(-i formula_file|-is formula)|(-e formula_file|-es formula)] | [-r|--reflexive] [-s|--symmetric] [-t|--transitive])) | (-m formulae_file [-c n][--cv]) [--aalta|--pltl] [--nnf] [-v|--verbose] [-wi file]"

let main =
  begin match Sys.getenv_opt "EAHYPER_SOLVER_DIR" with
    None | Some "" ->
      eprintf "EAHYPER_SOLVER_DIR environment variable was not set\n%!";
      exit 1
  | Some dir -> solver_dir := dir
  end;
  Arg.parse spec_list arg_failure usage_msg;
  if !print_usage then begin Arg.usage spec_list usage_msg; exit 1 end;
  !mode_ref ()
