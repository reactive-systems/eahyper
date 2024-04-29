(** Accepts formulae from the standard input and tests them for satisfiability.
    Each formula has to be on a separate line and empty lines are ignored.
    The input is terminated by EOF.
    @author Florian Widmann
 *)


(** Tests whether a string is "almost" empty.
    @param s A string.
    @return True iff the string is empty
    or contains only whitespaces.
 *)
let isEmptyString s =
  let rec empty i =
    if i < 0 then true
    else
      let c = String.get s i in
      if c = ' ' || c = '\009' then empty (pred i)
      else false
  in
  empty (pred (String.length s))


let printUsage () =
  print_endline "Usage: \"pltl <solver> [<verbose>]\" where";
  print_endline "       <solver> in { graph | tree }";
  print_endline "       <verbose> = any (second) argument";
  exit 1

let counter = ref 0

let _ = 
  if Array.length Sys.argv < 2 then printUsage()
  else
    let choice = Sys.argv.(1) in
    let _ =
      match choice with
      | "graph"
      | "tree" -> ()
      | _ -> printUsage ()
    in
    let verb = Array.length Sys.argv > 2 in
    let printRes sat =
      if not verb then
        print_endline (if sat then "satisfiable\n" else "unsatisfiable\n")
      else ()
    in
    try
      while true do
        let input = read_line () in
        if not (isEmptyString input) then
          let f = PLTLFormula.importFormula input in
          incr counter;
          print_string ("\nFormula " ^ (string_of_int !counter) ^ ": ");
          match choice with
          | "tree" -> printRes (PLTLTree.isSat ~verbose:verb f)
          | "graph" -> printRes (PLTLGraph.isSat ~verbose:verb f)
          | _ -> printUsage ()
        else ()
      done
    with End_of_file -> ()
