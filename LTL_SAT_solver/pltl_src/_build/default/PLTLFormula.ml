(** This module implements PLTL formulae
    (e.g. parsing, printing, (de-)constructing, ...).
    @author Florian Widmann
 *)


module HC = HashConsing
module A = AltGenlex


(** A general exception for all kinds of errors
    that can happen in the tableau procedure.
    More specific information is given in the argument. 
 *)
exception PLTLException of string


(** Defines PLTL formulae.
 *)
type formula = 
  | TRUE
  | FALSE
  | AP of string
  | NOT of formula
  | X of formula
  | EV of formula
  | AW of formula
  | EQU of formula * formula
  | IMP of formula * formula
  | OR of formula * formula
  | AND of formula * formula
  | UN of formula * formula 
  | BF of formula * formula


(** Determines the size of a formula.
    Basically, it counts the symbols (without parentheses) of a formula.
    @param f A formula.
    @return The size of f.
 *)
let rec sizeFormula f =
  match f with
  | TRUE 
  | FALSE 
  | AP _ -> 1
  | NOT f1
  | X f1
  | EV f1
  | AW f1 -> succ (sizeFormula f1)
  | EQU (f1, f2) 
  | IMP (f1, f2)
  | OR (f1, f2)  
  | AND (f1, f2)
  | UN (f1, f2)
  | BF (f1, f2) -> succ (sizeFormula f1 + sizeFormula f2)


(** Appends a string representation of a formula to a string buffer.
    Parentheses are ommited where possible
    where the preference rules are defined as usual.
    @param sb A string buffer.
    @param f A formula.
 *)
let rec exportFormula_buffer sb f =
  let prio n lf =
    let prionr = function
      | EQU _ -> 0
      | IMP _  -> 1 
      | OR _ -> 2
      | AND _ -> 3
      | UN _ -> 4
      | BF _ -> 4
      | _ -> 5
    in
    if prionr lf < n then begin
      Buffer.add_char sb '(';
      exportFormula_buffer sb lf;
      Buffer.add_char sb ')'
    end
    else exportFormula_buffer sb lf
  in
  match f with
  | TRUE -> Buffer.add_string sb "True"
  | FALSE -> Buffer.add_string sb "False"
  | AP s -> Buffer.add_string sb s
  | NOT f1 ->
      Buffer.add_string sb "~";
      prio 5 f1
  | X f1 ->
      Buffer.add_string sb "X ";
      prio 5 f1
  | EV f1 ->
      Buffer.add_string sb "F ";
      prio 5 f1
  | AW f1 ->
      Buffer.add_string sb "G ";
      prio 5 f1
  | EQU (f1, f2) ->
      prio 0 f1;
      Buffer.add_string sb " <=> ";
      prio 0 f2
  | IMP (f1, f2) ->
      prio 2 f1;
      Buffer.add_string sb " => ";
      prio 2 f2
  | OR (f1, f2) ->
      prio 2 f1;
      Buffer.add_string sb " | ";
      prio 2 f2
  | AND (f1, f2) ->
      prio 3 f1;
      Buffer.add_string sb " & ";
      prio 3 f2
  | UN (f1, f2) ->
      prio 5 f1;
      Buffer.add_string sb " U ";
      prio 5 f2
  | BF (f1, f2) ->
      prio 5 f1;
      Buffer.add_string sb " B ";
      prio 5 f2

(** Converts a formula into a string representation.
    Parentheses are ommited where possible
    where the preference rules are defined as usual.
    @param f A formula.
    @return A string representing f.
 *)
let exportFormula f =
  let size = sizeFormula f in
  let sb = Buffer.create (2 * size) in
  exportFormula_buffer sb f;
  Buffer.contents sb


let mk_exn s = PLTLException s

(** These functions parse a token stream to obtain a formula.
    It is a standard recursive descent procedure.
    @param ts A token stream.
    @return The resulting (sub-)formula.
    @raise PLTLException if ts does not represent a formula.
 *)
let rec parse_equ ts =
  let f1 = parse_imp ts in
  match Stream.peek ts with
  | None -> f1
  | Some (A.Kwd "<=>") ->
      Stream.junk ts;
      let f2 = parse_equ ts in
      EQU (f1, f2)
  | _ -> f1

(** These functions parse a token stream to obtain a formula.
    It is a standard recursive descent procedure.
    @param ts A token stream.
    @return The resulting (sub-)formula.
    @raise PLTLException if ts does not represent a formula.
 *)
and parse_imp ts =
  let f1 = parse_or ts in
  match Stream.peek ts with
  | None -> f1
  | Some (A.Kwd "=>") ->
      Stream.junk ts;
      let f2 = parse_imp ts in
      IMP (f1, f2)
  | _ -> f1

(** These functions parse a token stream to obtain a formula.
    It is a standard recursive descent procedure.
    @param ts A token stream.
    @return The resulting (sub-)formula.
    @raise PLTLException if ts does not represent a formula.
 *)
and parse_or ts =
  let f1 = parse_and ts in
  match Stream.peek ts with
  | None -> f1
  | Some (A.Kwd "|") ->
      Stream.junk ts;
      let f2 = parse_or ts in
      OR (f1, f2)
  | _ -> f1

(** These functions parse a token stream to obtain a formula.
    It is a standard recursive descent procedure.
    @param ts A token stream.
    @return The resulting (sub-)formula.
    @raise PLTLException if ts does not represent a formula.
 *)
and parse_and ts =
  let f1 = parse_unbf ts in
  match Stream.peek ts with
  | None -> f1
  | Some (A.Kwd "&") ->
      Stream.junk ts;
      let f2 = parse_and ts in
      AND (f1, f2)
  | _ -> f1

(** These functions parse a token stream to obtain a formula.
    It is a standard recursive descent procedure.
    @param ts A token stream.
    @return The resulting (sub-)formula.
    @raise PLTLException if ts does not represent a formula.
 *)
and parse_unbf ts =
  let f1 = parse_rest ts in
  match Stream.peek ts with
  | None -> f1
  | Some (A.Kwd "U") ->
      Stream.junk ts;
      let f2 = parse_unbf ts in
      UN (f1, f2)
  | Some (A.Kwd "B") ->
      Stream.junk ts;
      let f2 = parse_unbf ts in
      BF (f1, f2)
  | _ -> f1

(** These functions parse a token stream to obtain a formula.
    It is a standard recursive descent procedure.
    @param ts A token stream.
    @return The resulting (sub-)formula.
    @raise PLTLException if ts does not represent a formula.
 *)
and parse_rest ts =
  let t = Stream.next ts in
  match t with
  | A.Kwd "X" -> 
      let f = parse_rest ts in
      X f
  | A.Kwd "F" -> 
      let f = parse_rest ts in
      EV f
  | A.Kwd "G" -> 
      let f = parse_rest ts in
      AW f
  | A.Kwd "(" -> 
      let f = parse_equ ts in
      let _ =
        match Stream.next ts with
        | A.Kwd ")" -> ()
        | t -> A.printError mk_exn ~t ~ts "\")\" expected: "
      in
      f
  | A.Kwd "~" ->
      let f = parse_rest ts in
      NOT f
  | A.Kwd "True" -> TRUE
  | A.Kwd "False" -> FALSE
  | A.Ident s -> AP s
  | t -> A.printError mk_exn ~t ~ts
        "\"X\", \"F\", \"G\", \"~\", \"(\", \"True\", \"False\", or <ident> expected: "

let keywords =
    ["(";")";"<=>";"=>";"|";"&";"U";"B";"~";"X";"F";"G";"True";"False"] 

let lexer = A.make_lexer keywords

(** Parses a string to obtain a formula.
    @param s A string representing a formula.
    @return The resulting formula.
    @raise PLTLException if s does not represent a formula.
 *)
let importFormula s =
  let ts = lexer s in
  try
    begin
      let f = parse_equ ts in
      let _ =
        match Stream.peek ts with
        | None -> ()
        | Some _ -> A.printError mk_exn ~ts "EOS expected: "
      in
      f
    end
  with Stream.Failure -> A.printError mk_exn ~ts "unexpected EOS"

let lexer_ic = A.make_lexer_file ~comment:"%" keywords

(** Parses an input channel to obtain a formula.
    @param ic An input channel.
    @return The conjunction of all formulae read from ic.
    @raise PLTLException if s does not represent a formula.
 *)
let importFormula_ic ic =
  let ts = lexer_ic ic in
  let rec readFormula acc =
    match Stream.peek ts with
    | None -> acc
    | Some _ ->
        let f = parse_equ ts in
        let nacc = AND (acc, f) in
        readFormula nacc
  in
  try
    let f = parse_equ ts in
    readFormula f
  with Stream.Failure -> A.printError mk_exn ~ts "unexpected EOS"


(** Substitutes some propositional variables in a formula.
    @param subl A list of pairs (s, fp) 
    where s is the name of a propositional variable and fp is a formula.
    @param f A formula.
    @return A formula f' where each propositional variable p
    such that (p, fp) is contained in subl is replaced by fp.
 *)
let rec substFormula subl f =
  match f with
  | TRUE
  | FALSE -> f
  | AP s -> if List.mem_assoc s subl then List.assoc s subl else f
  | NOT f1 ->
      let ft = substFormula subl f1 in
      if ft == f1 then f else NOT ft
  | X f1 ->
      let ft = substFormula subl f1 in
      if ft == f1 then f else X ft
  | EV f1 ->
      let ft = substFormula subl f1 in
      if ft == f1 then f else EV ft
  | AW f1 ->
      let ft = substFormula subl f1 in
      if ft == f1 then f else AW ft
  | EQU (f1, f2) ->
      let ft1 = substFormula subl f1 in
      let ft2 = substFormula subl f2 in
      if (f1 == ft1) && (f2 == ft2) then f 
      else EQU (ft1, ft2)
  | IMP (f1, f2) ->
      let ft1 = substFormula subl f1 in
      let ft2 = substFormula subl f2 in
      if (f1 == ft1) && (f2 == ft2) then f 
      else IMP (ft1, ft2)
  | OR (f1, f2) ->
      let ft1 = substFormula subl f1 in
      let ft2 = substFormula subl f2 in
      if (f1 == ft1) && (f2 == ft2) then f 
      else OR (ft1, ft2)
  | AND (f1, f2) ->
      let ft1 = substFormula subl f1 in
      let ft2 = substFormula subl f2 in
      if (f1 == ft1) && (f2 == ft2) then f 
      else AND (ft1, ft2)
  | UN (f1, f2) ->
      let ft1 = substFormula subl f1 in
      let ft2 = substFormula subl f2 in
      if (f1 == ft1) && (f2 == ft2) then f 
      else UN (ft1, ft2)
  | BF (f1, f2) ->
      let ft1 = substFormula subl f1 in
      let ft2 = substFormula subl f2 in
      if (f1 == ft1) && (f2 == ft2) then f 
      else BF (ft1, ft2)


(** Converts the negation of a formula to negation normal form
    by "pushing in" the negations "~".
    The symbols "EV", "AW", "<=>" and "=>"
    are substituted by their usual definitions.
    @param f A formula.
    @return A formula in negation normal form and not containing "<=>" or "=>"
    that is equivalent to ~f.
 *)
let rec nnfNeg f =
  match f with
  | TRUE -> FALSE
  | FALSE -> TRUE
  | AP _ -> NOT f
  | NOT f1 -> nnf f1
  | X f1 -> X (nnfNeg f1)
  | EV f1 -> AW (nnfNeg f1)
  | AW f1 -> UN (TRUE, nnfNeg f1)
  | EQU (f1, f2) -> OR (AND (nnf f1, nnfNeg f2), AND (nnf f2, nnfNeg f1))
  | IMP (f1, f2) -> AND (nnf f1, nnfNeg f2)
  | OR (f1, f2) -> AND (nnfNeg f1, nnfNeg f2)
  | AND (f1, f2) -> OR (nnfNeg f1, nnfNeg f2)
  | UN (f1, f2) -> BF (nnfNeg f1, nnf f2)
  | BF (f1, f2) -> UN (nnfNeg f1, nnf f2)
        
(** Converts a formula to negation normal form
    by "pushing in" the negations "~".
    The symbols "EV", "AW", "<=>" and "=>"
    are substituted by their usual definitions.
    @param f A formula.
    @return A formula in negation normal form and not containing "<=>" or "=>"
    that is equivalent to f.
 *)
and nnf f =
  match f with
  | TRUE
  | FALSE
  | AP _
  | NOT (AP _) -> f
  | NOT f1 -> nnfNeg f1
  | X f1 -> 
      let ft = nnf f1 in
      if ft == f1 then f else X ft
  | EV f1 -> UN (TRUE, nnf f1)
  | AW f1 ->
      let ft = nnf f1 in
      if ft == f1 then f else AW ft
  | EQU (f1, f2) -> AND (OR (nnfNeg f1, nnf f2), OR (nnfNeg f2, nnf f1))
  | IMP (f1, f2) -> OR (nnfNeg f1, nnf f2)
  | OR (f1, f2) ->
      let ft1 = nnf f1 in
      let ft2 = nnf f2 in
      if ft1 == f1 && ft2 == f2 then f else OR (ft1, ft2)
  | AND (f1, f2) ->
      let ft1 = nnf f1 in
      let ft2 = nnf f2 in
      if ft1 == f1 && ft2 == f2 then f else AND (ft1, ft2)
  | UN (f1, f2) ->
      let ft1 = nnf f1 in
      let ft2 = nnf f2 in
      if ft1 == f1 && ft2 == f2 then f else UN (ft1, ft2)
  | BF (f1, f2) ->
      let ft1 = nnf f1 in
      let ft2 = nnf f2 in
      if ft1 == f1 && ft2 == f2 then f else BF (ft1, ft2)


(** Simplifies a formula that is in negation normal form.
    @param f A formula in negation normal form.
    @return A formula in negation normal form that is equivalent to f.
    @raise PLTLException if f is not in negation normal form.
 *)
let rec simplifyFormula f =
  match f with
  | TRUE
  | FALSE
  | AP _
  | NOT (AP _) -> f
  | X f1 ->
      let ft = simplifyFormula f1 in
      begin
        match ft with
        | TRUE
        | FALSE -> ft
        | _ -> if ft == f1 then f else X ft
      end
  | OR (f1, f2) ->
      let ft1 = simplifyFormula f1 in
      let ft2 = simplifyFormula f2 in
      begin
        match ft1, ft2 with
        | TRUE, _ -> TRUE
        | FALSE, _ -> ft2
        | _, TRUE -> TRUE
        | _, FALSE -> ft1
        | _, _ ->
            if (f1 == ft1) && (f2 == ft2) then f 
            else OR (ft1, ft2)
      end
  | AND (f1, f2) ->
      let ft1 = simplifyFormula f1 in
      let ft2 = simplifyFormula f2 in
      begin
        match ft1, ft2 with
        | TRUE, _ -> ft2
        | FALSE, _ -> FALSE
        | _, TRUE -> ft1
        | _, FALSE -> FALSE
        | _, _ ->
            if (f1 == ft1) && (f2 == ft2) then f 
            else AND (ft1, ft2)
      end
  | AW f1 ->
      let ft = simplifyFormula f1 in
      begin
        match ft with
        | TRUE
        | FALSE -> ft
        | _ -> if ft == f1 then f else AW ft
      end
  | UN (f1, f2) ->
      let ft1 = simplifyFormula f1 in
      let ft2 = simplifyFormula f2 in
      begin
        match ft1, ft2 with
        | _, TRUE -> TRUE
        | _, FALSE -> FALSE
        | FALSE, _ -> ft2
        | _, _ ->
            if (f1 == ft1) && (f2 == ft2) then f 
            else UN (ft1, ft2)
      end
  | BF (f1, f2) ->
      let ft1 = simplifyFormula f1 in
      let ft2 = simplifyFormula f2 in
      begin
        match ft1, ft2 with
        | _, TRUE -> FALSE
        | _, FALSE -> TRUE
        | TRUE, _ -> nnfNeg ft2
        | x, y when x = nnfNeg y -> x
        | _, _ ->
            if (f1 == ft1) && (f2 == ft2) then f 
            else BF (ft1, ft2)
      end
  | _ -> raise (PLTLException "Formula is not in negation normal form.")


(** Destructs an atomic proposition.
    @param f An atomic proposition.
    @return The name of the atomic proposition.
    @raise PLTLException if f is not an atomic proposition.
 *)
let dest_ap f =
  match f with
  | AP s -> s
  | _ -> raise (PLTLException "Formula is not an atomic proposition.")

(** Destructs a negation.
    @param f A negation.
    @return The immediate subformula of the negation.
    @raise PLTLException if f is not a negation.
 *)
let dest_not f =
  match f with
  | NOT f1 -> f1
  | _ -> raise (PLTLException "Formula is not a negation.")

(** Destructs an X-formula.
    @param f An X-formula.
    @return The immediate subformula of the X-formula.
    @raise PLTLException if f is not an X-formula.
 *)
let dest_x f =
  match f with
  | X f1 -> f1
  | _ -> raise (PLTLException "Formula is not an X-formula.")

(** Destructs an EV-formula.
    @param f An EV-formula.
    @return The immediate subformula of the EV-formula.
    @raise PLTLException if f is not an EV-formula.
 *)
let dest_ev f =
  match f with
  | EV f1 -> f1
  | _ -> raise (PLTLException "Formula is not an EV-formula.")

(** Destructs an AW-formula.
    @param f An AW-formula.
    @return The immediate subformula of the AW-formula.
    @raise PLTLException if f is not an AW-formula.
 *)
let dest_aw f =
  match f with
  | AW f1 -> f1
  | _ -> raise (PLTLException "Formula is not an AW-formula.")

(** Destructs an equivalence.
    @param f An equivalence.
    @return The two immediate subformulae of the equivalence.
    @raise PLTLException if f is not an equivalence.
 *)
let dest_equ f =
  match f with
  | EQU (f1, f2) -> (f1, f2)
  | _ -> raise (PLTLException "Formula is not an equivalence.")

(** Destructs an implication.
    @param f An implication.
    @return The two immediate subformulae of the implication.
    @raise PLTLException if f is not an implication.
 *)
let dest_imp f =
  match f with
  | IMP (f1, f2) -> (f1, f2)
  | _ -> raise (PLTLException "Formula is not an implication.")

(** Destructs an or-formula.
    @param f An or-formula.
    @return The two immediate subformulae of the or-formula.
    @raise PLTLException if f is not an or-formula.
 *)
let dest_or f =
  match f with
  | OR (f1, f2) -> (f1, f2)
  | _ -> raise (PLTLException "Formula is not an or-formula.")

(** Destructs an and-formula.
    @param f An and-formula.
    @return The two immediate subformulae of the and-formula.
    @raise PLTLException if f is not an and-formula.
 *)
let dest_and f =
  match f with
  | AND (f1, f2) -> (f1, f2)
  | _ -> raise (PLTLException "Formula is not an and-formula.")

(** Destructs an UN-formula.
    @param f An UN-formula.
    @return The two immediate subformulae of the UN-formula.
    @raise PLTLException if f is not an UN-formula.
 *)
let dest_un f =
  match f with
  | UN (f1, f2) -> (f1, f2)
  | _ -> raise (PLTLException "Formula is not an UN-formula.")


(** Destructs an AW-formula.
    @param f An AW-formula.
    @return The two immediate subformulae of the AW-formula.
    @raise PLTLException if f is not an AW-formula.
 *)
let dest_bf f =
  match f with
  | BF (f1, f2) -> (f1, f2)
  | _ -> raise (PLTLException "Formula is not an AW-formula.")


(** Tests whether a formula is the constant True.
    @param f A formula.
    @return True iff f is the constant True.
 *)
let is_true f =
  match f with
  | TRUE -> true
  | _ -> false

(** Tests whether a formula is the constant False.
    @param f A formula.
    @return True iff f is the constant False.
 *)
let is_false f =
  match f with
  | FALSE -> true
  | _ -> false

(** Tests whether a formula is an atomic proposition.
    @param f A formula.
    @return True iff f is an atomic proposition.
 *)
let is_ap f =
  match f with
  | AP _ -> true
  | _ -> false

(** Tests whether a formula is a negation.
    @param f A formula.
    @return True iff f is a negation.
 *)
let is_not f =
  match f with
  | NOT _ -> true
  | _ -> false

(** Tests whether a formula is an X-formula.
    @param f A formula.
    @return True iff f is an X-formula.
 *)
let is_x f =
  match f with
  | X _ -> true
  | _ -> false

(** Tests whether a formula is an EV-formula.
    @param f A formula.
    @return True iff f is an EV-formula.
 *)
let is_ev f =
  match f with
  | EV _ -> true
  | _ -> false

(** Tests whether a formula is an AW-formula.
    @param f A formula.
    @return True iff f is an AW-formula.
 *)
let is_aw f =
  match f with
  | AW _ -> true
  | _ -> false

(** Tests whether a formula is an equivalence.
    @param f A formula.
    @return True iff f is an equivalence.
 *)
let is_equ f =
  match f with
  | EQU _ -> true
  | _ -> false

(** Tests whether a formula is an implication.
    @param f A formula.
    @return True iff f is an implication.
 *)
let is_imp f =
  match f with
  | IMP _ -> true
  | _ -> false

(** Tests whether a formula is an or-formula.
    @param f A formula.
    @return True iff f is an or-formula.
 *)
let is_or f =
  match f with
  | OR _ -> true
  | _ -> false

(** Tests whether a formula is an and-formula.
    @param f A formula.
    @return True iff f is an and-formula.
 *)
let is_and f =
  match f with
  | AND _ -> true
  | _ -> false

(** Tests whether a formula is an UN-formula.
    @param f A formula
    @return True iff f is an UN-formula.
 *)
let is_un f =
  match f with
  | UN _ -> true
  | _ -> false
        
(** Tests whether a formula is an BF-formula.
    @param f A formula.
    @return True iff f is an BF-formula.
 *)
let is_bf f =
  match f with
  | BF _ -> true
  | _ -> false

        
(** The constant True.
 *)
let const_true = TRUE

(** The constant False.
 *)
let const_false = FALSE
    
(** Constructs an atomic proposition.
    @param s The name of the atomic proposition.
    @return The atomic proposition with name s.
 *)
let const_ap s = AP s

(** Negates a formula.
    @param f A formula.
    @return The negation of f.
 *)
let const_not f = NOT f

(** Constructs an X-formula from a formula.
    @param f A formula.
    @return The formula X f.
 *)
let const_x f = X f

(** Constructs an EV-formula from a formula.
    @param f A formula.
    @return The formula EV f.
 *)
let const_ev f = EV f

(** Constructs an AW-formula from a formula.
    @param f A formula.
    @return The formula AW f.
 *)
let const_aw f = AW f

(** Constructs an equivalence from two formulae.
    @param f1 The first formula (LHS).
    @param f2 The second formula (LHS).
    @return The equivalence f1 <=> f2.
 *)
let const_equ f1 f2 = EQU (f1, f2)

(** Constructs an implication from two formulae.
    @param f1 The first formula (LHS).
    @param f2 The second formula (LHS).
    @return The implication f1 => f2.
 *)
let const_imp f1 f2 = IMP (f1, f2)

(** Constructs an or-formula from two formulae.
    @param f1 The first formula (LHS).
    @param f2 The second formula (LHS).
    @return The formula f1 | f2.
 *)
let const_or f1 f2 = OR (f1, f2)

(** Constructs an and-formula from two formulae.
    @param f1 The first formula (LHS).
    @param f2 The second formula (LHS).
    @return The formula f1 & f2.
 *)    
let const_and f1 f2 = AND (f1, f2)

(** Constructs an UN-formula from two formulae.
    @param f1 The first formula (LHS).
    @param f2 The second formula (LHS).
    @return The formula f1 U f2.
 *)    
let const_un f1 f2 = UN (f1, f2)

(** Constructs an BF-formula from two formulae.
    @param f1 The first formula (LHS).
    @param f2 The second formula (LHS).
    @return The formula f1 B f2.
 *)    
let const_bf f1 f2 = BF (f1, f2)


(** The number of constructors of type formula.
 *)
let numberOfTypes = 13

(** Maps a formula to an integer representing its type (e.g. or-formula).
    The assignment of integers to types is arbitrary,
    but it is guaranteed that different types 
    map to different integers
    and that the codomain of this function is [0..numberOfTypes-1].
    @param f A formula.
    @return An integer that represents the type of f.
 *)
let getTypeFormula f = 
  match f with
  | TRUE -> 0
  | FALSE -> 1
  | AP _ -> 2
  | NOT _ -> 3
  | X _ -> 4
  | EV _ -> 5
  | AW _ -> 6
  | EQU _ -> 7
  | IMP _ -> 8
  | OR _ -> 9
  | AND _ -> 10
  | UN _ -> 11
  | BF _ -> 12

(** Generates a function comp that compares two formula.
    The order that is defined by comp is lexicograhic.
    It depends on the given ranking of types of formulae.
    @param order A list containing exactly the numbers 0 to numberOfTypes-1.
    Each number represents a type
    and the list therefore induces a ranking on the types
    with the smallest type being the first in the list.
    @return A function comp that compares two formula.
    comp f1 f2 returns 0 iff f1 is equal to f2, 
    -1 if f1 is smaller than f2, and
    1 if f1 is greater than f2.
    @raise Failure if order is not of the required form.
 *)
let generateCompare order =
  let rec listOK = function
    | 0 -> true
    | n ->
        let nn = pred n in
        if List.mem nn order then listOK nn
        else false
  in
  let _ = 
    if (List.length order <> numberOfTypes) || not (listOK numberOfTypes) then
      raise (Failure "generateCompare: argument is not in the correct form")
  in
  let arrayOrder = Array.make numberOfTypes 0 in
  let _ = 
    for i = 0 to (numberOfTypes - 1) do
      let ty = List.nth order i in
      arrayOrder.(ty) <- i
    done
  in
  let rec comp f1 f2 =
    match f1, f2 with
    | TRUE, TRUE
    | FALSE, FALSE -> 0
    | AP s1, AP s2 -> compare s1 s2
    | NOT f1a, NOT f2a
    | X f1a, X f2a
    | EV f1a, EV f2a
    | AW f1a, AW f2a -> comp f1a f2a
    | OR (f1a, f1b), OR (f2a, f2b)
    | AND (f1a, f1b), AND (f2a, f2b)
    | UN (f1a, f1b), UN (f2a, f2b)
    | BF (f1a, f1b), BF (f2a, f2b)
    | EQU (f1a, f1b), EQU (f2a, f2b)
    | IMP (f1a, f1b), IMP (f2a, f2b) ->
        let res1 = comp f1a f2a in
        if res1 <> 0 then res1
        else comp f1b f2b
    | _ ->
        let t1 = getTypeFormula f1 in
        let r1 = arrayOrder.(t1) in
        let t2 = getTypeFormula f2 in
        let r2 = arrayOrder.(t2) in
        if r1 < r2 then (-1) else 1
  in
  comp

(** Defines a ranking of the different types of formulae
    such that the ranking of the types corresponds
    to the ranking of the tableau rules.
 *)
let aRanking = [ getTypeFormula (AND (TRUE, TRUE));
                 getTypeFormula (AW TRUE);
                 getTypeFormula (BF (TRUE, TRUE));
                 getTypeFormula (OR (TRUE, TRUE));
                 getTypeFormula (UN (TRUE, TRUE));
                 getTypeFormula (X TRUE);
                 getTypeFormula TRUE;
                 getTypeFormula FALSE;
                 getTypeFormula (AP "");
                 getTypeFormula (NOT TRUE);
                 getTypeFormula (EQU (TRUE, TRUE));
                 getTypeFormula (IMP (TRUE, TRUE));
                 getTypeFormula (EV TRUE) ]


(** Calculates all formulae
    that may be created in the tableau procedure (i.e. a kind of Fischer-Ladner closure).
    @param compF A function that compares formulae.
    @param nnf The initial formula of the tableau procedure
    which must be in negation normal form.
    @return A list containing all formulae of the closure in increasing order.
    @raise PLTLException if nnf is not in negation normal form.
 *)
let detClosure compF nnf =
  let module TSet = Set.Make(
    struct
      type t = formula
      let (compare : t -> t -> int) = compF
    end
   )
  in
  let rec detC fs f =
    if TSet.mem f fs then fs
    else
      let nfs = TSet.add f fs in
      match f with
      | TRUE
      | FALSE
      | AP _
      | NOT (AP _) -> nfs
      | X f1 ->
          detC nfs f1
      | OR (f1, f2)
      | AND (f1, f2) ->
          let nfs = detC nfs f1 in
          detC nfs f2
      | AW f1 ->
          let nfs = detC nfs f1 in
          detC nfs (X f)
      | UN (f1, f2) ->
          let nfs = detC nfs f2 in
          detC nfs (AND (f1, X f))
      | BF (f1, f2) ->
          let nfs = detC nfs (nnfNeg f2) in
          detC nfs (OR (f1, X f))
      | _ -> raise (PLTLException "Formula is not in negation normal form.")
  in
  let tset = TSet.empty in
  let tset = TSet.add TRUE tset in
  let tset = TSet.add FALSE tset in
  let tset = TSet.add (X TRUE) tset in
  let rset = detC tset nnf in
  TSet.elements rset


(** Hash-consed formulae, which are in negation normal form,
    such that structural and physical equality coincide.
 *)
type hcFormula = (hcFormula_node, formula) HC.hash_consed
and hcFormula_node =
  | HCTRUE
  | HCFALSE
  | HCAP of string
  | HCNOT of string
  | HCX of hcFormula
  | HCOR of hcFormula * hcFormula
  | HCAND of hcFormula * hcFormula
  | HCUN of hcFormula * hcFormula
  | HCBF of hcFormula * hcFormula


(** Determines whether two formula nodes are structurally equal.
    @param f1 The first formula node.
    @param f2 The second formula node.
    @return True iff f1 and f2 are structurally equal.
 *)
let equal_hcFormula_node f1 f2 =
  match f1, f2 with
  | HCTRUE, HCTRUE -> true
  | HCFALSE, HCFALSE -> true
  | HCAP s1, HCAP s2
  | HCNOT s1, HCNOT s2 -> compare s1 s2 = 0
  | HCX f1, HCX f2 -> f1 == f2
  | HCOR (f1a, f1b), HCOR (f2a, f2b)
  | HCAND (f1a, f1b), HCAND (f2a, f2b)
  | HCUN (f1a, f1b), HCUN (f2a, f2b)
  | HCBF (f1a, f1b), HCBF (f2a, f2b) -> f1a == f2a && f1b == f2b
  | _ -> false

(** Computes the hash value of a formula node.
    @param f A formula node.
    @return The hash value of f.
 *)
let hash_hcFormula_node f =
  match f with
  | HCTRUE -> 0
  | HCFALSE -> 1
  | HCAP s -> Hashtbl.hash s
  | HCNOT s -> Hashtbl.hash s + 1
  | HCX f1 -> 19 * f1.HC.hkey + 3
  | HCOR (f1, f2) -> 19 * (19 * f1.HC.hkey + f2.HC.hkey) + 5
  | HCAND (f1, f2) -> 19 * (19 * f1.HC.hkey + f2.HC.hkey) + 6
  | HCUN (f1, f2) -> 19 * (19 * f1.HC.hkey + f2.HC.hkey) + 7
  | HCBF (f1, f2) -> 19 * (19 * f1.HC.hkey + f2.HC.hkey) + 8

(** Determines the "real" formula of a formula node.
    @param f A formula node.
    @return The formula (in negation normal form) which corresponds to f.
 *)
let toFml_hcFormula_node f =
  match f with
  | HCTRUE -> TRUE
  | HCFALSE -> FALSE
  | HCAP s -> AP s
  | HCNOT s -> NOT (AP s)
  | HCX f1 -> X f1.HC.fml
  | HCOR (f1, f2) ->
      let fml1 = f1.HC.fml in
      let fml2 = f2.HC.fml in
      OR (fml1, fml2)
  | HCAND (f1, f2) ->
      let fml1 = f1.HC.fml in
      let fml2 = f2.HC.fml in
      AND (fml1, fml2)
  | HCUN (f1, f2) ->
      let fml1 = f1.HC.fml in
      let fml2 = f2.HC.fml in
      UN (fml1, fml2)
  | HCBF (f1, f2) ->
      let fml1 = f1.HC.fml in
      let fml2 = f2.HC.fml in
      BF (fml1, fml2)

(** Determines the negation (in negation normal form) of a formula node.
    @param f A formula node.
    @return The negation (in negation normal form) of f.
 *)
let negNde_hcFormula_node f =
  match f with
  | HCTRUE -> HCFALSE
  | HCFALSE -> HCTRUE
  | HCAP s -> HCNOT s
  | HCNOT s -> HCAP s
  | HCX f1 -> HCX f1.HC.neg
  | HCOR (f1, f2) ->
      let notf1 = f1.HC.neg in
      let notf2 = f2.HC.neg in
      HCAND (notf1, notf2)
  | HCAND (f1, f2) ->
      let notf1 = f1.HC.neg in
      let notf2 = f2.HC.neg in
      HCOR (notf1, notf2)
  | HCUN (f1, f2) ->
      let notf1 = f1.HC.neg in
      HCBF (notf1, f2)
  | HCBF (f1, f2) ->
      let notf1 = f1.HC.neg in
      HCUN (notf1, f2)

(** An instantiation of hash-consing for formulae.
 *)
module HcFormula = HC.Make(
  struct
    type nde = hcFormula_node
    type fml = formula
    let equal (n1 : nde) n2 = equal_hcFormula_node n1 n2
    let hash (n : nde) = hash_hcFormula_node n
    let negNde (n : nde) = negNde_hcFormula_node n
    let toFml (n : nde) = toFml_hcFormula_node n
  end
 )


(** An instantiation of a hash table (of the standard library)
    for hash-consed formulae. The test for equality
    and computing the hash value is done in constant time.
 *)
module HcFHt = Hashtbl.Make(
  struct
    type t = hcFormula
    let equal (f1 : t) f2 = f1.HC.tag = f2.HC.tag
    let hash (f : t) = f.HC.tag
  end
 )


(** Converts a formula into its hash-consed version.
    @param hcF A hash-cons table for formulae.
    @param f A formula in negation normal form.
    @return The hash-consed version of f.
    @raise PLTLException if f is not in negation normal form.
*)
let rec hc_formula hcF f =
  match f with
  | TRUE -> HcFormula.hashconsNeg hcF HCTRUE
  | FALSE -> HcFormula.hashconsNeg hcF HCFALSE
  | AP s -> HcFormula.hashconsNeg hcF (HCAP s)
  | NOT (AP s) -> HcFormula.hashconsNeg hcF (HCNOT s)
  | X f1 ->
      let tf1 = hc_formula hcF f1 in
      HcFormula.hashconsNeg hcF (HCX tf1)
  | AW f1 ->
      let tff = HcFormula.hashconsNeg hcF HCFALSE in
      let tf1 = hc_formula hcF f1 in
      HcFormula.hashconsNeg hcF (HCBF (tff, tf1.HC.neg))
  | OR (f1, f2) ->
      let tf1 = hc_formula hcF f1 in
      let tf2 = hc_formula hcF f2 in
      HcFormula.hashconsNeg hcF (HCOR (tf1, tf2))
  | AND (f1, f2) ->
      let tf1 = hc_formula hcF f1 in
      let tf2 = hc_formula hcF f2 in
      HcFormula.hashconsNeg hcF (HCAND (tf1, tf2))
  | UN (f1, f2) ->
      let tf1 = hc_formula hcF f1 in
      let tf2 = hc_formula hcF f2 in
      HcFormula.hashconsNeg hcF (HCUN (tf1, tf2))
  | BF (f1, f2) ->
      let tf1 = hc_formula hcF f1 in
      let tf2 = hc_formula hcF f2 in
      HcFormula.hashconsNeg hcF (HCBF (tf1, tf2))
  | _ -> raise (PLTLException "Formula is not in negation normal form.")

(** Calculates all formulae
    that may be created in the tableau procedure (i.e. a kind of Fischer-Ladner closure).
    @param nnf The initial formula of the tableau procedure
    which must be in negation normal form.
    @return A list containing all hash-consed formulae of the closure (in arbitrary order);
    the hash-consed version of nnf; and the hash-cons table.
    @raise PLTLException if nnf is not in negation normal form.
 *)
let detClosureHc nnf =
  let size = 2 * (sizeFormula nnf) in
  let hcF = HcFormula.create size in
  let hcnnf = hc_formula hcF nnf in
  let hcFht = HcFHt.create size in
  let tt = HcFormula.hashconsNeg hcF HCTRUE in
  HcFHt.add hcFht tt ();
  HcFHt.add hcFht (HcFormula.hashconsNeg hcF HCFALSE) ();
  HcFHt.add hcFht (HcFormula.hashconsNeg hcF (HCX tt)) ();
  let rec detC f =
    if HcFHt.mem hcFht f then ()
    else begin
      HcFHt.add hcFht f ();
      match f.HC.node with
      | HCTRUE
      | HCFALSE
      | HCAP _
      | HCNOT _ -> ()
      | HCX f1 -> detC f1
      | HCOR (f1, f2)
      | HCAND (f1, f2) ->
          detC f1;
          detC f2
      | HCUN (f1, f2) ->
          detC f2;
          let f3 = HcFormula.hashconsNeg hcF (HCX f) in
          let f4 = HcFormula.hashconsNeg hcF (HCAND (f1, f3)) in
          detC f4
      | HCBF (f1, f2) ->
          detC f2.HC.neg;
          let f3 = HcFormula.hashconsNeg hcF (HCX f) in
          let f4 = HcFormula.hashconsNeg hcF (HCOR (f1, f3)) in
          detC f4
    end
  in
  detC hcnnf;
  let flist = HcFHt.fold (fun f () acc -> f::acc) hcFht [] in
  (flist, hcnnf, hcF)
