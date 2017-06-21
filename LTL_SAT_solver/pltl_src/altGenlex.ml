(** An alternative for the module Genlex 
    because Genlex cannot deal with key words properly.
    @author Florian Widmann
 *)


(** The three different kinds of tokens
    that the lexer can recognise (cf. Genlex)
 *)
type altToken =
  | Kwd of string
  | Ident of string
  | Int of int

(** A tree branching on characters that contains all key words.
    The boolean variable at every node indicates whether the
    corresponding string is a key word itself (if it is not a key word
    then it must be a strict prefix of a key word).
 *)
type kwSTree = (char * kwTree) list
and kwTree = KWTree of bool * kwSTree


(** An instantiation of a Set (of the standard library) for characters.
 *)
module CSet = Set.Make(Char)

(** Creates a key word tree from a list of key words.
    @param keywords A list of strings representing key words.
    @return A key word tree stripped by the uppermost node
    (see description of type kwSTree).
 *)
let make_kwSTree keywords =
  let rec mk_kwTree i kwl =
    let fldList (iskw, cset, kwl1) s =
      if String.length s = i then (true, cset, kwl1)
      else (iskw, CSet.add s.[i] cset, s::kwl1)
    in
    let (isKw, cset, kwl1) = List.fold_left fldList (false, CSet.empty, []) kwl in
    let fldCSet c acc =
      let kwl2 = List.filter (fun s -> s.[i] = c) kwl1 in
      let subtree = mk_kwTree (succ i) kwl2 in
      (c, subtree)::acc
    in
    let reslst = CSet.fold fldCSet cset [] in
    KWTree (isKw, reslst)
  in
  match mk_kwTree 0 keywords with
  | KWTree (_, subtree) -> subtree


(** Produces a lexer that can recognise identifiers, integers,
    and a given list of key words.
    Identifiers are sequences containing "A..Z", "a..z", "0..9", "_", and "'"
    that do not start with a digit.
    Integers are sequences of "0".."9" and "-"
    that contain at least one digit and
    have "-" at most at the very beginning of the sequence.
    Furthermore the integers should not exceed
    the range of integers representable in type int.
    @param keywords A list of strings representing key words.
    All key words are accepted, but the empty string,
    key words starting with a whitespace,
    key words starting with a digit, and
    key words starting with a "-" followed by a digit
    are never matched (see below).
    @return A function f that accepts a string
    and returns a stream of tokens (of type altToken).
    Intuitively, when a new token is requested,
    f works as follows on the suffix of the string
    that has not yet been tokenised:
    It first strips all leading whitespaces.
    If the result is the empty string then it returns None;
    otherwise if it can match an integer it returns
    the int value corresponding to the longest match (in the number of characters);
    otherwise it returns the longest identifier or key word that it can match
    (if the result is a key word and a identifier, it is returned as key word).
    If none of the above applies then f raises a Stream.Error exception.
 *)
let make_lexer keywords =
  let kwstree = make_kwSTree keywords in
  let resfkt input =
    let lpos = ref 0 in
    let len = String.length input in
    let retNumber hpos =
      let pos = !lpos in
      let s = String.sub input pos (hpos - pos) in
      lpos := hpos;
      Some (Int (int_of_string s))
    in
    let rec next_number hpos =
      if hpos < len then
        let c = input.[hpos] in
        match c with
        | '0'..'9' -> next_number (succ hpos)
        | _ -> retNumber hpos  
      else retNumber hpos
    in
    let retToken idpos kwpos hpos =
      let pos = !lpos in
      if idpos > kwpos then
        let s = String.sub input pos (idpos - pos) in
        lpos := idpos;
        Some (Ident s)
      else
        if kwpos > pos then
          let s = String.sub input pos (kwpos - pos) in
          lpos := kwpos;
          Some (Kwd s)
        else
          let s1 = String.sub input pos (hpos - pos) in
          raise (Stream.Error ("Illegal token " ^ s1))
    in        
    let rec next_token hpos kwstr idpos kwpos =
      if hpos < len then
        let c = input.[hpos] in
        let idpos1 =
          if idpos = hpos then
            match c with
            | 'A'..'Z' | 'a'..'z' | '0'..'9' | '_' | '\'' -> succ idpos
            | _ -> idpos
          else idpos
        in
        let hpos1 = succ hpos in
        let (maybeKw, kwstr1, kwpos1) =
          try
            match List.assoc c kwstr with
            | KWTree (newKw, lst) -> (true, lst, if newKw then hpos1 else kwpos)
          with Not_found -> (false, [], kwpos)
        in
        if idpos1 = hpos1 || maybeKw then next_token hpos1 kwstr1 idpos1 kwpos1
        else retToken idpos1 kwpos1 hpos1
      else retToken idpos kwpos hpos
    in
    let rec streamfkt (_ : int) =
      let pos = !lpos in
      if pos < len then 
        match input.[pos] with
        | ' ' | '\010' | '\013' | '\009' | '\026' | '\012' -> incr lpos; streamfkt 0
        | '0'..'9' -> next_number (succ pos)
        | '-' -> 
            let npos = succ pos in
            if npos < len then
              match input.[npos] with
              | '0'..'9' -> next_number (succ npos)
              | _ -> next_token pos kwstree pos pos
            else next_token pos kwstree pos pos
        | _ -> next_token pos kwstree pos pos
      else None
    in
    Stream.from streamfkt
  in
  resfkt


(** Produces a lexer that can recognise identifiers, integers,
    and a given list of key words.
    Identifiers are sequences containing "A..Z", "a..z", "0..9", "_", and "'"
    that do not start with a digit.
    Integers are sequences of "0".."9" and "-"
    that contain at least one digit and
    have "-" at most at the very beginning of the sequence.
    Furthermore the integers should not exceed
    the range of integers representable in type int.
    @param comment An optional string representing a pseudo-keyword
    which indicates that the rest of the line is a comment.
    It will be treated as a keyword during matching,
    but when it is matched then it and the rest of the line will be ignored,
    and the next token is returned.
    Note that if there exists a real keyword which is equal to comment
    then the keyword will never be matched.
    @param keywords A list of strings representing key words.
    All key words are accepted, but the empty string,
    key words starting with a whitespace,
    key words containing a new line character,
    key words starting with a digit, and
    key words starting with a "-" followed by a digit
    are never matched (see below).
    @return A function f that accepts a file handler
    and returns a stream of tokens (of type altToken).
    Intuitively, when a new token is requested,
    f works as follows on the remainder of the file
    that has not yet been tokenised:
    It first strips all leading whitespaces.
    If the end of the file is reached then it returns None;
    otherwise if it can match an integer it returns
    the int value corresponding to the longest match (in the number of characters);
    otherwise it returns the longest identifier or key word that it can match
    (if the result is a key word and a identifier, it is returned as key word).
    If the matched key word is the comment string
    then it is not returned but the rest of the line is discarded
    and f is (recursively) invoked on the next line of the file.
    If none of the above applies then f raises a Stream.Error exception.
 *)
let make_lexer_file ?comment keywords =
  let (excmt, cmt, keywordsAndComment) =
    match comment with
    | None -> (false, "", keywords)
    | Some s -> (true, s, s::keywords)
  in
  let lexer = make_lexer keywordsAndComment in
  let resfkt file =
    let ts = ref (lexer "") in
    let rec streamfkt (_ : int) =
      match Stream.peek !ts with
      | None -> begin
          try
            ts := lexer (input_line file);
            streamfkt 0
          with End_of_file -> None
        end
      | Some _ ->
          match Stream.next !ts with
          | Kwd s when excmt && s = cmt -> begin
              try
                ts := lexer (input_line file);
                streamfkt 0
              with End_of_file -> None
            end
          | t -> Some t
    in
    Stream.from streamfkt
  in
  resfkt


(** Prints a token.
    @param t A token.
 *)
let printToken t =
  match t with
  | Kwd s -> print_string s
  | Ident s -> print_string s
  | Int n -> print_int n

(** Prints an error message and the rest of a token stream (if given)
    and then raises an exception.
    @param exc A function which accepts a string and constructs an exception.
    @param topt An optional token.
    @param ts An optional token stream.
    @param msg An error message
    @raise exc(.) This exception is always raised.
 *)
let printError exc ?t ?ts msg =
  let printTkn t =
    printToken t;
    print_string " "
  in
  print_string msg;
  let _ =
    match t with
    | None -> ()
    | Some t -> printTkn t
  in
  let _ =
    match ts with
    | None -> ()
    | Some ts -> Stream.iter printTkn ts
  in
  print_newline ();
  raise (exc "Parsing error")


(** Tries to read a given list of key words from a token stream.
    @param exc A function which accepts a string and constructs an exception.
    @param ts A token stream.
    @param kwl A list of key words.
    @raise exc(.) if the next tokens
    are not the key words in kwl (in the right order).
 *)
let rec getKws exc ts kwl =
  match kwl with
  | [] -> ()
  | kw::tl ->
      match Stream.next ts with
      | Kwd s when s = kw -> getKws exc ts tl
      | t -> printError exc ~t ("key word \"" ^ kw ^ "\" expected: ")
