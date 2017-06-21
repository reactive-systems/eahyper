type altToken =
  | Kwd of string
  | Ident of string
  | Int of int

val make_lexer : string list -> string -> altToken Stream.t
val make_lexer_file : ?comment:string -> string list -> in_channel -> altToken Stream.t

val printToken : altToken -> unit
val printError : (string -> exn) -> ?t:altToken -> ?ts:altToken Stream.t -> string -> 'a

val getKws : (string -> exn) -> altToken Stream.t -> string list -> unit
