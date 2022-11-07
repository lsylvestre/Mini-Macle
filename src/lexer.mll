{
  open Parser
  exception Eof

  let hashtbl_of_list_assoc l =
    let h = Hashtbl.create (List.length l) in
    List.iter (fun (k,v) -> Hashtbl.add h k v) l;
    h

  let keywords =
    hashtbl_of_list_assoc @@
     [ "circuit", CIRCUIT;
       "fun",   FUN;
       "type",  TYPE;
       "of",    OF;
       "true",  BOOL_LIT true;
       "false", BOOL_LIT false;
       "let",   LET;
       "and",   AND;
       "rec",   REC;
       "in",    IN;
       "begin", BEGIN;
       "end",   END;
       "mod",   MOD;
       "if",    IF;
       "then",  THEN;
       "else",  ELSE;
       "not",   NOT;
       "match", MATCH;
       "with",  WITH;
       "for",            FOR;
       "to",             TO;
       "do",             DO;
       "done",           DONE;
       "of_packet",      OF_PACKET;
       "to_packet",      TO_PACKET;
       "raise",        RAISE;
       "size",   SIZE;
       "signal", SIGNAL;
       "automaton", AUTOMATON;
       "continue", CONTINUE;
       "output", OUTPUT;
       "input", INPUT;
     ]
}

let tvar_ident = [''']['a'-'z'] ['a'-'z''A'-'Z''0'-'9''_''A'-'Z'''']*
let ident = ['a'-'z''_'] ['a'-'z''A'-'Z''0'-'9''_''A'-'Z'''']*
let up_ident = ['A'-'Z']['a'-'z''A'-'Z''0'-'9''_''A'-'Z'''']*

rule token = parse
| ident as id         { try Hashtbl.find keywords id with
                        | Not_found -> IDENT id }
| "Failure"           { FAILURE }
| "Invalid_arg"       { INVALID_ARG }
| up_ident as lxm     { UP_IDENT lxm }
| tvar_ident as lxm   { QUOTE_TVAR lxm }
| '('                 { LPAREN }
| ')'                 { RPAREN }
| ":="                { COLONEQ }
| "~"                 { TILDE }
| "#"                 { SHARP }
| "::"                { COLCOL }
| ','                 { COMMA }
| ';'                 { SEMICOL }
| '|'                 { PIPE }
| "->"                { RIGHT_ARROW }
| "||"                { PIPE_PIPE }
| (['0'-'9']+) as n  { INT_LIT (int_of_string n) }
| "+"                 { PLUS }
| "-"                 { MINUS }
| "*"                 { TIMES }
| "/"                 { DIV }
| "//"                { PAR }
| "<"                 { LT }
| "<="                { LE }
| ">"                 { GT }
| ">="                { GE }
| "="                 { EQ }
| "=="                { EQEQ }
| "<>"                { NEQ }
| "&&."               { PARALLEL_AND }
| "["                 { LBRACKET }
| "]"                 { RBRACKET }
| "#[|"               { SHARP_LBRACKET_PIPE }
| "|]"                { PIPE_RBRACKET }
| ['?']               { QUESTION_MARK }
| ['!']               { BANG }
| ['.']               { DOT }
| [':']               { COL }
| "<-"                { LEFT_ARROW }
| ['"']([^'"']* as s)['"'] { STRING_LIT s }
| ['_']               { WILDCARD }
| ['\n' ]             { (Lexing.new_line lexbuf) ; (token lexbuf) }
| [' ' '\t']          { token lexbuf }
| ";;"                { SEMI_SEMI }
| eof                 { EOF }
| "(*"                { comment lexbuf }
| _  as lxm           { failwith (Printf.sprintf "Unexpected character: %c"  lxm) }

and comment = parse
| "*)" { token lexbuf }
| _    { comment lexbuf }
