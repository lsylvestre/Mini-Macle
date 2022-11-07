
(* The type of tokens. *)

type token = 
  | WITH
  | WILDCARD
  | UP_IDENT of (string)
  | TYPE
  | TO_PACKET
  | TO
  | TIMES
  | TILDE
  | THEN
  | STRING_LIT of (string)
  | SIZE
  | SIGNAL
  | SHARP_LBRACKET_PIPE
  | SHARP
  | SEMI_SEMI
  | SEMICOL
  | RPAREN
  | RIGHT_ARROW
  | REC
  | RBRACKET
  | RAISE
  | QUOTE_TVAR of (string)
  | QUESTION_MARK
  | PLUS
  | PIPE_RBRACKET
  | PIPE_PIPE
  | PIPE
  | PARALLEL_AND
  | PAR
  | PACKET
  | OUTPUT
  | OF_PACKET
  | OF
  | NOT
  | NEQ
  | MOD
  | MINUS
  | MATCH
  | LT
  | LPAREN
  | LET
  | LEFT_ARROW
  | LE
  | LBRACKET
  | INVALID_ARG
  | INT_LIT of (int)
  | INPUT
  | IN
  | IF
  | IDENT of (string)
  | GT
  | GE
  | FUN
  | FOR
  | FAILURE
  | EQEQ
  | EQ
  | EOF
  | END
  | ELSE
  | DOT
  | DONE
  | DO
  | DIV
  | CONTINUE
  | COMMA
  | COLONEQ
  | COLCOL
  | COL
  | CIRCUIT
  | BOOL_LIT of (bool)
  | BEGIN
  | BANG
  | AUTOMATON
  | AND

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val exp_end: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Macle.circuit)
