{
open Lexing
open Parser

exception SyntaxError of string

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_bol = lexbuf.lex_curr_pos;
               pos_lnum = pos.pos_lnum + 1
    }
}

let eol = '\n'
let space = [' ' '\t' '\r']
let digit = ['0'-'9']
let lower = ['a'-'z']
let upper = ['A'-'Z']
let alpha = lower | upper
let alnum = digit | alpha | '_'

rule lex = parse
  | eol                     { Lexing.new_line lexbuf; lex lexbuf }
  | space                   { lex lexbuf }
  | eof                     { EOF }
  | "True"                  { TRUE }
  | "False"                 { FALSE }
  | "!"                     { EXCLAM }
  | "~"                     { NOT }
  | "+"                     { PLUS }
  | "-"                     { MINUS }
  | "="                     { EQ }
  | "<"                     { LT }
  | "<=" | "≤"              { LE }
  | ">"                     { GT }
  | ">=" | "≥"              { GE }
  | "true"                  { TRUTH }
  | "false"                 { FALSENESS }
  | "/\\" | "&&" | "⋀"      { AND }
  | "\\/" | "||" | "⋁"      { OR }
  | "->"  | "→"             { IMPLY }
  | "//"                    { PAR }
  | "#"                     { SHARP }
  | "."  | "·"              { DOT }
  | "^*" | "*"  | "﹡"      { KLEENE }
  | "|-" | "=>" | "⤇"      { ENTAIL }
  | ","                     { COMMA }
  | ":"                     { COLON }
  | "::"                    { COLON2 }
  | "("                     { LPAREN }
  | ")"                     { RPAREN }
  | "{"                     { LBRACE }
  | "}"                     { RBRACE }
  | "bot" | "_|_" | "⏊"    { BOTTOM }
  | "emp" | "𝝐"             { EMPTY }
  | "?"                     { QUESTION }
  | '"'      { read_string (Buffer.create 17) lexbuf }
  | digit+ as n             { INT (int_of_string n) }
  | alpha alnum* as id      { IDENT id }
  (*| _                       { UNKNOWN }*)
  | eof { EOF }

  | _ { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }



(* part 5   *)

and read_string buf = parse
  | '"'       { STRING (Buffer.contents buf) }
  | '\\' '/'  { Buffer.add_char buf '/'; read_string buf lexbuf }
  | '\\' '\\' { Buffer.add_char buf '\\'; read_string buf lexbuf }
  | '\\' 'b'  { Buffer.add_char buf '\b'; read_string buf lexbuf }
  | '\\' 'f'  { Buffer.add_char buf '\012'; read_string buf lexbuf }
  | '\\' 'n'  { Buffer.add_char buf '\n'; read_string buf lexbuf }
  | '\\' 'r'  { Buffer.add_char buf '\r'; read_string buf lexbuf }
  | '\\' 't'  { Buffer.add_char buf '\t'; read_string buf lexbuf }
  | [^ '"' '\\']+
    { Buffer.add_string buf (Lexing.lexeme lexbuf);
      read_string buf lexbuf
    }
  | _ { raise (SyntaxError ("Illegal string character: " ^ Lexing.lexeme lexbuf)) }
  | eof { raise (SyntaxError ("String is not terminated")) }
