
open Pretty
open Ast

exception Foo of string

let string_of_param (p : param) : string =
  match p with 
  | IN str -> "in " ^ str 
  | OUT str -> "out " ^ str
  ;;

let string_of_literal (l:literal) : string = 
  match l with 
  | STRING str -> str
  | INT n -> string_of_int n 
  | BOOL f -> string_of_bool f
  ;;

let rec string_of_expression (expr: expression): string =
  match expr with 
  | Unit -> "()"
  | Variable mn -> mn
  | Literal lit -> string_of_literal lit
  | Access mn_li -> List.fold_left (fun acc a -> acc ^"."^a) "." mn_li   
  | BinOp (str, e2, e3) -> string_of_expression e2 ^ " "^ str ^ " " ^ string_of_expression e3
  | FunctionCall (ex, ex_li) -> string_of_expression ex ^ "(" ^List.fold_left (fun acc a -> acc ^","^string_of_expression a) "." ex_li    ^")"
  | NewExpr ex -> "new " ^ string_of_expression ex
  | Emit (str, ex) -> "emit " ^ str ^ "(" ^ 
    (match ex with 
    | None -> ")"
    | Some ex -> string_of_expression ex ^")"
    )
  | Await ex -> "emit " ^ string_of_expression ex
  | DoEvery (ex1, ex2) -> "do:\n " ^ string_of_expression ex1 ^ "every: " ^ string_of_expression ex2
  | ForkPar (e_li) -> "PAR:\n " ^ List.fold_left (fun acc a -> acc ^"\n||\n"^string_of_expression a) "" e_li
  | Seq (ex1, ex2) -> "Seq:\n " ^ string_of_expression ex1 ^ "; " ^ string_of_expression ex2
  | Abort (ex1, ex2) -> "Seq:\n " ^ string_of_expression ex1 ^ "; " ^ string_of_expression ex2
  | Loop ex -> "loop " ^ string_of_expression ex
  | Yield -> "yield"
  | Halt -> "Halt"
  | Signal str -> "signal "^ str
  | Present (ex1, ex2) -> "Seq:\n " ^ string_of_expression ex1 ^ "; " ^ string_of_expression ex2
  

  ;;
let string_of_statement (state) : string = 
  match state with
  | ImportStatement str -> str 
  | VarDeclear (str, ex) -> "var " ^ str ^" = "^ string_of_expression ex 
  | ConsDeclear (str, ex) -> "const " ^ str ^" = "^ string_of_expression ex 
  | Let (ex1, ex2) ->"exports." ^ string_of_expression ex1 ^ " = " ^ string_of_expression ex2
  | ExportStatement (ex1, ex2) ->"exports." ^ string_of_expression ex1 ^ " = " ^ string_of_expression ex2
  | ModelDeclear (mn, p_li, ex) -> "hiphop module " ^ mn ^"("^ List.fold_left (fun acc a -> acc ^ "," ^ string_of_param a) "" p_li ^") {" ^ string_of_expression ex ^"\n }"
  ;;

let rec string_of_program (states : statement list) : string =
  match states with
    [] -> ""
  | x::xs -> string_of_statement x ^ "\n\n" ^ string_of_program xs 
  ;;



let () =
  let inputfile = (Sys.getcwd () ^ "/" ^ Sys.argv.(1)) in
(*    let outputfile = (Sys.getcwd ()^ "/" ^ Sys.argv.(2)) in
print_string (inputfile ^ "\n" ^ outputfile^"\n");*)
  let ic = open_in inputfile in
  try
      let lines =  (input_lines ic ) in
      let line = List.fold_right (fun x acc -> acc ^ "\n" ^ x) (List.rev lines) "" in
      let progs = Parser.program Lexer.token (Lexing.from_string line) in
      

      print_string (string_of_program progs^"\n");
      
      flush stdout;                (* 现在写入默认设备 *)
      close_in ic                  (* 关闭输入通道 *)

    with e ->                      (* 一些不可预见的异常发生 *)
      close_in_noerr ic;           (* 紧急关闭 *)
      raise e                      (* 以出错的形式退出: 文件已关闭,但通道没有写入东西 *)

   ;;
