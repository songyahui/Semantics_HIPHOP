(*----------------------------------------------------
----------------------PRINTING------------------------
----------------------------------------------------*)

open List
open Printf
open Ast


exception Foo of string


let counter = ref 0;;

let getAnewVar = 
  counter := ! counter + 1; 
  "t" ^ string_of_int !counter;;

let counter_rewriting = ref 0;;



let getAnewVar_rewriting () = 
  counter_rewriting := ! counter_rewriting + 1; 
  let var = "tv" ^ string_of_int !counter_rewriting in 
  (var , Sleek.Atomic(Sleek.Ge, Var var , Const 0)) ;;

(*used to generate the free veriables, for subsititution*)
let freeVar = ["t1"; "t2"; "t3"; "t4";"t5";"t6";"t7";"t8";"t9";"t10"
              ;"t11"; "t12"; "t13"; "t14";"t15";"t16";"t17";"t18";"t19";"t20"
              ;"t21"; "t22"; "t23"; "t24";"t25";"t26";"t27";"t28";"t29";"t30"];;



let getAfreeVar (varList:string list):string  =
  let rec findOne li = 
    match li with 
        [] -> raise ( Foo "freeVar list too small exception!")
      | x :: xs -> if (exists (fun a -> String.compare a x == 0) varList) == true then findOne xs else x
  in
  findOne freeVar
;;




let rec iter f = function
  | [] -> ()
  | [x] ->
      f true x
  | x :: tl ->
      f false x;
      iter f tl

let to_buffer ?(line_prefix = "") ~get_name ~get_children buf x =
  let rec print_root indent x =
    bprintf buf "%s\n" (get_name x);
    let children = get_children x in
    iter (print_child indent) children
  and print_child indent is_last x =
    let line =
      if is_last then
        "└── "
      else
        "├── "
    in
    bprintf buf "%s%s" indent line;
    let extra_indent =
      if is_last then
        "    "
      else
        "│   "
    in
    print_root (indent ^ extra_indent) x
  in
  Buffer.add_string buf line_prefix;
  print_root line_prefix x

let printTree ?line_prefix ~get_name ~get_children x =
  let buf = Buffer.create 1000 in
  to_buffer ?line_prefix ~get_name ~get_children buf x;
  Buffer.contents buf

type binary_tree =
  | Node of string * (binary_tree  list )
  | Leaf

let get_name = function
    | Leaf -> "."
    | Node (name, _) -> name;;

let get_children = function
    | Leaf -> []
    | Node (_, li) -> List.filter ((<>) Leaf) li;;



let rec input_lines file =
  match try [input_line file] with End_of_file -> [] with
   [] -> []
  | [line] -> (String.trim line) :: input_lines file
  | _ -> failwith "Weird input_line return value"
;;






let string_of_param (p : param) : string =
  match p with 
  | IN str -> "in " ^ str 
  | OUT str -> "out " ^ str
  | Data str -> str
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
  | Await ex -> "await " ^ string_of_expression ex
  | DoEvery (ex1, ex2) -> "do:\n " ^ string_of_expression ex1 ^ "every: " ^ string_of_expression ex2
  | ForkPar (e_li) -> "PAR:\n " ^ List.fold_left (fun acc a -> acc ^"\n||\n"^string_of_expression a) "" e_li
  | Seq (ex1, ex2) -> "Seq:\n " ^ string_of_expression ex1 ^ "; " ^ string_of_expression ex2
  | Abort (ex1, ex2) -> "Seq:\n " ^ string_of_expression ex1 ^ "; " ^ string_of_expression ex2
  | Loop ex -> "loop " ^ string_of_expression ex
  | Hop ex -> "Hop " ^ string_of_expression ex
  | Async (str, ex1, es2) -> "async " ^ str ^"{ "^ string_of_expression ex1  ^"}\n" ^ string_of_expression es2 
  | Lambda (ex1, ex) -> "lamdba " ^ string_of_expression ex1 ^" => "^ string_of_expression ex 
  | Continue (ex1, con) -> "continue " ^ string_of_expression ex1 ^" => "^ string_of_expression con
  | Return ex -> "return " ^ string_of_expression ex
  | Break ex -> "Break " ^ string_of_expression ex
  | Trap (ex1, ex) -> "trap " ^ string_of_expression ex1 ^" : "^ string_of_expression ex 
  | Yield -> "yield"
  | Halt -> "Halt"
  | Run ex -> " run " ^ string_of_expression ex
  | Signal (str, p) -> "signal: "^ str ^ string_of_expression p
  | Present (ex1, ex2, ex3) -> "Seq:\n " ^ string_of_expression ex1 ^ "; " ^ string_of_expression ex2 ^ (
    match ex3 with 
    | None -> ""
    | Some ex -> "else " ^ string_of_expression ex
  )
  | FunctionExpr (p_li, ex) -> "function " ^ "("^ List.fold_left (fun acc a -> acc ^ "," ^ string_of_param a) "" p_li ^") {" ^ string_of_expression ex ^"\n }"

  

  ;;

let rec show_effects_list (eff_li: Sleek.effects) : string =
  match eff_li with 
  | [] -> ""
  | [x] -> Sleek.show_simple_effects x 
  | x :: xs -> Sleek.show_simple_effects x ^ "\\/" ^ show_effects_list xs ;;


let string_of_statement (state) : string = 
  match state with
  | ImportStatement str -> str 
  | VarDeclear (str, ex) -> "var " ^ str ^" = "^ string_of_expression ex 
  | ConsDeclear (str, ex) -> "const " ^ str ^" = "^ string_of_expression ex 
  | Let (ex1, ex2) ->"let " ^ string_of_expression ex1 ^ " = " ^ string_of_expression ex2
  | ModduleDeclear (mn, p_li, ex, pre, post) -> "hiphop module " ^ mn ^"("^ List.fold_left (fun acc a -> acc ^ "," ^ string_of_param a) "" p_li ^")"^ 
  show_effects_list ( pre) ^ "\n" ^ show_effects_list ( post) ^"\n" ^
  "{" ^ string_of_expression ex ^"\n }"
  | FunctionDeclear (mn, p_li, ex) -> "function " ^ mn ^"("^ List.fold_left (fun acc a -> acc ^ "," ^ string_of_param a) "" p_li ^") {" ^ string_of_expression ex ^"\n }"
  | Call (str_li, ex_li) -> List.fold_left (fun acc a -> acc ^"."^a) "." str_li    ^ "(" ^List.fold_left (fun acc a -> acc ^","^string_of_expression a) "." ex_li    ^")"
  | Assign (str_li, ex) -> List.fold_left (fun acc a -> acc ^"."^a) "." str_li   ^ " = " ^ string_of_expression ex
  | TryCatch (ex1, e, ex) -> "try " ^ string_of_expression ex1 ^"\n catch (" ^ string_of_expression e ^ ")" ^ string_of_expression ex 

  ;;

let rec string_of_program (states : statement list) : string =
  match states with
    [] -> ""
  | x::xs -> string_of_statement x ^ "\n\n" ^ string_of_program xs 
  ;;



let string_of_prog_states (ps: prog_states) : string = 
  List.fold_left  (fun acc (his, instance, k) -> 

    acc^  " : " ^  Sleek.show_instants his ^ ", "^
    
    (match instance with 
    | None -> "none instance"
    | Some (t) -> Sleek.show_instants (Instant t)
    ) ^ ", " ^ string_of_int k 

  ) " "ps
  ;;

let rec zip (ls:'a list * 'b list) : ('a * 'b) list =
  let (xs,ys) = ls in
  match (xs,ys) with
      ([],_) -> []
    | (_,[]) -> []
    | ([x],y::yrest) -> (x,y)::zip ([x],yrest)
    | (x::xrest,[y]) -> (x,y)::zip (xrest,[y])
    | (x::xrest, _) -> List.append (zip ([x], ys)) (zip (xrest, ys))
;;



