open Z3

let rec term_to_expr ctx : Ast.term -> Expr.expr = function
  | Const n        -> Arithmetic.Real.mk_numeral_i ctx n
  | Var v          -> Arithmetic.Real.mk_const_s ctx v
  | Gen i          -> Arithmetic.Real.mk_const_s ctx ("t" ^ string_of_int i ^ "'")
  | Plus (t1, t2)  -> Arithmetic.mk_add ctx [ term_to_expr ctx t1; term_to_expr ctx t2 ]
  | Minus (t1, t2) -> Arithmetic.mk_sub ctx [ term_to_expr ctx t1; term_to_expr ctx t2 ]


let rec pi_to_expr ctx : Ast.pi -> Expr.expr = function
  | True                -> Boolean.mk_true ctx
  | False               -> Boolean.mk_false ctx
  | Atomic (op, t1, t2) -> (
      let t1 = term_to_expr ctx t1 in
      let t2 = term_to_expr ctx t2 in
      match op with
      | Eq -> Boolean.mk_eq ctx t1 t2
      | Lt -> Arithmetic.mk_lt ctx t1 t2
      | Le -> Arithmetic.mk_le ctx t1 t2
      | Gt -> Arithmetic.mk_gt ctx t1 t2
      | Ge -> Arithmetic.mk_ge ctx t1 t2)
  | And (pi1, pi2)      -> Boolean.mk_and ctx [ pi_to_expr ctx pi1; pi_to_expr ctx pi2 ]
  | Or (pi1, pi2)       -> Boolean.mk_or ctx [ pi_to_expr ctx pi1; pi_to_expr ctx pi2 ]
  | Imply (pi1, pi2)    -> Boolean.mk_implies ctx (pi_to_expr ctx pi1) (pi_to_expr ctx pi2)
  | Not pi              -> Boolean.mk_not ctx (pi_to_expr ctx pi)


let check pi =
  let cfg = [ ("model", "false"); ("proof", "false") ] in
  let ctx = mk_context cfg in
  let expr = pi_to_expr ctx pi in
  (* print_endline (Expr.to_string expr); *)
  let goal = Goal.mk_goal ctx true true false in
  (* print_endline (Goal.to_string goal); *)
  Goal.add goal [ expr ];
  let solver = Solver.mk_simple_solver ctx in
  List.iter (fun a -> Solver.add solver [ a ]) (Goal.get_formulas goal);
  let sat = Solver.check solver [] == Solver.SATISFIABLE in
  (* print_endline (Solver.to_string solver); *)
  sat
