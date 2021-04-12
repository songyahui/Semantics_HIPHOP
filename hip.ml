
open Pretty
open Ast

exception Foo of string

(*
prog_states = 
(Sleek.pi * Sleek.instants * instance option * string option) list 


*)

let forward (current:prog_states) (prog:expression) (full: statement list): prog_states =

  match prog with 
  | Unit -> current
  | Halt -> 
      List.map (fun state ->
        match state with 
        | (pi, his, Some cur, k) -> (pi, Sleek.Sequence (his, Sleek.Instant cur), None,  k)
        | (_, _, None, _) -> state
      )  current
  
  | _ -> print_string( string_of_program full ) ;current
 
  ;;
(*

| Yield -> 
    List.map (fun (pi, his, cur, k) -> (pi, Cons (his,Instance cur) , [](*make_nothing env *), k))  current
  
  | Emit (s, _ ) -> 
    List.map (fun (pi, his, cur, k) ->(pi, his , ((One s)::cur )(*setState cur s 1*), k))  current (* flag 0 - Zero, 1- One, 2-Wait *)
  | Await (s) -> 
    List.map (fun (pi, his, cur, k) ->(pi, Cons (his, Cons(Wait s , Instance cur)) , [] (*setState cur s 2*), k))  current (* flag 0 - Zero, 1- One, 2-Wait *)

  | Present (s, p1, p2) ->
    List.fold_left (fun acc (pi, his, cur, k) -> 
      List.append acc (
          if isPresent s cur then forward env current p1 full 
          else forward env current p2 full) 
    ) [] current

  | Signal (s, p) -> 
    forward (List.append env [s]) current p full 

  | Async (s, p) -> 
    List.map (fun (pi1, his1, cur1, k1) ->
      let term = Var getAnewVar in 
      (PureAnd (pi1, GtEq (term, Number delay)), RealTime (Cons (his1, Instance cur1), term), [(One s)](*setState (make_nothing env) s 1*), k1)
        ) (forward env current p full)

  | Assert eff -> 

      let (_, re, _, _) = check_containment (List.map (fun (pi, his, cur, k) -> (pi, Cons(his, Instance cur))) current) eff in 
      if re then current 
      else raise (Foo "assertion failed")
   
  | Seq (p1, p2) -> 
    
    List.fold_left (fun acc (pi1, his1, cur1, k1) ->  
    List.append acc (  
    (match k1 with 
      Some str -> [(pi1, his1, cur1, k1)] 
    | None -> forward env [(pi1, his1, cur1, k1)] p2 full
    )
    )
    ) [] ( forward env current p1 full)
    

  | Trap (mn, p1) -> 
    List.fold_left (fun acc (pi1, his1, cur1, k1) ->  
      List.append acc (  
    
    [(match k1 with 
      Some str -> if String.compare str mn == 0 then (pi1, his1, cur1, None) else (pi1, his1, cur1, k1)
    | None -> (pi1, his1, cur1, k1)
    )]
      )
    ) [] ( forward env current p1 full)

  | Break name -> 
    List.map (fun (pi, his, cur, k) ->
      (match k with 
        Some str -> (pi, his, cur, k)
      | None -> (pi, his, cur, Some name)
      )
    ) current

  | Abort (delay, p) ->
    List.map (fun (pi1, his1, cur1, k1) ->
    let term = Var getAnewVar in 
    (PureAnd (pi1, Lt (term, Number delay)), RealTime (Cons (his1, Instance cur1),  term) , [] (*make_nothing env*), k1)
    )
    (forward env current p full)

  | Run (mn, _) ->
  List.fold_left (fun acc (pi, his, cur, k) ->

    List.append acc (  
      let (fun_name, inp, outp, precon, postcon, _) = findProg mn full in 
      let (_, re, _, _) = check_containment [(pi, Cons (his, Instance cur))] precon in 
      
      
      List.map (fun (pi1, es1) -> 
      if re then (PureAnd (pi, pi1), Cons (Cons (his, Instance cur), es1), make_nothing env, k)
      else raise (Foo "precondiction check failed")
      ) precon
    )
   ) [] current 

  | Loop p ->
List.flatten(
  List.fold_left (fun acc (pi, his, cur, k) ->


  List.append acc (  
   
    List.map (fun (pi1, his1, cur1, k1) -> 
    (match k1 with 
      Some trap -> [(PureAnd (pi, pi1), Cons (Cons (his, Instance cur), his1), cur1, k1)]
    | None -> 
      List.map ( fun ins ->

      match (ins, cur1) with 
      | ([], _) -> (pi1, Cons (Cons (his, Instance cur), Kleene (Cons (derivativePar (SL ins) his1, Instance cur1))), make_nothing env, k1)
      | (_, []) -> (pi1, Cons (Cons (his, Instance (List.append cur ins)), Kleene (Cons (derivativePar (SL ins) his1, Instance ins))), make_nothing env, k1)
      | _ -> (pi1, Cons (Cons (his, Instance (List.append cur ins)), Kleene (Cons (derivativePar (SL ins) his1, Instance (List.append cur1 ins)))), make_nothing env, k1)
      ) (fst_simple his1)
    
    )
    ) (forward env [(pi, Emp, [], k)] p full)

  )
  
  
  ) [] current )

  | Fork (p1, p2) -> 
  List.flatten (
  List.fold_left (fun acc (pi, his, cur, k) ->

  List.append acc (  

  let temp1 = forward env [(pi, Emp, cur, k)] p1 full in 
  let temp2 = forward env [(pi, Emp, cur, k)] p2 full in 
  let combine = zip (temp1, temp2) in 



  List.map (fun (  (pi1, his1, cur1, k1),(pi2, his2, cur2, k2)) ->

 
  match (k1, k2) with
    (None, None) -> let (pi_new, es_new) = parallelES pi1 pi2 (Cons (his1, Instance cur1)) (Cons (his2, Instance cur2)) in
      
    List.map 
      (fun (pi_new_, his_new, cur_new) -> 
        (pi_new_, Cons(his, his_new), cur_new, None) )
      (splitEffects  (normalES es_new pi_new) pi_new)      
      
      
  | (Some trap, None) -> let (pi_new, es_new) = parallelES pi1 pi2 (Cons (his1, Instance cur1)) (Cons (his2, Instance cur2)) in
                    
      List.map (
        fun (pi_new_, his_new, cur_new) -> 
          (pi_new, Cons(his, his_new), cur_new, k1) )
      (splitEffects  (normalES es_new pi_new) pi_new)        

  
  | (None, Some trap) -> let (pi_new, es_new) = parallelES pi1 pi2 (Cons (his1, Instance cur1)) (Cons (his2, Instance cur2)) in
      List.map (
        fun (pi_new_, his_new, cur_new) -> 
        (pi_new, Cons(his, his_new), cur_new, k2) )
      (splitEffects  (normalES es_new pi_new) pi_new)                    

  | (Some t1, Some t2) -> raise (Foo ("not defined curretly"))

  ) combine
  )) [] current
  )
  *)





let forward_verification (prog : statement) (whole: statement list): string = 
  match prog with 
  | ModduleDeclear (mn, (*p_li*)_ , ex, pre, post) -> 
    print_string (string_of_program [prog]^"\n");
    let pre = Sleek.parse_effects pre in 
    let post = Sleek.parse_effects post in 
    (*let inp_sig = List.fold_left (fun acc a ->  List.append acc 
      (match a with 
      | OUT str -> [str]
      | _ -> []) 
      ) [] p_li in 
      *)
    let raw_final = (*effects_inference*) forward (*pre*) [] ex whole in 
    print_string (string_of_prog_states raw_final);
    let final = (Sleek.True, Sleek.Bottom) in 
    
    let (verbose, history) = Sleek.verify_entailment (Sleek.Entail { lhs = final; rhs = List.hd (post) })  in 
    "\n========== Module: "^ mn ^" ==========\n" ^
    "[Pre  Condition] " ^ show_effects_list pre ^"\n"^
    "[Post Condition] " ^ show_effects_list post ^"\n"^
    "[Final  Effects] " ^ show_effects_list [final] ^"\n\n"^
    (*(string_of_inclusion final_effects post) ^ "\n" ^*)
    "[TRS: Verification for Post Condition]\n" ^ 
    Sleek.show_history  history    ~verbose ^ "\n\n"
    
  | _ -> ""
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
      
      print_string (List.fold_left (fun acc a -> acc ^ forward_verification a progs) "" progs ) ; 
      flush stdout;                (* 现在写入默认设备 *)
      close_in ic                  (* 关闭输入通道 *)

    with e ->                      (* 一些不可预见的异常发生 *)
      close_in_noerr ic;           (* 紧急关闭 *)
      raise e                      (* 以出错的形式退出: 文件已关闭,但通道没有写入东西 *)

   ;;
