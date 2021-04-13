
open Pretty
open Ast
open List

exception Foo of string

(*
prog_states = 
(Sleek.pi * Sleek.instants * instance option * string option) list 


*)

let rec lengthOfEs (es:Sleek.instants) : int =
  match es with 
    Bottom  -> raise (Foo "Bottom does not have length")
  | Empty -> 0
  | Await _ -> 1
  | Instant _ -> 1
  | Sequence (es1, es2) -> lengthOfEs es1 + lengthOfEs es2
  | Union (es1, es2) -> if lengthOfEs es1 > lengthOfEs es2 then lengthOfEs es1 else lengthOfEs es2
  | Parallel (es1, es2) -> if lengthOfEs es1 > lengthOfEs es2 then lengthOfEs es1 else lengthOfEs es2
  | Timed (es1, _) -> lengthOfEs es1 
  | Kleene es1 -> lengthOfEs es1 
  ;;

let rec splitEffects (es:Sleek.instants) (pi:Sleek.pi) :prog_states= 
  match es with 
  | Bottom -> []
  | Empty -> [(pi, Empty, Some (None, Sleek__Signals.empty))]
  | Await s -> [(pi, Await s, Some (None, Sleek__Signals.empty))]

  | Instant ins -> [(pi, Empty, Some (None, ins))]
  | Sequence (es1, es2) -> 
    let temp = splitEffects es2 pi in 
    List.map (fun state ->
      match state with 
      | (pi2, es2', ins2) -> (pi2, Sleek.Sequence (es1, es2'), ins2)
    ) temp
  | Union (es1, es2) -> 
    List.append (splitEffects es1 pi ) (splitEffects es2 pi)
  
  | Kleene es1 -> 
    let temp = splitEffects es1 pi in 
    List.map (fun state ->
      match state with 
      | (pi2, es2', ins2) -> (pi2, Sleek.Sequence (es, es2'), ins2)
    ) temp

  | Timed (es1, t) -> 
    let temp = splitEffects es1 pi in 
    List.map (fun state ->
      let newTV1 = getAnewVar_rewriting () in
      let newTV2 = getAnewVar_rewriting () in
      match state with 
      | (p, e, Some (None, i)) -> 
        let newPi = Sleek.And(p, Sleek.Atomic(Sleek.Eq, Sleek.Plus(Var newTV1, Var newTV2) , t)) in 
        (newPi, Sleek.Timed (e, Sleek.Var newTV1), Some (Some (Sleek.Var newTV2), i))
      | (p, e, Some (Some t', i)) -> 
        let newPi = Sleek.And(p, Sleek.Atomic(Sleek.Eq, Sleek.Plus(Var newTV1, Var newTV2) , t)) in 
        (Sleek.And(newPi, Sleek.Atomic(Sleek.Eq, t', Var newTV2)), Sleek.Timed (e, Sleek.Var newTV1), Some (Some (Sleek.Var newTV2), i))
      | (p, e, None) ->  (p, e, None)
    ) temp

  | Parallel (es1, es2) -> 
    let len1 = lengthOfEs es1 in 
    let len2 = lengthOfEs es2 in 
    if len1 > len2 then 
      let temp = splitEffects es1 pi in 
      List.map (fun (p, e, i) -> (p, Sleek.Parallel (e, es2), i)) temp
    else if len1 < len2 then 
      let temp = splitEffects es2 pi in 
      List.map (fun (p, e, i) -> (p, Sleek.Parallel (e, es1), i)) temp
    else 
      let temp1 = splitEffects es1 pi in 
      let temp2 = splitEffects es2 pi in 
      let combine = zip (temp1, temp2) in 
      List.map (fun ((p1, e1, i1), (p2, e2, i2)) -> (Sleek.And(p1, p2), Sleek.Parallel(e1, e2), 
      (
        match (i1, i2) with 
        | (Some(None,cur1 ), Some(None,cur2 )) -> Some (None, Sleek__Signals.merge cur1 cur2)
        | _ -> None 
      )
      
      )) combine

    

  ;;




let rec fstPar (es:Sleek.instants) :parfst list = 
  match es with 
    Bottom -> []
  | Empty -> []
  | Await s -> [(W s)] 
  | Instant ins ->  [(SL ins)]
  | Sequence (es1 , es2) ->  if Sleek__Inference.nullable es1 then append (fstPar  es1) (fstPar  es2) else fstPar  es1
  | Union (es1, es2) -> append (fstPar  es1) (fstPar  es2)
  | Timed (es1, _) -> fstPar es1
  | Kleene es1 -> fstPar  es1
  | Parallel (_ , _) -> 
    (raise (Foo "should not be here fstPar"))
    (*let fst1 = fstPar es1 in
    let fst2 = fstPar es2 in
    let combine = zip (fst1,  fst2) in 
    List.map (fun (a, b) -> 
    
    List.append a b) combine
    *)
  

    ;;




let rec derivativePar (fst: parfst) (es:Sleek.instants) : Sleek.instants =
  match es with 
  | Bottom ->  Bottom
  | Empty ->  Bottom
  | Await s -> 
    (
      match fst with 
        W (f) ->  if Sleek__Signals.compare_event f s  then Empty else Bottom
      | SL ins -> if Sleek__Signals.isSigOne s ins then Empty else Bottom
    )
  | Instant ins ->  
    (
      match fst with 
        W f ->  if Sleek__Signals.isSigOne f ins then Empty else Bottom
      | SL f -> if Sleek__Signals.(|-)  f ins then Empty else Bottom
    )
    
  | Sequence (es1 , es2) -> 
      let esF = derivativePar fst es1  in 
      let esL = Sleek.Sequence(esF,  es2) in  
      if Sleek__Inference.nullable es1 
      then 
          let esR =  derivativePar fst es2 in 
          Union (esL, esR)
      else esL

  | Union (es1, es2) -> 
      let temp1 =  derivativePar fst es1  in
      let temp2 =  derivativePar fst es2  in 
      Union (temp1,temp2)

  | _ -> raise (Foo "derivativePar error")

  

  ;;


let rec parallelES (pi1:Sleek.pi) (pi2:Sleek.pi) (es1:Sleek.instants) (es2:Sleek.instants) : (Sleek.pi * Sleek.instants) =
  let norES1 = Sleek.normalize_es es1 in 
  let norES2 = Sleek.normalize_es es2 in 

  print_string (Sleek.show_instants (norES1)^"\n");
  print_string (Sleek.show_instants (norES2)^"\n\n");



  let fst1 = fstPar norES1 in
  let fst2 = fstPar norES2 in 

  let headcom = zip (fst1, fst2) in 
  let esLIST = List.map (
  fun (f1, f2) -> 

    let der1 = Sleek.normalize_es  (derivativePar f1 norES1) in 
    let der2 = Sleek.normalize_es  (derivativePar f2 norES2) in 

  

    match (f1, f2) with  
      (W _, W _ ) -> raise (Foo "there is a deadlock")
    | (W s, SL ins) -> 
      if Sleek__Signals.isSigOne s ins then 
        parallelES pi1 pi2 der1 der2
      else 
        let (p, es) = parallelES pi1 pi2 es1 der2  in 
        (p, Sequence (Instant ins, es))
    | (SL ins, W s) -> 
      if Sleek__Signals.isSigOne s ins then 
        parallelES pi1 pi2 der1 der2
      else 
        let (p, es) = parallelES pi1 pi2 der1 es2  in 
        (p, Sequence (Instant ins, es))
    | (SL ins1, SL ins2) -> 
      (match (der1, der2) with 
      | (Empty, _) -> (True, Sequence (Instant (Sleek__Signals.merge ins1 ins2), der2))
      | (_, Empty) -> (True, Sequence (Instant (Sleek__Signals.merge ins1 ins2), der1))
      | (der1, der2) -> 
        let (pi, es) = (parallelES pi1 pi2 der1 der2) in 
        (pi, Sequence (Instant (Sleek__Signals.merge ins1 ins2), es))
      
    ) 




    
  ) headcom
  in 
  print_string ((List.fold_left (fun acc a -> acc ^ Sleek.show_effects a ) "" esLIST) ^"\n"); 

  List.fold_left (fun (pacc, esacc) (p, e) -> (Sleek.And(pacc, p), Sleek.Union(esacc, e)))  (Sleek.And(pi1, pi2), Bottom) esLIST


  
 ;;

let tAdd_None (t:Sleek__Signals.t option  ): (Sleek.term option * Sleek__Signals.t) option=
  match t with
  | None -> None
  | Some ins -> Some (None, ins)
  ;;


let rec forward (current:prog_states) (prog:expression) (full: statement list): prog_states =

  match prog with 
  | Unit -> current
  | Halt -> 
      List.map (fun state ->
        match state with 
        | (pi, his, Some (_, cur)) -> (pi, Sleek.Sequence (his, Sleek.Instant cur), None)
        | (_, _, None) -> state
      )  current
  
  | Emit (s, _ ) -> 
      List.map (fun state ->
        match state with 
        | (pi, his, Some (t, cur)) -> (pi, his , Some (t, Sleek__Signals.merge cur (Sleek__Signals.from s)))
        | (_, _, None) -> state
      )  current

  | Signal (_, p) -> forward current p full 

  | Seq (p1, p2) -> 
    forward (forward current p1 full) p2 full

  | Async (s, p) -> 
    List.map (fun (pi1, his, cur1) ->
      match cur1 with 
      | None -> (pi1, his, cur1)
      | Some (None, cur) -> (pi1, Sleek.Sequence (his, Sleek.Instant cur), Some (None, Sleek__Signals.make [(Sleek__Signals.present s)]))
      | Some (Some t, cur) -> (pi1, Sleek.Sequence (his, Sleek.Timed (Sleek.Instant cur, t)), Some (None, Sleek__Signals.make [(Sleek__Signals.present s)]))
      ) (forward current p full)

  
  

    | Await (Variable s) -> 
      List.map (fun (pi1, his, cur1) -> 
        match cur1 with 
        | None -> (pi1, his, cur1)
        | Some (None, cur) -> (pi1, Sleek.Sequence (his, Sleek.Sequence(Sleek.Instant cur, Await (Sleek__Signals.present s))), Some (None, Sleek__Signals.empty))
        | Some (Some t, cur) -> (pi1, Sleek.Sequence (his, Sleek.Sequence(Sleek.Timed (Sleek.Instant cur, t), Await (Sleek__Signals.present s))), Some (None, Sleek__Signals.empty))
      

    )  current 



  | ForkPar (p1::p2::_) -> 
    List.flatten (
    List.fold_left (fun acc (pi, his, cur) ->
  
    List.append acc (  
  
    let temp1 = forward [(pi, Empty, cur)] p1 full in 
    let temp2 = forward [(pi, Empty, cur)] p2 full in 
    let combine = zip (temp1, temp2) in 

  
    List.map (fun (  (pi1, his1, cur1),(pi2, his2, cur2)) ->
  
   
    match (cur1, cur2) with
        
    | (Some (None, cur1), Some (None, cur2)) -> 
      
      let (pi_new, es_new) = parallelES pi1 pi2 (Sequence (his1, Instant cur1)) (Sequence (his2, Instant cur2)) in 
      List.map (fun (a, b, c) -> (a, Sleek.Sequence(his,b), c)) (splitEffects (Sleek.normalize_es es_new) pi_new )  
    
    | (Some (Some t, cur1), Some (None, cur2))-> 
      let (pi_new, es_new) = parallelES pi1 pi2 (Sequence (his1, Timed (Instant cur1, t))) (Sequence (his2, Instant cur2)) in 
      List.map (fun (a, b, c) -> (a, Sleek.Sequence(his,b), c)) (splitEffects (Sleek.normalize_es es_new) pi_new )  
    
    | (Some (None, cur1), Some (Some t, cur2))-> 
      let (pi_new, es_new) = parallelES pi1 pi2 (Sequence (his1, Instant cur1)) (Sequence (his2, Timed (Instant cur2, t))) in 
      List.map (fun (a, b, c) -> (a, Sleek.Sequence(his,b), c)) (splitEffects (Sleek.normalize_es es_new) pi_new )  
    
    | (Some (Some t1, cur1), Some (Some t2, cur2))-> 
      let (pi_new, es_new) = parallelES pi1 pi2 (Sequence (his1, Timed (Instant cur1, t1))) (Sequence (his2, Timed (Instant cur2, t2))) in 
      List.map (fun (a, b, c) -> (a, Sleek.Sequence(his,b), c)) (splitEffects (Sleek.normalize_es es_new) pi_new )  

    | _ -> 
      let (pi_new, es_new) = parallelES pi1 pi2 (Sequence(his,his1)) (his2) 
      in [(pi_new, es_new, None)] 

    ) combine
    )) [] current
    )

   

  
  | _ -> print_string( string_of_program full ) ;current
 
  ;;
(*


  | Emit (s, _ ) -> 
    List.map (fun (pi, his, cur, k) ->(pi, his , ((One s)::cur )(*setState cur s 1*), k))  current (* flag 0 - Zero, 1- One, 2-Await *)
  | Await (s) -> 
    List.map (fun (pi, his, cur, k) ->(pi, Sequence (his, Sequence(Await s , Instant cur)) , [] (*setState cur s 2*), k))  current (* flag 0 - Zero, 1- One, 2-Await *)

  | Present (s, p1, p2) ->
    List.fold_left (fun acc (pi, his, cur, k) -> 
      List.append acc (
          if isPresent s cur then forward env current p1 full 
          else forward env current p2 full) 
    ) [] current

  

  | Assert eff -> 

      let (_, re, _, _) = check_containment (List.map (fun (pi, his, cur, k) -> (pi, Sequence(his, Instant cur))) current) eff in 
      if re then current 
      else raise (Foo "assertion failed")
   
  

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
    (PureAnd (pi1, Lt (term, Number delay)), Timed (Sequence (his1, Instant cur1),  term) , [] (*make_nothing env*), k1)
    )
    (forward env current p full)

  | Run (mn, _) ->
  List.fold_left (fun acc (pi, his, cur, k) ->

    List.append acc (  
      let (fun_name, inp, outp, precon, postcon, _) = findProg mn full in 
      let (_, re, _, _) = check_containment [(pi, Sequence (his, Instant cur))] precon in 
      
      
      List.map (fun (pi1, es1) -> 
      if re then (PureAnd (pi, pi1), Sequence (Sequence (his, Instant cur), es1), make_nothing env, k)
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
      Some trap -> [(PureAnd (pi, pi1), Sequence (Sequence (his, Instant cur), his1), cur1, k1)]
    | None -> 
      List.map ( fun ins ->

      match (ins, cur1) with 
      | ([], _) -> (pi1, Sequence (Sequence (his, Instant cur), Kleene (Sequence (derivativePar (SL ins) his1, Instant cur1))), make_nothing env, k1)
      | (_, []) -> (pi1, Sequence (Sequence (his, Instant (List.append cur ins)), Kleene (Sequence (derivativePar (SL ins) his1, Instant ins))), make_nothing env, k1)
      | _ -> (pi1, Sequence (Sequence (his, Instant (List.append cur ins)), Kleene (Sequence (derivativePar (SL ins) his1, Instant (List.append cur1 ins)))), make_nothing env, k1)
      ) (fst_simple his1)
    
    )
    ) (forward env [(pi, Empty, [], k)] p full)

  )
  
  
  ) [] current )

  | Fork (p1, p2) -> 
 
      
  | (Some trap, None) -> let (pi_new, es_new) = parallelES pi1 pi2 (Sequence (his1, Instant cur1)) (Sequence (his2, Instant cur2)) in
                    
      List.map (
        fun (pi_new_, his_new, cur_new) -> 
          (pi_new, Sequence(his, his_new), cur_new, k1) )
      (splitEffects  (normalES es_new pi_new) pi_new)        

  
  | (None, Some trap) -> let (pi_new, es_new) = parallelES pi1 pi2 (Sequence (his1, Instant cur1)) (Sequence (his2, Instant cur2)) in
      List.map (
        fun (pi_new_, his_new, cur_new) -> 
        (pi_new, Sequence(his, his_new), cur_new, k2) )
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
    let init = (List.fold_left (fun acc (pre_pi, pre_es) ->
        List.append acc (splitEffects pre_es  pre_pi)
        ) [] pre
      ) in 
    let raw_final = (*effects_inference*) forward init ex whole in 
    let final = List.map (fun state ->
        match state with 
        | (pi, his, Some (None, cur)) -> Sleek.normalize (pi, Sleek.Sequence (his, Sleek.Instant cur))
        | (pi, his, Some (Some t, cur)) ->Sleek.normalize (pi, Sleek.Sequence (his, Sleek.Timed (Sleek.Instant cur, t)))

        | (pi, his, None) -> (pi, his)
      ) raw_final in 

    let (verbose, history) = Sleek.verify_entailment (Sleek.Entail { lhs = List.hd final; rhs = List.hd (post) })  in 
    "\n========== Module: "^ mn ^" ==========\n" ^
    "[Pre  Condition] " ^ show_effects_list pre ^"\n"^
    "[Post Condition] " ^ show_effects_list post ^"\n"^
    "[Final  Effects] " ^ show_effects_list (List.map (fun a -> Sleek.normalize a) final) ^"\n\n"^
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
