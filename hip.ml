
open Pretty
open Ast
open List

exception Foo of string


let rec fstPar (es:Sleek.instants) :(Sleek.Signals.t) list = 
  match es with 
  | Bottom -> []
  | Empty -> []
  | Await _ -> [[]] (*[Sleek.Signals.fstHelper ev ]*)
  | Instant ins -> [ins]
  | Sequence (es1 , es2) -> if Sleek.Inference.nullable es1 then append (fstPar  es1) (fstPar  es2) else fstPar  es1
  | Union (es1, es2) -> append (fstPar  es1) (fstPar  es2)
  | Kleene es1 -> fstPar  es1
  | Parallel (es1 , _) -> fstPar  es1
  | _ -> raise (Foo "fstPar later")
    

  
(*
  [(True, SL ins, None)]
   ->  
*)
    ;;


let rec derivativePar (fst:Sleek.Signals.t) (es:Sleek.instants) : Sleek.instants =

  match es with 
  | Bottom ->  Bottom
  | Empty ->  Bottom
  | Await s -> if Sleek.Signals.isEventExist s fst then Empty else Await s
  | Instant ins -> if Sleek.Signals.(|-) fst ins then Empty else Bottom
    
  | Sequence (es1 , es2) -> 
      let esF = derivativePar fst es1 in 
      let esL = Sleek.Sequence(esF,  es2) in  
      if Sleek.Inference.nullable es1 
      then 
          let esR =  derivativePar fst es2 in 
          Union (esL, esR)
      else (esL)

  | Union (es1, es2) -> 
      let (temp1) =  derivativePar fst es1  in
      let (temp2) =  derivativePar fst es2  in 
      (Union (temp1,temp2))


  | Kleene (es1) -> 
    let (temp1) =  derivativePar fst es1  in  
    (Sleek.Sequence (temp1, es))

  | Parallel (es1, es2) -> 
      let (temp1) =  derivativePar fst es1 in
      let (temp2) =  derivativePar fst es2 in 

      ( Parallel (temp1,temp2))


  | _ -> raise (Foo "derivativePar later")
  ;;

  
let rec normalizeES_final (trace:Sleek.instants):Sleek.instants =
  match trace with 
  (* reduction *)
  | Bottom -> Bottom
  | Empty -> Empty
  | Instant ins -> if Sleek.Signals.controdicts_final ins then Bottom else Instant ins 
  | Union(es1, es2) -> 
    (match (es1, es2) with 
    | (Bottom, es) -> normalizeES_final es 
    | (es, Bottom) -> normalizeES_final es 
    | (Union (es11, es12), es3) -> Union (es11, Union (es12, es3))
    | _ -> normalizeES_final (Union (normalizeES_final es1, normalizeES_final es2))
    )
  | Sequence (es1, es2) -> 
    let es1 = normalizeES_final es1 in 
    let es2 = normalizeES_final es2 in 
    (match (es1, es2) with 
    | (Empty, _) -> normalizeES_final es2
    | (_, Empty) -> normalizeES_final es1
    | (Bottom, _) -> Bottom
    | (_, Bottom) -> Bottom
    (*| (Sequence (es11, es12), es3) -> (Sequence (es11, Sequence (es12, es3)))*)
    | _ -> (Sequence (es1, es2))
    )

  | Parallel (es, Empty) -> es
  | Parallel (Empty, es) -> es
  | Parallel (_, Bottom) -> Bottom
  | Parallel (Bottom, _) -> Bottom
  | Parallel (es, es') when es = es' -> es
  | Kleene (Kleene esin) -> normalizeES_final (Kleene esin)
  | Kleene Bottom -> Empty
  | Kleene Empty -> Empty
  | Kleene (Union (Empty, es)) -> Kleene es

  | Parallel (es1, es2) ->
      let es1' = normalizeES_final es1 in
      if es1' <> es1 then
        Parallel (es1', es2)
      else
        Parallel (es1, normalizeES_final es2)
  | Kleene es -> Kleene (normalizeES_final es)
  | Timed (es, t) -> Timed (normalizeES_final es, t)
  | es -> es


let rec normalizeES (trace:Sleek.instants):Sleek.instants =
  match trace with 
  (* reduction *)
  | Bottom -> Bottom
  | Empty -> Empty
  | Instant ins -> if Sleek.Signals.controdicts ins then Bottom else Instant ins 
  | Union(es1, es2) -> 
    (match (es1, es2) with 
    | (Bottom, es) -> normalizeES es 
    | (es, Bottom) -> normalizeES es 
    | (Union (es11, es12), es3) -> Union (es11, Union (es12, es3))
    | _ -> normalizeES (Union (normalizeES es1, normalizeES es2))
    )
  | Sequence (es1, es2) -> 
    let es1 = normalizeES es1 in 
    let es2 = normalizeES es2 in 
    (match (es1, es2) with 
    | (Empty, _) -> normalizeES es2
    | (_, Empty) -> normalizeES es1
    | (Bottom, _) -> Bottom
    | (_, Bottom) -> Bottom
    (*| (Sequence (es11, es12), es3) -> (Sequence (es11, Sequence (es12, es3)))*)
    | _ -> (Sequence (es1, es2))
    )

  | Parallel (es, Empty) -> es
  | Parallel (Empty, es) -> es
  | Parallel (_, Bottom) -> Bottom
  | Parallel (Bottom, _) -> Bottom
  | Parallel (es, es') when es = es' -> es
  | Kleene (Kleene esin) -> normalizeES (Kleene esin)
  | Kleene Bottom -> Empty
  | Kleene Empty -> Empty
  | Kleene (Union (Empty, es)) -> Kleene es

  | Parallel (es1, es2) ->
      let es1' = normalizeES es1 in
      if es1' <> es1 then
        Parallel (es1', es2)
      else
        Parallel (es1, normalizeES es2)
  | Kleene es -> Kleene (normalizeES es)
  | Timed (es, t) -> Timed (normalizeES es, t)
  | es -> es
(*
prog_states = 
(Sleek.pi * Sleek.instants * instance option * string option) list 

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
*)



let unifyOptionalTerms t1 t2 : (Sleek.term option * Sleek.pi) = 
  match (t1, t2) with 
  | (None, None) -> (None, Sleek.True )
  | (Some t, None) -> (Some t, Sleek.True )
  | (None, Some t) -> (Some t, Sleek.True )
  | (Some tt1, Some tt2) -> (Some tt1, Sleek.Atomic(Sleek.Eq, tt1, tt2) )

  ;;

let addOptionaLTerm ins t = 
  match t with 
  | None -> ins
  | Some t -> Sleek.Timed (ins, t)
  ;;


 





let rec findProg name full:(param list* Sleek.effects * Sleek.effects) = 
  match full with 
  | [] -> raise (Foo ("function " ^ name ^ " is not found!"))
  | x::xs -> 
    match x with 
    | ModduleDeclear (str, p_li, _, pre, post) -> 
      if String.compare str name == 0 then (p_li, pre, post)
      else findProg name xs
    | _ -> findProg name xs
;;

let rec matchParams param_real param_formal : Sleek.pi = 
  match (param_real, param_formal) with 
  | ([], []) -> Sleek.True
  | ((Literal (INT n))::xs, (Data d)::ys) -> Sleek.And (Sleek.Atomic(Sleek.Eq, Const n, Var d) , matchParams xs ys)
  | (_::xs, _::ys) -> matchParams xs ys
  | _ -> raise (Foo "function call with unmatched parameters!")
;;


let tAdd_None (t:(Sleek.Signals.event list) option  ): (Sleek.term option * Sleek.Signals.event list) option=
  match t with
  | None -> None
  | Some ins -> Some (None, ins)
  ;;

let setPresent (s:string) (cur) = (Sleek.Signals.setPresent s cur);; 

let setAbsent (s:string) (cur)  = (Sleek.Signals.setAbsent s cur);;

let max k1 k2 = if k1 >= k2 then k1 else k2 

let unionCur c1 c2 = 
  match (c1, c2) with 
  | (None, None) -> None 
  | (Some cur1, Some cur2) -> Some (Sleek.Signals.merge cur1 cur2)
  | (Some _, None ) -> c1 
  | _ -> c2

let parrallHisAndCur  his cur =
  match cur with 
  | None -> None 
  | Some cur1 -> let fst = fstPar his in 
    Some (Sleek.Signals.merge cur1 (List.hd fst))

let parrallHisAndCurAbsorb  (his:Sleek.instants ) (cur:Sleek.Signals.t option) : Sleek.instants =
  match cur with 
  | None -> his 
  | Some cur1 -> 
    let fst = List.hd (fstPar his) in 
    let head = (Sleek.Signals.merge cur1 fst) in 
    let der = derivativePar head his in
    let list = [(Sleek.Sequence (Sleek.Instant head, der)) ] 
    
    in let rec helper li = 
      match li with 
      | [] -> Sleek.Bottom 
      | x::xs -> Sleek.Union (x,  (helper xs))
    in helper list




let rec paralleMerge (state1:prog_states) (state2:prog_states) :prog_states = 
  let state1 = List.filter (fun (his, _, _) -> match normalizeES his with |Sleek.Bottom -> false | _ -> true )state1 in 
  let state2 = List.filter (fun (his, _, _) -> match normalizeES his with |Sleek.Bottom -> false | _ -> true )state2 in 

  let combine = zip (state1, state2) in 
  List.flatten (List.map (fun ((his1, cur1, k1), (his2, cur2, k2)) ->
    
    (*print_string ("\n==================\n");
    print_string (string_of_prog_states [(normalizeES his1, cur1, k1)] ^"\n");
    print_string (string_of_prog_states [(normalizeES his2, cur2, k2)] ^"\n");
    *)
    let his1 = normalizeES his1 in
    let his2 = normalizeES his2 in 
    match (his1, his2) with 
    | (Sleek.Bottom, _) -> []
    | (_, Sleek.Bottom) -> []
    | (Sleek.Empty, Sleek.Empty) -> [(Sleek.Empty, unionCur cur1 cur2, max k1 k2)]
    | (Sleek.Empty, _ ) -> if k1 > 1 then [(Sleek.Empty, parrallHisAndCur his2 cur1, k1)] 
      else [(parrallHisAndCurAbsorb (his2) cur1, cur2, k2)]
    | (_, Sleek.Empty) -> if k2 > 1 then [(Sleek.Empty, parrallHisAndCur his1 cur2, k2) ]
      else [(parrallHisAndCurAbsorb his1 cur2, cur1, k1)]
    | (_, _) -> 
      let fst1 = fstPar his1 in
      let fst2 = fstPar his2 in 
      let headSet = zip (fst1, fst2) in 
      List.flatten (List.map (fun (f1, f2)->
        let head =  (Sleek.Signals.merge f1 f2) in 
        let der1 = derivativePar head his1 in 
        let der2 = derivativePar head his2 in
        let states =  paralleMerge [(der1, cur1, k1)] [(der2, cur2, k2)] in 
        List.map (fun (a, b, c) -> (Sleek.Sequence (Instant head, a), b, c)) states
        )
      headSet)

  )
  combine)
  

let rec splitEffects (env: string list) (es:Sleek.instants) :(Sleek.instants* (Sleek.Signals.t) option) list= 
  let es = normalizeES es  in 
  match es with 
  | Bottom -> []
  | Empty -> [(Empty, None)]
  | Await s -> [(Await s,None)]
  | Instant ins -> [(Empty, Some (Sleek.Signals.add_UndefSigs env ins))]
  | Sequence (es1, es2) -> 
    let temp = splitEffects env es2 in 
    List.map (fun state ->
      match state with 
      | (es2', ins2) -> (Sleek.Sequence (es1, es2'), ins2)
    ) temp
  | Union (es1, es2) -> 
    List.append (splitEffects env es1) (splitEffects env es2)
  
  | Kleene es1 -> 
    let temp = splitEffects env es1 in 
    List.map (fun state ->
      match state with 
      | (es2', ins2) -> (Sleek.Sequence (es, es2'), ins2)
    ) temp



  | Parallel (es1, es2) -> 
    let s1  = splitEffects env es1 in 
    let s2  = splitEffects env es2 in 
    let lambda li = List.map (fun (a, b) -> (a, b, 0)) li in 
    let states = paralleMerge (lambda s1) (lambda s2) in 
    List.map (fun (a, b, _) -> (a, b) ) states


  | _ -> raise (Foo ("splitEffects later"))
  ;;


let fstToInstance cur = 
  match cur with 
  | None -> Sleek.Empty
  | Some ins ->  Sleek.Instant ins 
;;

let addEventToCur (env:string list) (ev:Sleek.Signals.event) (cur: Sleek.Signals.t option):Sleek.Signals.t option=
  match cur with 
  | None ->  Some (ev :: (Sleek.Signals.initUndef env))
  | Some ins ->  Some (ev :: ins )
;;

let rec forward (env:string list) (current:prog_states) (prog:expression) (full: statement list): prog_states =

  match prog with 
  | Unit -> current
  | Yield -> 
      List.map (fun state -> 
      let (his, cur, _) = state in 
      (Sleek.Sequence (his, fstToInstance cur), Some (Sleek.Signals.initUndef env), 0)) current

  
  | Emit (s, _ ) -> 

      List.map (fun state ->
        match state with 
        | (his, Some (cur), _) -> (his , setPresent s cur, 0)
        | (his, None, _ ) -> (his, setPresent s (Sleek.Signals.initUndef env), 0)
        
      )  current

  | Signal (s, p) -> forward (s::env) (
    List.map (
      fun (his, cur, _) -> 
        match cur with 
        | Some (ins) -> (his, Some(Sleek.Signals.add_UndefSigs (s::env) ins), 0)
        | _ -> (his, cur, 0)
    )
    current) p full 

  | Seq (p1, p2) -> 
    let states1 =  (forward env current p1 full) in 
    List.flatten (
      List.map (fun (his, cur, k) -> 
      if k > 1 then [(his, cur, k)]
      else forward env [(his, cur, k)] p2 full

      ) states1
    )
    
    
  
  | Async (s, p, q) -> 
    let branch1 = Seq (p, Emit(s, None)) in 
    let desugar = ForkPar [branch1; q] in 
    forward env current desugar full

  
  | Await (Access (s::_ )) 
  | Await (Variable s) -> 
      let waitSig = Sleek.Await (Sleek.Signals.present s) in 
      let final = List.map (fun (his, cur1, _) ->  
        match cur1 with 
        | None -> (Sleek.Sequence(his, waitSig), None, 0)
        | Some (_) -> 
          (Sleek.Sequence (his, Sleek.Sequence(fstToInstance cur1,  waitSig)), None, 0 )
      )  current in 
      final 

  | Raise d -> 
    List.map (fun (a, b, _) -> (a, b, d+2) ) current

  | Trap (p, q) -> 
    let state1 = forward env current p full in 
    List.flatten (
      List.map (fun (his, cur, k) ->
        if k =2 then forward env [((his, cur, 0))] q full
        else if k > 2 then [(his, cur, k-1)]
        else [(his, cur, k)]

      ) state1
    )
    

  | ForkPar (p1::p2::[]) -> 
    let temp1 = forward env current p1 full in 
    let temp2 = forward env current p2 full in 
    (*
    print_string (string_of_prog_states temp1 ^"\n");
    print_string (string_of_prog_states temp2 ^"\n");
    *)
    paralleMerge temp1 temp2 


  | ForkPar (p1::p2::rest) -> 

    forward env current (ForkPar ((ForkPar ([p1; p2])) ::rest)) full



  | Loop p ->
    List.fold_left (fun acc (his, cur, k) ->
  
    List.append acc (  

      let first_round = forward env [(Empty, cur, k)] p full in 

      List.flatten (
      List.map (fun (his1, cur1, k1) -> 
        if k1 >1 then [(his1, cur1, k1)]
        else let second_round = forward env [(Empty, cur1, k1)] p full in 

        List.map (fun (his2, cur2, k2)->
          (Sleek.Sequence (his, Sequence(his1, Kleene (his2))), cur2, k2)

        ) second_round
      ) first_round
      )
    ) ) [] current

  | Present (Access(str::_), p1, p2)-> 
    List.flatten (
      List.map (fun (his, cur, k) -> 
        let b1 = forward env [(his, addEventToCur env (Sleek.Signals.present str) cur, k)] p1 full in  
        let b2 = forward env [(his, addEventToCur env (Sleek.Signals.absent str) cur, k)] p2 full in 
        List.append b1 b2  

      ) current
    )


  | _ ->  current
 
    ;;
(*
  | Run (FunctionCall (Variable mn, param_real)) -> 

    let (param_formal, precon, postcon) = findProg mn full in 
    
    List.flatten (

    List.fold_left (fun acc (pi, his, cur) ->

    (match cur with 
    | None -> 
      List.append acc (  
        let (verbose, history) = Sleek.verify_entailment (Sleek.Entail { lhs = [(pi, Sleek.Sequence (his, Empty))]; rhs = (precon) })  in 
        if verbose then 

          List.map (fun (pi1, es1) -> 
            let pi_enforcePre = Sleek.And(pi_pre, pi1) in 
            let final = splitEffects env  (Sleek.fixpoint ~f: normalizeES es1) pi_enforcePre  in
            final

          ) postcon

        else 
        (print_string (Sleek.History.show history    ~verbose ^ "\n\n");
 
        raise (Foo "precondiction check failed"))
      )

    | Some (ins, t) -> 

      List.append acc (  
        let (verbose, history) = Sleek.verify_entailment (Sleek.Entail { lhs = [(pi, Sleek.Sequence (his, addOptionaLTermToFst ins t))]; rhs = (precon) })  in 
        if verbose then 
        List.flatten (
          List.map (fun (pi1, es1) -> 
            let trace = parallelES pi pi1 (addOptionaLTermToFst ins t) es1 in 



            List.map (fun (pi_new, ins_new) -> 
            let pi_enforcePre = Sleek.And(pi_pre, pi_new) in 

            let final = splitEffects env  (Sleek.fixpoint ~f: normalizeES ins_new) pi_enforcePre  in
            final
            
            
            ) [trace]
            
           
          ) postcon
        )

        else 
        (print_string (Sleek.History.show history    ~verbose ^ "\n\n");
        
        
        raise (Foo "precondiction check failed"))
      )
      

    )
   ) [] current 
    )

  


  | Abort (FunctionCall (_, (Variable s)::_), p) ->


  List.flatten (

    List.fold_left (fun acc (pi, his, cur) ->
      let (newTV1, newPi1) = getAnewVar_rewriting () in
      let newPi = Sleek.And (newPi1, Sleek.And(pi, Sleek.Atomic(Sleek.Lt, Var newTV1, Var s))) in 

    
      List.append acc (
        List.map (fun (pi1, his1, cur1) ->
        match cur1 with 
        | None -> [(pi1, Sleek.Sequence(his, Timed(his1, Var newTV1)), cur1)]
        | Some (cur, t) -> splitEffects env (Sleek.Sequence(his, Timed (Sleek.Sequence (his1, addOptionaLTermToFst cur t), Var newTV1))) newPi
      
        ) (forward env [(newPi, Empty, cur)] p full)

      )) [] current

  )


  | Abort (Access (s::_ ), p) ->
  
  List.flatten (
    List.fold_left (fun acc (pi, his, cur) ->

      List.append acc (


        List.map (fun (pi1, his1, cur1) ->
        match cur1 with 
        | None -> 
          [(pi1, Sleek.Sequence(his, enforceAbortTrace s his1 ), None)]
        | Some (cur, t) -> 

          match enforceAbortCur s cur t with 
          | None -> [(pi1, Sleek.Sequence(his, enforceAbortTrace s his1 ), None)]        
          | Some (cur', t') ->
          splitEffects env  (Sleek.Sequence(his, enforceAbortTrace s (Sleek.Sequence(his1, addOptionaLTermToFst cur' t'))))  pi1

        ) (forward env [(pi, Empty, cur)] p full)

      )) [] current
  )
    



  | DoEvery (p, Access (str::_ ))->

  (*
  print_string (string_of_states current ^ "\n");
*)


    List.fold_left (fun acc (pi, his, cur) ->
  
      List.append acc (  
  
        let temp = forward env [(pi, Empty, cur)] p full in 

        List.map (fun  (pi1, his1, cur1)->
          match cur with 
          | None -> 
            (match cur1 with
            | None -> 
              (pi1, Sleek.Sequence(his, Sleek.Sequence (Await (Sleek.Signals.present str), his1)), cur1)
          
            | Some (ins1, t1) -> 
              let repeat  = Sleek.Sequence (Await (Sleek.Signals.present str), Sleek.Sequence(his1, addOptionaLTermToFst ins1 t1)) in 
              (pi1, Sleek.Sequence(his, Sleek.Sequence(Kleene repeat, Sleek.Sequence (Await (Sleek.Signals.present str), his1))), cur1)
            )
          | Some (ins, t) -> 


            (match cur1 with
            | None -> 
              (pi1, Sleek.Sequence(Sleek.Sequence(his, addOptionaLTermToFst ins t), Sleek.Sequence (Await (Sleek.Signals.present str), his1)), cur1)
          
            | Some (ins1, t1) -> 
              let repeat  = Sleek.Sequence (Await (Sleek.Signals.present str), Sleek.Sequence(his1, addOptionaLTermToFst ins1 t1)) in 
              (pi1, Sleek.Sequence(Sleek.Sequence(his, addOptionaLTermToFst ins t), Sleek.Sequence(Kleene repeat, Sleek.Sequence (Await (Sleek.Signals.present str), his1))), cur1)
            )
       ) temp
      )
    )[] current








| Present (Access(str::_), p1, p2)->
List.flatten (

    List.fold_left (fun acc (pi, his, cur) ->
    List.append acc (  
      match cur with 
      | None ->
          let then_branch = forward env [(pi, Empty, (setPresent str (Sleek.Signals.initUndef env) None))] p1 full in 
          (match p2 with 
          | None -> 
              List.map (fun (pi1, his1, cur1) -> 
              let temp = setAbsent str (Sleek.Signals.initUndef env) None in 
             
              match temp with 
              | None -> [(pi1, Sleek.Sequence(his, his1), cur1)]
              | Some _ -> 
                    [(pi1, Sleek.Sequence(his, his1), cur1); (pi, his, temp) ]
                    ) then_branch
          | Some p2 ->
            let else_branch = forward env [(pi, Empty, (setAbsent str (Sleek.Signals.initUndef env) None))] p2 full in 
            let combine = zip (then_branch,  else_branch) in 

            List.map (fun ((pi1, his1, cur1), (pi2, his2, cur2)) -> 
                    [(pi1, Sleek.Sequence(his, his1), cur1); (pi2, Sleek.Sequence(his, his2), cur2) ]
                    ) combine
           )

      | Some (SL ins, t) -> 
          let then_branch = forward env [(pi, Empty, (setPresent str ins t))] p1 full in 
          (*
          print_string (string_of_states current);
          print_string (string_of_states [(pi, Empty, (setPresent str ins t))]);
          print_string (string_of_states then_branch);
          *)

          (match p2 with 
          | None -> 
            List.map (fun (pi1, his1, cur1) -> 
              let temp = setAbsent str ins t in 
              match temp with 
              | None -> [(pi1, Sleek.Sequence(his, his1), cur1)]
              | Some _ -> 
                    [(pi1, Sleek.Sequence(his, his1), cur1); (pi, his, temp) ]
                    ) then_branch
          | Some p2 ->
            let else_branch = forward env [(pi, Empty, (setAbsent str (Sleek.Signals.initUndef env) None))] p2 full in 


            let combine = zip (then_branch,  else_branch) in 

            List.map (fun ((pi1, his1, cur1), (pi2, his2, cur2)) -> 
              match (cur1, cur2) with 
              | (None, None) -> [(pi1, his, cur1)]
              | (Some _, None) -> [(pi1, Sleek.Sequence(his, his1), cur1)]
              | (None, Some _ ) -> [(pi2, Sleek.Sequence(his, his2), cur2) ]
              | _ -> 
                    [(pi1, Sleek.Sequence(his, his1), cur1); (pi2, Sleek.Sequence(his, his2), cur2) ]
                    ) combine

          )
        
      | Some (W s, t) ->  
        let then_branch = forward env [(pi, Empty, (setPresent str (Sleek.Signals.initUndef env) None))] p1 full in 
          (match p2 with 
          | None -> List.map (fun (pi1, his1, cur1) -> 
                    [(pi1, Sleek.Sequence(Sequence(his, addOptionaLTermToFst (W s) t), his1), cur1); (pi, his, cur) ]
                    ) then_branch
          | Some p2 ->
            let else_branch = forward env [(pi, Empty, (setAbsent str (Sleek.Signals.initUndef env) None))] p2 full in 
            let combine = zip (then_branch,  else_branch) in 

            List.map (fun ((pi1, his1, cur1), (pi2, his2, cur2)) -> 
                    [(pi1, Sleek.Sequence(his, Sequence(his1, addOptionaLTermToFst (W s) t)), cur1); (pi2, Sleek.Sequence(his, Sequence(his2, addOptionaLTermToFst (W s) t)), cur2) ]
                    ) combine
          
          )

    
    ) ) [] current
)
  | Lambda (_, p) -> 

    forward env current p full  
    
  | NewExpr p -> 

    forward env current p full

  | FunctionCall (Variable "setTimeout", li) ->
  (*
      print_string (string_of_int time);
    raise (Foo "setTimeout");
    *)

    (match List.hd (List.tl li) with 
    | (Literal (INT n)) -> let time = n/1000 in 

        List.map (fun (pi, his, cur) -> 
          let (newTV1, newPi1) = getAnewVar_rewriting () in
          let newPi = Sleek.And(pi, Sleek.And(newPi1, Sleek.Atomic(Sleek.Gt, Var newTV1, Const time))) in 
          match cur with 
          | None -> (newPi, his, Some( SL (Sleek.Signals.initUndef env), Some(Sleek.Var newTV1)))
          | Some (ins, None) -> (newPi, his, Some( ins, Some(Sleek.Var newTV1)))
          | Some (ins, Some t) -> (Sleek.And(newPi, Sleek.Atomic(Sleek.Eq, t, Var  newTV1)), his, Some( ins, Some t))
          
          
        )
        current
       

    | _ -> current
    )


  | FunctionExpr (_, p) -> 

  
  forward env current p full

  | FunctionCall (_, p::_) -> 

  
  forward env current p full
*)
  



let normalize_effs effs = 
  List.filter (fun (pi, es) ->
    match (pi, es) with 
    | (_,  Sleek.Bottom) -> false 
    | _ -> true 
  )
  (List.map (
    fun (pi, es) -> (pi, Sleek.fixpoint ~f: normalizeES es)
  ) effs)
  
let normalize_effs_final effs = 
  List.filter (fun (pi, es) ->
    match (pi, es) with 
    | (_,  Sleek.Bottom) -> false 
    | _ -> true 
  )
  (List.map (
    fun (pi, es) -> (pi, Sleek.fixpoint ~f: normalizeES_final es)
  ) effs)
  

let forward_verification (prog : statement) (whole: statement list): string = 
  match prog with 
  | ModduleDeclear (mn, p_li , ex, pre, post) -> 
    let startTimeStamp = Sys.time() in 
    let env = List.fold_left (fun acc a ->  List.append acc 
      (match a with 
      | OUT str -> [str]
      | IN str -> [str]
      | _ -> []
      ) 
      ) [] p_li in 
      
    let init = (List.fold_left (fun acc (_, pre_es) ->
        List.append acc (splitEffects env pre_es)
        ) [] pre
      ) in 
    
    let raw_final = (*effects_inference*) forward env (List.map (fun (a, b) -> (a, b, 0))init) ex whole in 
    let final = List.map (fun state ->
        match state with 
        | (his, Some (cur), _) ->Sleek.normalize (True, Sleek.Sequence (his, fstToInstance ( Some (cur))))
        | (his, None, _) -> (True, his)
      ) raw_final in 

    let startTimeStamp01 = Sys.time() in

    let final = normalize_effs_final final in 

    let startTimeStamp1 = Sys.time() in
    let (verbose, _) = Sleek.verify_entailment (Sleek.Entail {lhs = final; rhs = (post) })  in 
    let startTimeStamp2 = Sys.time() in

    "\n========== Module: "^ mn ^" ==========\n" ^
    "[Pre  Condition] " ^ show_effects_list pre ^"\n"^
    "[Post Condition] " ^ show_effects_list post ^"\n"^
    "[Final  Effects] " ^ show_effects_list ( final) ^"\n"^
    "[Inferring Time] " ^ string_of_float ((startTimeStamp01 -. startTimeStamp) *.1000.0)^ " ms" ^"\n" ^
    "[Proving   Time] " ^ string_of_float ((startTimeStamp2 -. startTimeStamp1) *.1000.0)^ " ms" ^"\n\n" ^
    (*(string_of_inclusion final_effects post) ^ "\n" ^*)
    "[TRS: Verification for Post Condition]\n" ^ 
    "[" ^ (if verbose then "SUCCEED"  else "FAIL") ^ "]\n" ^ 
    (*Sleek.History.show history    ~verbose ^*) "\n\n"
    
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

   (*
   statck , heap, -> op semantcis 

   traces  -> instrumental semantics. 

   state |= logic

   then the logic. 

*)
