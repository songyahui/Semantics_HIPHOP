
open Pretty
open Ast
open List

exception Foo of string


type fst4Par = Sig of Sleek.Signals.t | Wait of Sleek.Signals.event 

let rec fstPar (es:Sleek.instants) :fst4Par list = 
  match es with 
  | Bottom -> []
  | Empty -> []
  | Await ev -> [(Wait ev)] (*[Sleek.Signals.fstHelper ev ]*)
  | Instant ins -> [(Sig ins)]
  | Sequence (es1 , es2) -> if Sleek.Inference.nullable es1 then append (fstPar  es1) (fstPar  es2) else fstPar  es1
  | Union (es1, es2) -> append (fstPar  es1) (fstPar  es2)
  | Kleene es1 -> fstPar  es1
  | Parallel (es1 , es2) -> append (fstPar  es1) (fstPar  es2)
  | _ -> raise (Foo "fstPar later")
    

let fst4Par2Instants f : Sleek.instants = 
  match f with 
  | Sig ins -> Instant ins
  | Wait ev -> Await ev 
;;

let waitToIns (w:Sleek.Signals.event): Sleek.Signals.t = [w]


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
      if String.compare str name == 0 then (p_li, pre, List.hd post)
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

let setPresent str v (cur) = (Sleek.Signals.setPresent (Sleek.Signals.makeSignal str v) cur);; 

let setAbsent str v  (cur)  = (Sleek.Signals.setAbsent (Sleek.Signals.makeSignal str v) cur);;

let max k1 k2 = if k1 >= k2 then k1 else k2 

let unionCur c1 c2 = 
  match (c1, c2) with 
  | (None, None) -> None 
  | (Some cur1, Some cur2) -> Some (Sleek.Signals.merge cur1 cur2)
  | (Some _, None ) -> c1 
  | _ -> c2

let parrallHisAndCur his cur =
  match cur with 
  | None -> None 
  | Some cur1 -> let fst = fstPar his in 
    (match (List.hd fst) with 
    | Sig f -> Some (Sleek.Signals.merge cur1 f)
    | _ -> raise (Foo "parrallHisAndCur")
    )

let parrallHisAndCurAbsorb  (his:Sleek.instants ) (cur:Sleek.Signals.t option) : Sleek.instants =
  match cur with 
  | None -> his 
  | Some cur1 -> 
    let fst = List.hd (fstPar his) in 
    (match fst with
    | Sig f -> 
      let head = (Sleek.Signals.merge cur1 f) in 
      let der = derivativePar head his in
      let list = [(Sleek.Sequence (Sleek.Instant head, der)) ] 
      in let rec helper li = 
        match li with 
        | [] -> Sleek.Bottom 
        | x::xs -> Sleek.Union (x,  (helper xs))
      in helper list
    | _ -> raise (Foo "parrallHisAndCurAbsorb"))



let fstToInstance cur = 
  match cur with 
  | None -> Sleek.Empty
  | Some ins ->  Sleek.Instant ins 
;;
  

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

        match f1, f2 with 
        | Sig f1, Sig f2 ->
          let head =  (Sleek.Signals.merge f1 f2) in 
          let der1 = normalizeES (derivativePar head his1) in 
          let der2 = normalizeES (derivativePar head his2) in
          let states =  paralleMerge [(der1, cur1, k1)] [(der2, cur2, k2)] in 
          List.map (fun (a, b, c) -> (Sleek.Sequence (Instant head, a), b, c)) states
        | Wait _, Wait _ ->
          [(Sleek.Parallel (Sleek.Sequence (his1, fstToInstance cur1), Sleek.Sequence (his2, fstToInstance cur2)), None(*Some(Sleek.Signals.empty)*), max k1 k2)]    
        | Sig f, Wait _ 
        | Wait _, Sig f -> 
          let der1 = normalizeES (derivativePar f his1) in 
          let der2 = normalizeES (derivativePar f his2) in
          let states =  paralleMerge [(der1, cur1, k1)] [(der2, cur2, k2)] in 
          List.map (fun (a, b, c) -> (Sleek.Sequence (Instant f, a), b, c)) states

        )
      headSet)

  )
  combine)
  
let literalToSigLiteral (l:literal) :Sleek.Signals.literal = 
  match l with 
  | INT i -> Sleek.Signals.constructINT i 
  | STRING str -> Sleek.Signals.constructSTRING str
  | BOOL b -> Sleek.Signals.constructBOOL b

;;literalToSigLiteral

let valueToSigValue (v:value) : Sleek.Signals.value = 
  match v with 
| Unit -> Sleek.Signals.constructUnit
| Variable str -> Sleek.Signals.constructVariable str
| Literal lit -> Sleek.Signals.constructLiteral (literalToSigLiteral lit) 
| Access acc -> Sleek.Signals.constructAccess acc
;;

let rec makeEnv (env:event list): Sleek.Signals._signal list =
  match env with 
  | [] -> [] 
  | (str, None) :: xs -> Sleek.Signals.makeSignal str (None) :: makeEnv xs 
  | (str, Some v) :: xs -> 
    Sleek.Signals.makeSignal str (Some (valueToSigValue v)) :: makeEnv xs 

;;
  

let rec splitEffects (env: string list) (es:Sleek.instants) :(Sleek.instants* (Sleek.Signals.t) option) list= 
  let es = normalizeES es  in 
  match es with 
  | Bottom -> []
  | Empty -> [(Empty, None)]
  | Await s -> [(Await s,None)]
  | Instant ins -> [(Empty, Some (ins))]
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

let vOptToSigvOpt (v:value option) : Sleek.Signals.value option = 
  match v with 
  | None -> None 
  | Some v -> Some (valueToSigValue v)


let rec addInToTheTail (es:Sleek.instants) (ev:event) : (Sleek.instants)  = 
  let (str, v) = ev in 
  (*print_string (Sleek.show_instants (fstToInstance ( (setPresent str (vOptToSigvOpt v) Sleek.Signals.empty))));*)
  match es with 
  | Sequence (es1, Parallel(es2, es3)) -> Sequence (es1, Parallel(addInToTheTail es2 ev, addInToTheTail es3 ev))
  | Sequence (es1, Instant cur) ->  Sequence (es1,fstToInstance ( (setPresent str (vOptToSigvOpt v) cur)))
  | Sequence (es1, es2) -> Sequence (es1, addInToTheTail es2 ev)
  | Instant cur ->fstToInstance (setPresent str (vOptToSigvOpt v) cur)
  | Bottom
  | Empty
  | Await  _  -> es 
  | Union    (es1, es2) -> Union (addInToTheTail es1 ev, addInToTheTail es2 ev)
  | Parallel (es1, es2) -> Parallel(addInToTheTail es1 ev, addInToTheTail es2 ev)
  | Kleene   (es1) -> Sequence (es1, addInToTheTail es1 ev)
  | _   -> raise (Foo "addInToTheTail")



let addEventToCur (env:event list) (ev:Sleek.Signals.event) (cur: Sleek.Signals.t option):Sleek.Signals.t option=
  match cur with 
  | None ->  Some (ev :: (Sleek.Signals.initUndef (makeEnv env)))
  | Some ins ->  Some (ev :: ins )
;;


let rec insertNegation (es:Sleek.instants) (ev) : (Sleek.instants) = 
  let (str, v) = ev in 
  let aux arg = (setAbsent str (vOptToSigvOpt v) arg) in 
  match es with 
  | Instant ins -> (fstToInstance (aux ins))
  | Sequence (es1, es2) -> Sequence (insertNegation es1 ev, insertNegation es2 ev) 
  | Union (es1, es2) -> Union (insertNegation es1 ev, insertNegation es2 ev) 
  | Parallel (es1, es2) -> Parallel (insertNegation es1 ev, insertNegation es2 ev) 
  | Kleene es1 -> Kleene (insertNegation es1 ev)
  | _ -> es
  ;;



let rec abortinterleaving (pre:Sleek.instants) (es:Sleek.instants) (ev) : prog_states = 
  let es = Sleek.fixpoint ~f: Sleek.normalize_es  es in 
  match es with 
  | Sleek.Kleene es' ->
    let non_abortion = insertNegation es' ev in 
    let prepenx = Sleek.Sequence(pre, Kleene non_abortion) in 
    let interleav = (abortinterleaving (Sleek.Empty) es' ev) in 
    (*(prepenx, None, 0) :: *)
    List.map (fun (a, b, k) -> (Sleek.Sequence(prepenx, a), b, k) ) interleav

  | Sleek.Sequence (Sleek.Kleene es', _) -> 
    let non_abortion = insertNegation es' ev in 
    let prepenx = Sleek.Sequence(pre, Kleene non_abortion) in 
    let interleav = (abortinterleaving (Sleek.Empty) es' ev) in 
    (*(prepenx, None, 0) :: *)
    List.map (fun (a, b, k) -> (Sleek.Sequence(prepenx, a), b, k) ) interleav

  | _ -> 
  let (str, v) = ev in 
  let fSet = fstPar es in 
  List.flatten (List.map (fun ele -> 
    match ele with 
    | Sig ele' -> 
      let thisOne = (pre, setPresent str (vOptToSigvOpt v) ele' , 0) in 
      let tail =  abortinterleaving (Sleek.Sequence(pre, fstToInstance (setAbsent str (vOptToSigvOpt v) (ele')))) (derivativePar ele' es) ev  in 
      thisOne :: tail
    | Wait ev' -> abortinterleaving (Sleek.Sequence(pre, fst4Par2Instants ele)) (derivativePar (waitToIns ev') es) ev
  )fSet)

;;



let rec suspendinterleaving (es:Sleek.instants) (cur:(Sleek.Signals.t) option) (ev) : prog_states = 
  let (str, v) = ev in 
  let fSet = fstPar es in 
  if List.length fSet == 0 then 
    (match cur with 
    | None -> [(Sleek.Empty, None, 0)] 
    | Some cur' -> 
      let op1 = (setAbsent str (vOptToSigvOpt v) (cur')) in 
      let op2 = fstToInstance (setPresent str (vOptToSigvOpt v) (Sleek.Signals.empty))  in 
      [(Sleek.Empty, op1, 0); (op2, op1, 0)]
    )
  else 
  List.flatten (List.map (fun ele -> 
    let aux pre rest = List.map (fun (a, b, k) -> (Sleek.Sequence(pre, a), b, k)) rest in 
    match ele with 
    | Sig ele' -> 
      let op1 = fstToInstance (setAbsent str (vOptToSigvOpt v) (ele')) in 
      let op2 = Sleek.Sequence (fstToInstance (setPresent str (vOptToSigvOpt v) (Sleek.Signals.empty)) , op1) in 
      let rest = suspendinterleaving (derivativePar ele' es) cur ev in (*yaya is pretty*)
      List.append (aux op1 rest) (aux op2 rest)
    | Wait ev' -> 
      let rest = suspendinterleaving (derivativePar (waitToIns ev') es) cur ev in 
      aux (fst4Par2Instants ele) rest
      
    
    (*
    
      (match derivativePar ele' es with
      | Sleek.Empty -> [(Sleek.Empty, fstToInstance (setAbsent str (vOptToSigvOpt v) (ele')) , 0); (Sleek.Empty, , 0)]


      )

      let thisOne = (pre, setPresent str (vOptToSigvOpt v) ele' , 0) in 
      let tail =  suspendinterleaving (Sleek.Sequence(pre, fstToInstance (setAbsent str (vOptToSigvOpt v) (ele')))) (derivativePar ele' es) ev  in 
      thisOne :: tail
    | Wait ev' -> suspendinterleaving (Sleek.Sequence(pre, fst4Par2Instants ele)) (derivativePar (waitToIns ev') es) ev
    *)
  )fSet)

;;


let rec forward (env:string list) (current:prog_states) (prog:expression) (full: statement list): prog_states =

  match prog with 
  | Value _ -> current
  | Yield -> 
      List.map (fun state -> 
      let (his, cur, _) = state in 
      (Sleek.Sequence (his, fstToInstance cur), Some (Sleek.Signals.empty), 0)) current

  | Await (Ev (str, v )) -> 
    List.map (fun (his, cur, _) -> (Sleek.Sequence(Sleek.Sequence (his, fstToInstance cur), Await (Sleek.Signals.present (Sleek.Signals.makeSignal str (vOptToSigvOpt v)))), 
    Some (Sleek.Signals.empty), 0))
    current

  
  | Emit (str, v) -> 


      List.map (fun state ->
        match state with 
        | (his, Some (cur), _) -> (his , setPresent str (vOptToSigvOpt v) cur, 0)
        | (his, None, _ ) -> 
          let trace =  addInToTheTail (Sleek.normalize_es his) (str, v) in 
          (*print_string (Sleek.show_instants  trace^"\n");*)
          (trace, None, 0)
          (*match with 
          | Some trace -> (trace, None, 0)
          | None -> (his, None, 0)*)
        
      )  current

  | Signal (s, p) -> forward (s::env) current p full 

  | Seq (p1, p2) -> 
    let states1 =  (forward env current p1 full) in 
    List.flatten (
      List.map (fun (his, cur, k) -> 
      if k > 1 then [(his, cur, k)]
      else forward env [(his, cur, k)] p2 full

      ) states1
    )
    
    
  
  | Async (ev, p, q) -> 
    let branch1 = Seq (p, Emit ev) in 
    let desugar = ForkPar [branch1; q] in 
    forward env current desugar full

  


  | Exit d -> 
    List.map (fun (a, b, _) -> (a, b, d+2) ) current

  | Trap p  -> 
    let state1 = forward env current p full in 
    List.flatten (
      List.map (fun (his, cur, k) ->
        if k =2 then [((his, cur, 0))]
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
        else 
          (let second_round = forward env [(Empty, cur1, k1)] p full in 
          List.map (fun (his2, cur2, k2)->
            (Sleek.Sequence (his, Sequence(his1, Kleene (his2))), cur2, k2)
          ) second_round)
          (*
          (List.flatten(List.map (fun (his2, cur2, k2)->
          if k2 >1 then [(his2, cur2, k2)]
          else 
            let thrid_round = forward env [(Empty, cur2, k2)] p full in 
            List.map (fun (his3, cur3, k3)->
              (Sleek.Sequence (his, Sequence(Sequence(his1, his2), Kleene (his3))), cur3, k3)
              )
            thrid_round

          ) second_round))   
          *)
      ) first_round
      )
    ) ) [] current

  | Abort (ev, p)  -> 


    let (str, v) = ev in 
    List.flatten (List.map (fun (his, cur, k) ->
      let pEff = forward env [(Empty, cur, k)] p full in 

      let allPosibleAux = List.map (fun (a, b, k) -> 
        if k > 1 then [(a, b, k)]
        else  
          let aux = match b with 
          | None -> None 
          | Some b' -> setAbsent str (vOptToSigvOpt v) b'
          in 
          (*print_string (Sleek.show_instants ((Sleek.Sequence (a, fstToInstance b))) ^"\n");*)
          (insertNegation a ev, aux, k)  :: (abortinterleaving (Sleek.Empty) (Sleek.Sequence (a, fstToInstance b)) ev)
      ) pEff in 
      let allPosible = List.fold_left (fun acc a -> List.append acc a) [] allPosibleAux in 
      List.map (fun (a, b, c) -> (Sleek.Sequence(his, a), b, c)) allPosible
    ) current)

  
  | Suspend (ev, p)  ->  
    let (str, v) = ev in 
    List.flatten (List.map (fun (his, cur, k) ->
      let pEff = forward env [(Empty, cur, k)] p full in 
      let allPosibleAux = List.map (fun (a, b, k) -> 
          let aux = match b with 
          | None -> None 
          | Some b' -> setAbsent str (vOptToSigvOpt v) b'
          in 
          (insertNegation a ev, aux, k)  :: (suspendinterleaving (Sleek.Sequence (a, fstToInstance b)) b ev)
      ) pEff in 
      let allPosible = List.fold_left (fun acc a -> List.append acc a) [] allPosibleAux in 
      List.map (fun (a, b, c) -> (Sleek.Sequence(his, a), b, c)) allPosible
    ) current)


  
  | DoEvery (p, ev) -> 
    let halt = Loop (Yield) in 
    let helper expr cond = Abort (cond, Seq(expr, halt)) in 
    let loopEach expr cond = Loop (helper expr cond)  in 
    let _ = Seq (Await (Ev ev), loopEach p ev) in 
    forward env current (loopEach p ev) full  

  | Present ((str, v), p1, p2) -> 
    let s1 = List.map (fun state -> 
      let (his, cur, k) = state in 
      match cur with 
      | Some cur' -> (his, setPresent str (vOptToSigvOpt v) cur', k)
      | None -> (his, cur, k) 
    ) current in 
    let s2 = List.map (fun state -> 
      let (his, cur, k) = state in 
      match cur with 
      | Some cur' -> (his, setAbsent str (vOptToSigvOpt v) cur', k)
      | None -> (his, cur, k) 
    ) current in 

    let ifbranch =  forward env s1 p1 full in 
    let elsebranch =  forward env s2 p2 full in 
    List.append ifbranch elsebranch



  | _ ->  raise (Foo(string_of_expression_kind prog ^ " not yet covered!"))
 
    ;;
  


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
  

let entailmentShell lhs rhs = 
  let startTimeStamp1 = Sys.time() in
  let (verbose, tree) = Sleek.verify_entailment (Sleek.Entail {lhs = lhs; rhs = (rhs) })  in 
  let startTimeStamp2 = Sys.time() in
  let msg =  (*(string_of_inclusion final_effects post) ^ "\n" ^*)
  "[TRS: Verification for Post Condition]\n" ^ 
  "[" ^ (if verbose then "SUCCEED"  else "FAIL") ^ "]\n" ^ 
  Sleek.History.show tree    ~verbose ^ "\n\n" in 
  print_string (msg);
  ((startTimeStamp2 -. startTimeStamp1) *.1000.0, verbose, tree)

let forward_verification (prog : statement) (whole: statement list): string = 
  match prog with 
  | ModduleDeclear (mn, p_li , ex, pre, posts) -> 
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
        | (his, cur, _) ->Sleek.normalize (True, Sleek.Sequence (his, fstToInstance ( (cur))))
      ) raw_final in 

    let startTimeStamp01 = Sys.time() in

    let final = normalize_effs_final final in 

    let results = List.map (fun rhs -> entailmentShell final rhs) posts in 

    let proves = List.filter (fun (_, b, _) -> b ==true ) results in 
    let disproves = List.filter (fun (_, b, _) -> b==false ) results in 
    let totol li = List.fold_left (fun acc (a, _, _) -> acc +. a) 0.0 li in  
    let printing li = string_of_int (List.length li) ^ " cases with avg time " ^  string_of_float ((totol li)/.(float_of_int(List.length li))) ^ " ms\n" in 


    "\n========== Module: "^ mn ^" ==========\n" ^
    "[Pre  Condition] " ^ show_effects_list pre ^"\n"^
    "[Post Condition] " ^ show_effects_list_list posts ^"\n"^
    "[Final  Effects] " ^ show_effects_list ( final) ^"\n"^
    "[Inferring Time] " ^ string_of_float ((startTimeStamp01 -. startTimeStamp) *.1000.0)^ " ms" ^"\n" ^

    "[TOTAL TRS TIME] " ^ string_of_float (totol proves +. totol disproves) ^ " ms \n" ^ 
    "[Proving   Time] " ^ printing proves ^
    "[Disprove  Time] " ^ printing disproves ^"\n" 

    
    
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
