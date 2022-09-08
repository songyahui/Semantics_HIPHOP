type literal = 
| INT of int
| STRING of string
| BOOL of bool


type value = 
| Unit
| Variable of string
| Literal of literal
| Access of string list 

let constructUnit : value = Unit
let constructVariable str : value = Variable  str
let constructLiteral lit : value = Literal lit
let constructAccess acc : value = Access acc

let constructINT i = INT i 
let constructSTRING str = STRING str
let constructBOOL b = BOOL b

let makeSignal (a:string) (b:value option )= (a, b) 


type _signal = string * value option 

type event = Present of _signal | Absent of _signal | Undef of _signal 


let string_of_literal (l:literal) : string = 
  match l with 
  | STRING str -> str
  | INT n -> string_of_int n 
  | BOOL f -> string_of_bool f
  ;;

let string_of_value (v:value) : string = 
  match v with 
  | Unit -> "()"
  | Variable mn -> mn
  | Literal lit -> string_of_literal lit
  | Access mn_li -> List.fold_left (fun acc a -> acc ^"."^a) "." mn_li   
;;

let string_of_signals ((str, vopt):_signal) : string = 
  str ^ 
    (match vopt with 
    | None -> ""
    | Some ex ->"(" ^  string_of_value ex ^")"
    )
;;

let show_event = function
  | Present name -> string_of_signals name
  | Absent name -> "!" ^ string_of_signals name
  | Undef name -> "@" ^ string_of_signals name ^ "@"

let compareLiteral l1 l2 : bool =
  match l1, l2 with 
  | INT i1, INT i2 -> i1 == i2 
  | STRING s1, STRING s2 -> String.compare s1 s2 == 0 
  | BOOL b1, BOOL b2 -> Bool.compare b1 b2 == 0 
  | _ -> false 

let rec compareAccess acc1 acc2 : bool = 
  match acc1, acc2 with 
  | [], [] -> true 
  | x::xs, y::ys -> String.compare x y == 0 && compareAccess xs ys 
  | _ -> false 
;;
  

let compareValue v1 v2 : bool  =
 match v1, v2 with 
 | Unit, Unit -> true 
 | Variable s1, Variable s2 -> String.compare s1 s2 == 0 
 | Literal l1, Literal l2 -> compareLiteral l1 l2
 | Access acc1, Access acc2 -> compareAccess acc1 acc2 
 | _ -> false 
;;
 

 

let compareValueOpt v1opt v2opt : bool =
  match v1opt, v2opt with 
  | None, None -> true 
  | Some v1, Some v2 -> compareValue  v1 v2 
  | _ -> false 

let compareSignal (s1, v1) (s2, v2) : bool = String.compare s1 s2 == 0 && compareValueOpt v1 v2 

let compare_event ev1 ev2 : bool =
  match (ev1, ev2) with
  | Present (e1, v1), Present (e2, v2) -> compareSignal (e1, v1) (e2, v2)
  | Absent (e1, v1), Absent (e2, v2) -> compareSignal (e1, v1) (e2, v2) 
  | Undef (e1, v1), Undef (e2, v2) -> compareSignal (e1, v1) (e2, v2)
  | _ -> false 

(* To test if the event ev Exist in instant ins *)
let rec isEventExist ev ins : bool =
  match ins with
  | []      -> false
  | x :: xs -> if compare_event x ev then true else isEventExist ev xs

(* To test if the event list contains controdicts {S, !S} *)
let rec controdicts ins = 
  match ins with 
  | [] -> false 
  | Present s :: xs -> if (isEventExist (Absent s) xs (*|| isEventExist (Undef s) xs*)) then true else controdicts xs
  | Absent s :: xs -> if isEventExist (Present s) xs then true else controdicts xs
  | Undef _ :: xs -> (*if isEventExist (Present s) xs then true else*) controdicts xs
  ;;

let rec controdicts_final ins = 
  match ins with 
  | [] -> false 
  | Present s :: xs -> if (isEventExist (Absent s) xs || isEventExist (Undef s) xs) then true else controdicts_final xs
  | Absent s :: xs -> if isEventExist (Present s) xs then true else controdicts_final xs
  | Undef s :: xs -> if isEventExist (Present s) xs then true else controdicts_final xs
  ;;

let fstHelper ev = 
  match ev with 
  | Present str -> [(Present str); (Undef str)]
  | Absent str -> [(Absent str); (Undef str)]
  | x -> [(x)]
;;


let present name = Present name

let absent name = Absent name

let undefine name = Undef name 

let is_present = function
  | Present _ -> true
  | _ -> false 


(* Type of signals *)
type t = event list

let show = function
  | [] -> "{}"
  | l  -> "{" ^ String.concat ", " (List.map show_event(List.filter(fun a -> match a with |Present _ -> true | Absent _ -> true | _ -> false  ) l)) ^ "}"


(* Empty signal *)
let empty = []

let is_empty = function
  | [] -> true
  | _  -> false


let from name = [ present name ]

(* Make new signal from name list *)
let make lst = List.sort_uniq compare lst

let initUndef lst = List.map (fun a -> undefine a) lst


let setPresent (ev:_signal) lst = 
  let rec helper li = 
  match li with 
  | [] -> [(Present ev)]
  | (Undef s):: xs -> if compareSignal ev s  then (Present ev) :: xs else (Undef s)::helper xs
  | x :: xs -> x::helper xs in 
  Some (helper lst)
;;

let setAbsent (ev:_signal) lst = 
  let rec helper li = 
  match li with 
  | [] -> [(Absent ev)]
  | (Undef s):: xs -> if compareSignal ev s  then (Absent ev) :: xs else (Undef s)::helper xs
  | x :: xs -> x::helper xs in 
  Some (helper lst)
;;

(*
let rec setPresent str lst= 
  match lst with 
  | [] -> Some []
  | (Absent s):: xs -> 
    if String.compare s str == 0 then None (* signal status controdiction *)
    else 
      (match setPresent str xs with 
      | None -> None 
      | Some rest -> Some ((Absent s) :: rest)  (* signal status controdiction *)
      )
  | (Undef s):: xs -> if String.compare s str == 0 then 
      match setPresent str xs with 
      | None -> None 
      | Some rest -> Some ((Present s) :: rest)  (* signal status controdiction *)
    else  
      (match setPresent str xs with 
      | None -> None 
      | Some rest -> Some ((Undef s) :: rest)  (* signal status controdiction *)
      )
    
  | x::xs -> 
    match setPresent str xs with 
    | None -> None 
    | Some rest -> Some (x :: rest)  (* signal status controdiction *)
   *)


  (*
  match lst with 
  | [] -> Some []
  | (Present s):: xs -> 
    if String.compare s str == 0 then None (* signal status controdiction *)
    else 
      (match setAbsent str xs with 
      | None -> None 
      | Some rest -> Some ((Present s) :: rest)  (* signal status controdiction *)
      )
  | (Undef s):: xs -> if String.compare s str == 0 then 
      match setAbsent str xs with 
      | None -> None 
      | Some rest -> Some ((Absent s) :: rest)  (* signal status controdiction *)
    else  
      (match setAbsent str xs with 
      | None -> None 
      | Some rest -> Some ((Undef s) :: rest)  (* signal status controdiction *)
      )
    
  | x::xs -> 
    match setAbsent str xs with 
    | None -> None 
    | Some rest -> Some (x :: rest)  (* signal status controdiction *)
   *)

let rec delete_shown_sig  (env:_signal list) _sig=
  match env with 
  | [] -> []
  | x::xs -> if compareSignal x _sig then xs
            else x:: (delete_shown_sig xs _sig )

let rec add_UndefSigs (env:_signal list) (ins:event list) = 
  match ins with 
  | [] -> initUndef env
  | (Present str)::xs -> 
    let newEnv = delete_shown_sig env str in 
    (Present str)::(add_UndefSigs newEnv xs)
  | (Absent str)::xs ->
    let newEnv = delete_shown_sig env str in 
    (Absent str)::(add_UndefSigs newEnv xs)
  | (Undef str)::xs ->
    let newEnv = delete_shown_sig env str in 
    (Undef str)::(add_UndefSigs newEnv xs)

    

(* Merge signals `a` and `b` into a new one *)
let merge a b = 
  let rec helper left list = 
    match left with 
    | [] -> []
    | x :: xs -> (
      match x with 
      | Undef str -> if (isEventExist (Absent str) list || isEventExist (Present str) list ) then helper xs list else x :: (helper xs list)
      | _ -> x :: (helper xs list)
    )
  in 
  let aa = helper a b in 
  let bb = helper b a in 
  
  List.sort_uniq compare (aa @ bb)


(* Is `b` included in `a`? *)
let ( |- ) a b = (*b |> List.fold_left (fun res y -> res && a |> List.exists (( = ) y)) true*)
  List.fold_left (fun acc ev -> acc && (
    match ev with 
    | Present _ 
    | Absent _ -> isEventExist ev a 
    | _ -> true 
  )) true b
(* tests *)
let () =
  assert ([] |- []);
  assert ([ present ("A", None) ] |- []);
  assert ([ present ("A", None) ] |- [ present ("A", None) ]);
  assert ([ present ("A", None); present ("B", None) ] |- [ present ("A", None) ])
