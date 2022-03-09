type event = Present of string | Absent of string | Undef of string

let show_event = function
  | Present name -> name
  | Absent name -> "!" ^ name
  | Undef name -> "@" ^ name ^ "@"

let compare_event ev1 ev2 : bool =
  match (ev1, ev2) with
  | Present e1, Present e2 -> String.compare e1 e2 == 0
  | Absent e1, Absent e2 -> String.compare e1 e2 == 0
  | Undef e1, Undef e2 -> String.compare e1 e2 == 0
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


let setPresent str lst= 
  let rec helper li = 
  match li with 
  | [] -> []
  | (Undef s):: xs -> if String.compare s str == 0 then (Present str) :: xs else (Undef s)::helper xs
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

let setAbsent str lst= 
  let rec helper li = 
  match li with 
  | [] -> []
  | (Undef s):: xs -> if String.compare s str == 0 then (Absent str) :: xs else (Undef s)::helper xs
  | x :: xs -> x::helper xs in 
  Some (helper lst)
;;
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

let rec delete_shown_sig  env _sig=
  match env with 
  | [] -> []
  | x::xs -> if String.compare x _sig == 0 then xs
            else x:: (delete_shown_sig xs _sig )

let rec add_UndefSigs env ins = 
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
  assert ([ present "A" ] |- []);
  assert ([ present "A" ] |- [ present "A" ]);
  assert ([ present "A"; present "B" ] |- [ present "A" ])
