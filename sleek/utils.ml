let fixpoint ~f ?(fn_iter = fun _ -> ()) ?(fn_stop = fun _ -> ()) init =
  let rec iter cur =
    let next = f cur in
    if cur = next then (
      fn_stop cur; cur)
    else (
      fn_iter cur; iter next)
  in
  iter init


let opt_map2 ?(sn = fun x -> x) ?(ns = fun y -> y) ~ss = function
  | None, None     -> None
  | Some x, None   -> Some (sn x)
  | None, Some y   -> Some (ns y)
  | Some x, Some y -> Some (ss x y)
