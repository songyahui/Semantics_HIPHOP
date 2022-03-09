type entry = {
  mutable first : Inference.Set.elem option;
  mutable iterations : (string * Ast.simple_entailment) list;
  mutable unfoldings : entry list;
  mutable terms : Ast.term list option;
  mutable constraints : Ast.pi option;
  mutable verdict : bool option;
}

let make_entry () =
  {
    first = None;
    iterations = [];
    unfoldings = [];
    terms = None;
    constraints = None;
    verdict = None;
  }


let set_first (i, t) hist = hist.first <- Some (i, t)

let add_iteration (label, es) hist =
  (* Printf.printf "%s :: %s\n" label (Ast.show_entailment es); *)
  hist.iterations <- (label, es) :: hist.iterations


let add_unfolding sub hist = hist.unfoldings <- sub :: hist.unfoldings

let set_terms terms hist = if List.length terms > 0 then hist.terms <- Some terms

let set_constraints constrnt hist = hist.constraints <- Some constrnt

let set_verdict verdict hist = hist.verdict <- Some verdict

let show_entry hist ~verbose =
  let rec aux spaces prefix hist =
    let first = ref true in
    let get_prefix () =
      if !first then (
        first := false;
        prefix)
      else
        spaces
    in
    let id x = x in
    let print name message =
      Printf.sprintf "%s%10s %s┃%s  %s%s%s" Colors.yellow name Colors.magenta Colors.reset
        (get_prefix ()) message Colors.reset
    in
    let show_first =
      match hist.first with
      | None        -> id
      | Some (i, t) ->
          let first =
            Printf.sprintf "%s%s, %s%s" Colors.magenta (Signals.show i) Colors.yellow
              (match t with
              | None   -> "_"
              | Some t -> Ast.show_term t)
          in
          List.cons (print "-" first)
    in
    let show_iterations =
      if verbose then
        List.fold_right
          (fun (name, entailment) acc -> print name (Ast.show_simple_entailment entailment) :: acc)
          hist.iterations
      else
        List.cons
          (let name, entailment = List.hd hist.iterations in
           print name (Ast.show_simple_entailment entailment))
    in
    let show_unfoldings =
      List.fold_right List.cons
        (List.mapi
           (fun i x ->
             let prefix' = get_prefix () in
             if i = 0 then
               aux (prefix' ^ "   ") (prefix' ^ "└──") x
             else
               aux (prefix' ^ "│  ") (prefix' ^ "├──") x)
           hist.unfoldings)
    in
    let _show_terms =
      match hist.terms with
      | None       -> id
      | Some terms ->
          List.cons
            (print "(TERMS)"
               (Colors.yellow ^ (List.map Ast.show_term terms |> String.concat ", ") ^ Colors.reset))
    in
    let show_constraints =
      match hist.constraints with
      | None      -> id
      | Some True -> id
      | Some con  -> List.cons (print "(CHECK)" (Ast.show_pi con))
    in
    let show_verdict =
      match hist.verdict with
      | None         -> id
      | Some verdict ->
          List.cons
            (print "(RESULT)"
               (Colors.blue ^ Colors.italic
               ^ (if verdict then "SUCCESS" else "FAILURE")
               ^ Colors.reset))
    in
    [] |> show_first |> show_iterations |> show_unfoldings |> show_constraints |> show_verdict
    |> List.rev |> String.concat "\n"
  in
  aux "" "" hist


type t = entry list list

let from_entries l = l

let roman n =
  assert (n >= 0);
  let digits = [| ""; "I"; "V"; "X"; "L"; "C"; "D"; "M"; "V"; "X"; "L"; "C"; "D"; "M" |] in
  let idx =
    [|
      [];
      [ 1 ];
      [ 1; 1 ];
      [ 1; 1; 1 ];
      [ 1; 2 ];
      [ 2 ];
      [ 2; 1 ];
      [ 2; 1; 1 ];
      [ 2; 1; 1; 1 ];
      [ 1; 3 ];
    |]
  in
  let rec aux p n =
    match (p, n) with
    | 0, 0 -> "O"
    | _, 0 -> ""
    | p, n ->
        let d = n mod 10 in
        let t = List.fold_left (fun acc x -> acc ^ digits.(p + x)) "" idx.(d) in
        aux (p + 2) (n / 10) ^ t
  in
  aux 0 n


let case_no i j =
  assert (i >= 0 && j >= 0);
  let i = roman i in
  Printf.sprintf "%s-%d" i j


let show hist ~verbose =
  let _, output =
    List.fold_left
      (fun (i, acc) l ->
        ( i + 1,
          let _, subh =
            List.fold_left
              (fun (j, acc2) sub ->
                ( j + 1,
                  let entry = show_entry sub ~verbose in
                  let label =
                    Printf.sprintf "%s%-10s %s┃" Colors.bold (case_no i j) Colors.reset
                  in
                  entry :: label :: acc2 ))
              (1, []) l
          in
          List.rev subh :: acc ))
      (1, []) hist
  in
  String.concat "\n" (List.concat (List.rev output))


let () =
  (* test case_no *)
  assert (case_no 0 0 = "O-0");
  assert (case_no 0 1 = "O-1");
  assert (case_no 1 1 = "I-1");
  assert (case_no 2 1 = "II-1");
  assert (case_no 3 2 = "III-2");
  assert (case_no 4 2 = "IV-2");
  assert (case_no 5 3 = "V-3");
  assert (case_no 6 3 = "VI-3");
  assert (case_no 7 3 = "VII-3");
  assert (case_no 8 3 = "VIII-3");
  assert (case_no 9 3 = "IX-3");
  assert (case_no 10 3 = "X-3");
  assert (case_no 11 3 = "XI-3");
  assert (case_no 12 3 = "XII-3");
  assert (case_no 13 3 = "XIII-3");
  assert (case_no 14 3 = "XIV-3");
  assert (case_no 15 3 = "XV-3");
  assert (case_no 19 3 = "XIX-3");
  assert (case_no 20 3 = "XX-3");
  assert (case_no 40 3 = "XL-3");
  assert (case_no 45 3 = "XLV-3");
  assert (case_no 50 3 = "L-3");
  assert (case_no 60 3 = "LX-3");
  assert (case_no 90 3 = "XC-3");
  assert (case_no 99 3 = "XCIX-3");
  assert (case_no 100 3 = "C-3");
  assert (case_no 200 3 = "CC-3");
  assert (case_no 400 3 = "CD-3");
  assert (case_no 450 3 = "CDL-3");
  assert (case_no 455 3 = "CDLV-3");
  assert (case_no 456 3 = "CDLVI-3");
  assert (case_no 456 3 = "CDLVI-3");
  assert (case_no 495 3 = "CDXCV-3");
  assert (case_no 499 3 = "CDXCIX-3");
  assert (case_no 999 3 = "CMXCIX-3");
  assert (case_no 1000 3 = "M-3");
  assert (case_no 1100 3 = "MC-3");
  assert (case_no 1500 3 = "MD-3");
  assert (case_no 2500 3 = "MMD-3");
  assert (case_no 3999 3 = "MMMCMXCIX-3");
  assert (case_no 4000 3 = "MV-3");
  assert (case_no 9000 3 = "MX-3");
  ()
