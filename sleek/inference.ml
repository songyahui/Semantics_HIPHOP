open Ast
open Ast_helper

module Set = struct
  include List

  type elem = Signals.t * Ast.term option

  type t = elem list

  let empty = []

  let is_empty = function
    | [] -> true
    | _  -> false


  let from s t = [ (s, t) ]

  let union a b = a @ b |> List.sort_uniq Stdlib.compare

  let zip ctx a b =
    a
    |> List.fold_left
         (fun acc (es1, t1) ->
           acc
           @ (b
             |> List.map (fun (es2, t2) ->
                    let es' = Signals.merge es1 es2 in
                    match (t1, t2) with
                    | None, None -> (es', None)
                    | _          ->
                        let t' = ctx |> Proofctx.next_term in
                        (es', Some t'))))
         empty
    |> List.sort_uniq Stdlib.compare


  let () =
    let open Signals in
    assert (
      let ctx = Proofctx.make () in
      zip ctx [ (from "A", None) ] [ (from "B", None) ]
      = [ (make [ present "A"; present "B" ], None) ]);
    assert (
      let ctx = Proofctx.make () in
      zip ctx [ (from "A", None) ] [ (from "B", None); (from "C", None) ]
      = [ (make [ present "A"; present "B" ], None); (make [ present "A"; present "C" ], None) ]);
    assert (
      let ctx = Proofctx.make () in
      zip ctx [ (empty, None); (from "A", None) ] [ (empty, None); (from "B", None) ]
      = [
          (empty, None);
          (from "A", None);
          (make [ present "A"; present "B" ], None);
          (from "B", None);
        ]);
    ()
end

let rec is_bot = function
  | Bottom              -> true
  | Empty               -> false
  | Instant _           -> false
  | Await _             -> false
  | Sequence (es1, es2) -> is_bot es1 || is_bot es2
  | Union (es1, es2)    -> is_bot es1 && is_bot es2
  | Parallel (es1, es2) -> is_bot es1 || is_bot es2
  | Kleene _            -> false
  | Timed (es, _)       -> is_bot es


let rec nullable = function
  | Bottom              -> false
  | Empty               -> true
  | Instant _           -> false
  | Await _             -> false
  | Sequence (es1, es2) -> nullable es1 && nullable es2
  | Union (es1, es2)    -> nullable es1 || nullable es2
  | Parallel (es1, es2) -> nullable es1 && nullable es2
  | Kleene _            -> true
  | Timed (es, _)       -> nullable es


let first ctx es =
  let rec aux = function
    | Bottom -> Set.empty
    | Empty -> Set.empty
    | Instant i -> Set.from i None
    | Await e -> Set.(union (from Signals.empty None) (from (Signals.make [ e ]) None))
    | Sequence (es1, es2) when nullable es1 -> Set.union (aux es1) (aux es2)
    | Sequence (es1, _) -> aux es1
    | Union (es1, es2) -> Set.union (aux es1) (aux es2)
    | Parallel (es1, es2) -> Set.zip ctx (aux es1) (aux es2)
    | Kleene es -> aux es
    | Timed (es, _) ->
        aux es
        |> Set.map (function
             | i, None         ->
                 let t' = ctx |> Proofctx.next_term in
                 (i, Some t')
             | i, Some inner_t -> (i, Some inner_t))
  in
  aux es


let partial_deriv ctx (i, t') es =
  let rec aux es =
    match es with
    | Bottom -> Bottom
    | Empty -> Bottom
    | Instant j when Signals.(i |- j) -> Empty
    | Instant _ -> Bottom
    | Await e when Signals.(i |- make [ e ]) -> Empty
    | Await e -> Await e
    | Sequence (es1, es2) when nullable es1 ->
        let deriv1 = aux es1 in
        let deriv2 = aux es2 in
        Union (Sequence (deriv1, es2), deriv2)
    | Sequence (es1, es2) ->
        let deriv1 = aux es1 in
        Sequence (deriv1, es2)
    | Union (es1, es2) ->
        let deriv1 = aux es1 in
        let deriv2 = aux es2 in
        Union (deriv1, deriv2)
    | Parallel (es1, es2) ->
        let deriv1 = aux es1 in
        let deriv2 = aux es2 in
        Parallel (deriv1, deriv2)
    | Kleene es -> aux (Sequence (es, Kleene es))
    | Timed (es, t) -> (
        match t' with
        | None    -> Bottom
        | Some t' -> (
            match es with
            | Bottom -> Bottom
            | Empty -> Bottom
            | Instant j when Signals.(i |- j) ->
                ctx |> Proofctx.track_term t';
                ctx |> Proofctx.add_precond (t =* t');
                Empty
            | Instant _ -> Bottom
            | Await e when Signals.(i |- make [ e ]) ->
                ctx |> Proofctx.track_term t';
                ctx |> Proofctx.add_precond (t =* t');
                Empty
            | Await e ->
                let t1 = ctx |> Proofctx.next_term in
                let t2 = ctx |> Proofctx.next_term in
                let cond = t =* t1 +* t2 &&* (t1 >=* Const 0) &&* (t2 >=* Const 0) in
                ctx |> Proofctx.add_precond cond;
                ctx |> Proofctx.track_term t';
                ctx |> Proofctx.add_precond (t1 =* t');
                Timed (Await e, t2)
            | Sequence (es1, es2) ->
                let t1 = ctx |> Proofctx.next_term in
                let t2 = ctx |> Proofctx.next_term in
                let cond = t =* t1 +* t2 &&* (t1 >=* Const 0) &&* (t2 >=* Const 0) in
                ctx |> Proofctx.add_precond cond;
                aux (Sequence (Timed (es1, t1), Timed (es2, t2)))
            | Union (es1, es2) ->
                let t1 = ctx |> Proofctx.next_term in
                let t2 = ctx |> Proofctx.next_term in
                let deriv1 = aux (Timed (es1, t1)) in
                let deriv2 = aux (Timed (es2, t2)) in
                let cond =
                  match (is_bot deriv1, is_bot deriv2) with
                  | false, false -> t =* t1 ||* (t =* t2)
                  | false, true  -> t =* t1
                  | true, false  -> t =* t2
                  | true, true   -> True
                in
                ctx |> Proofctx.add_precond cond;
                Union (deriv1, deriv2)
            | Parallel (es1, es2) -> aux (Parallel (Timed (es1, t), Timed (es2, t)))
            | Kleene es ->
                let t1 = ctx |> Proofctx.next_term in
                let t2 = ctx |> Proofctx.next_term in
                let cond = t =* t1 +* t2 &&* (t1 >=* Const 0) &&* (t2 >=* Const 0) in
                ctx |> Proofctx.add_precond cond;
                aux (Sequence (Timed (es, t1), Timed (Kleene es, t2)))
            | Timed (_, inner_t) ->
                ctx |> Proofctx.add_precond (t =* inner_t);
                aux es))
  in
  aux es
