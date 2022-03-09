let verify_simple_entailment (Ast.SimpleEntail { lhs; rhs }) =
  let rec aux ctx first_opt (lhs : Ast.simple_effects) rhs =
    let hist = History.make_entry () in
    let () =
      match first_opt with
      | None        -> ()
      | Some (i, t) -> hist |> History.set_first (i, t)
    in
    let bot_lhs (_, es1) = es1 = Ast.Bottom
    and bot_rhs (_, es2) = es2 = Ast.Bottom
    and disprove (_, es1) (_, es2) = Inference.nullable es1 && not (Inference.nullable es2)
    and reoccur ctx (_, es1) (_, es2) = Proofctx.exists_entail es1 es2 ctx
    and unfold ctx (pi1, es1) (pi2, es2) =
      ctx |> Proofctx.add_entail es1 es2;
      let firsts = Inference.first ctx es1 in
      let terminate = Inference.Set.is_empty firsts in
      let verdict =
        firsts
        |> Inference.Set.for_all (fun x ->
               let ctx = Proofctx.clone ctx in
               let es1 = Inference.partial_deriv ctx x es1 in
               let es2 = Inference.partial_deriv ctx x es2 in
               let verdict, sub_hist = aux ctx (Some x) (pi1, es1) (pi2, es2) in
               hist |> History.add_unfolding sub_hist;
               verdict)
      in
      (verdict, terminate)
    and normal lhs rhs =
      let lhs =
        Utils.fixpoint ~f:Ast_helper.normalize
          ~fn_iter:(fun _ ->  ())
          (*fun es ->
            hist |> History.add_iteration ("NORM-LHS", SimpleEntail { lhs = es; rhs })*)
          lhs
      in
      let rhs =
        Utils.fixpoint ~f:Ast_helper.normalize
          ~fn_iter:(fun _ ->  ()) (*fun es ->
            hist |> History.add_iteration ("NORM-RHS", SimpleEntail { lhs; rhs = es })*)
          rhs
      in
      (lhs, rhs)
    in
    let check = function
      | false ->
          hist |> History.set_verdict false;
          false
      | true  ->
          let verdict, constrnt = ctx |> Proofctx.check_constraints in
          hist |> History.set_terms (ctx |> Proofctx.tracked_terms);
          hist |> History.set_constraints constrnt;
          hist |> History.set_verdict verdict;
          verdict
    in
    (* Verify *)
    let lhs, rhs = normal lhs rhs in
    let verdict =
      if bot_lhs lhs then (
        hist |> History.add_iteration ("Bot-LHS", SimpleEntail { lhs; rhs });
        check true)
      else if bot_rhs rhs then (
        hist |> History.add_iteration ("Bot-RHS", SimpleEntail { lhs; rhs });
        check false)
      else if disprove lhs rhs then (
        hist |> History.add_iteration ("DISPROVE", SimpleEntail { lhs; rhs });
        check false)
      else if reoccur ctx lhs rhs then (
        hist |> History.add_iteration ("REOCCUR", SimpleEntail { lhs; rhs });
        let _, es1 = lhs in
        let _, es2 = rhs in
        let gen = ctx |> Proofctx.current_term_gen in
        let t1, cond1 = Ast_helper.total_terms_of_es es1 gen in
        let t2, cond2 = Ast_helper.total_terms_of_es es2 gen in
        ctx |> Proofctx.add_precond Ast_helper.(t1 =* t2 &&* cond1 &&* cond2);
        check true)
      else (
        hist |> History.add_iteration ("UNFOLD", SimpleEntail { lhs; rhs });
        let verdict, terminate = unfold ctx lhs rhs in
        if verdict && terminate then
          check true
        else
          verdict)
    in
    (verdict, hist)
  in
  let ctx = Proofctx.make () in
  let () =
    let pre, _ = lhs in
    let post, _ = rhs in
    ctx |> Proofctx.add_precond pre;
    ctx |> Proofctx.add_postcond post
  in
  aux ctx None lhs rhs


let verify_entailment (Ast.Entail { lhs; rhs }) =
  let verdict, entriess =
    List.fold_left
      (fun (acc_verdict, acc_history) lhs ->
        if not acc_verdict then
          (false, acc_history)
        else
          let verdict, entries =
            List.fold_left
              (fun (acc2_verdict, acc2_history) rhs ->
                if acc2_verdict then
                  (true, acc2_history)
                else
                  let verdict, entry = verify_simple_entailment (Ast.SimpleEntail { lhs; rhs }) in
                  (verdict, entry :: acc2_history))
              (false, []) rhs
          in
          (verdict, List.rev entries :: acc_history))
      (true, []) lhs
  in
  (verdict, History.from_entries (List.rev entriess))


let verify_specification (Ast.Spec (entailment, assertion)) =
  let verdict, history = verify_entailment entailment in
  if verdict == assertion then
    (true, Colors.green ^ "Correct" ^ Colors.reset, history)
  else
    ( false,
      Printf.sprintf "%sIncorrect%s  got: %s%B%s  expect: %s%B%s" Colors.red Colors.reset
        Colors.blue verdict Colors.reset Colors.blue assertion Colors.reset,
      history )


let show_verification ~case ~no ~verdict ~verbose ~history =
  let no = string_of_int no in
  Colors.reset
  ^ Printf.sprintf "%s%-10s %s┃  %s\n" Colors.bold ("Case " ^ no) Colors.reset
      (Ast.show_specification case)
  ^ Printf.sprintf "%s\n" (History.show history ~verbose)
  ^ Printf.sprintf "%s%-10s %s┃  %s\n" Colors.bold "Verdict" Colors.reset verdict
