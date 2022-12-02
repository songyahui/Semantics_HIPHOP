open Pretty
open Printf
exception Foo of string


let files = [



  "1_abcro.hh";

  "2_abort-par-implicit-seq.hh";

  "4_abort-present.hh";

  "5_abortpre.hh";

  "6_abro-without-loopeach.hh";

  "7_abro.hh";

  
  "9_atom-exprs.hh";
  "10_atom.hh";





  "11_authenticate.hh";
  "12_await-count-pre.hh";
  "13_await-count.hh";
  "14_await-count2.hh";
  "15_await-immediate.hh";
  "16_await-par.hh";
  "17_await-seq-implicit-seq.hh";
  "18_await-seq.hh";
  "19_await-valued.hh";
  "20_await-valued2.hh";
  (*
  "21_button-implicit-seq.hh";
  "22_button.hh";
  *)
  "23_cross-await.hh";
  "24_countfunc-countargs.hh";
  "25_causality.hh";
  "26_causality-error.hh";
  "27_deep-trap.hh";
  "28_emit-if1.hh";
  "29_emit-if2.hh";
  "30_emit-multiple.hh";
  "31_emiterror.hh";
  "32_emitnovalue.hh";
  "33_emitvaluedlocal1.hh";
  "34_emitvaluedlocal2.hh";
  "35_every-delay.hh";
  "36_every-immediate.hh";
  "37_every1.hh";
  "38_example-loop-pause-emit.hh";
  "39_example-parallel.hh";
  "40_example-parallel2.hh";
  "41_example1.hh";
  "42_example2.hh";
  "43_example3.hh";
  "44_example4.hh";
  "45_exec-module-react.hh";
  "46_exec-module.hh";
  "47_exec-no-sig.hh";
  "48_exec-reincar.hh";
  "49_exec.hh";
  "50_exec2.hh";
  "51_exec3.hh";
  "52_Constructiveness.hh";
  "53_loop.hh";
  "54_Interference.hh";
  "55_abort.hh";
  "56_suspend.hh";
  "57_abort_loop.hh";
  "58_abort_present.hh";
  "59_loop.hh";
  "60_loop1.hh";
  "61_loop2.hh";

  "0_test.hh";
  "3_abort-par.hh";

  "8_atom-dep-par.hh";
]




let () =
  try

    let msg = List.fold_left (fun acc fileName ->
        let path = Sys.getcwd () ^ "/" ^ Sys.argv.(1)^fileName in 
    
        let ic = open_in path in
        let lines =  (input_lines ic ) in
        let line = List.fold_right (fun x acc -> acc ^ "\n" ^ x) (List.rev lines) "" in
        let _ = Parser.program Lexer.token (Lexing.from_string line) in
        close_in ic;                  (* 关闭输入通道 *)
        
        acc ^ line  ; 


  

     

    ) "" files in 

    let oc = open_out (Sys.getcwd () ^ "/src/microbenchmark/evaluation_tests/new_1_test.hh") in    (* 新建或修改文件,返回通道 *)
    fprintf oc "%s\n" msg;   (* 写一些东西 *)
    flush stdout;                (* 现在写入默认设备 *)


  with e ->                      (* 一些不可预见的异常发生 *)
  raise e                      (* 以出错的形式退出: 文件已关闭,但通道没有写入东西 *)

  

