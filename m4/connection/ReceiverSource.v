(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.input: Actual terminal receiver locals, arguments and read-loop boundaries. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events
  Globalenvs Errors Ctypes Ctypesdefs Cop Clight.
Require Import Slice IO Machine ClightSteps StoreSteps WriteAll LocalAccess CallAccess
  ScalarMemory ResultLayout FreshMemory SenderSource.
Import ListNotations.
Open Scope Z_scope.

Record receiver_blocks := {
  rb_pipe : block; rb_result : block; rb_bytes : block;
  rb_unknown : block; rb_signal : block; rb_exit : block; rb_setup : block
}.
Definition receiver_env b :=
  PTree.set __res__4 (rb_setup b,result_type)
    (PTree.set __res__3 (rb_exit b,result_type)
      (PTree.set __res__2 (rb_signal b,result_type)
        (PTree.set __res__1 (rb_unknown b,result_type)
          (PTree.set _failure_bytes (rb_bytes b,tarray tuchar 9)
            (PTree.set _result__1 (rb_result b,result_type)
              (PTree.set _pipefd (rb_pipe b,tarray tint 1) empty_env)))))).
Definition receiver_args output ofs fd bad entered done status :=
  [Vptr output (Ptrofs.repr ofs);Vint fd;Vint bad;Vint entered;Vint done;Vint status].
Definition receiver_temps output ofs fd bad entered done status :=
  PTree.set _leader_status (Vint status) (PTree.set _leader_done (Vint done)
    (PTree.set _entered (Vint entered) (PTree.set _bad (Vint bad)
      (PTree.set _fd (Vint fd) (PTree.set __res (Vptr output (Ptrofs.repr ofs))
        (create_undef_temps (fn_temps f_m4_collect_failure))))))).
Definition receiver_initial output ofs fd bad entered done status k m :=
  Callstate (Internal f_m4_collect_failure)
    (receiver_args output ofs fd bad entered done status) k m.
Definition receiver_allocations base b allocated :=
  exists m1 m2 m3 m4 m5 m6,
    Mem.alloc base 0 4=(m1,rb_pipe b) /\
    Mem.alloc m1 0 144=(m2,rb_result b) /\
    Mem.alloc m2 0 9=(m3,rb_bytes b) /\
    Mem.alloc m3 0 144=(m4,rb_unknown b) /\
    Mem.alloc m4 0 144=(m5,rb_signal b) /\
    Mem.alloc m5 0 144=(m6,rb_exit b) /\
    Mem.alloc m6 0 144=(allocated,rb_setup b).

Theorem receiver_allocation_exists : forall base,exists b allocated,
  receiver_allocations base b allocated.
Proof.
  intros base.
  destruct (Mem.alloc base 0 4) as [m1 pipe] eqn:A1.
  destruct (Mem.alloc m1 0 144) as [m2 result] eqn:A2.
  destruct (Mem.alloc m2 0 9) as [m3 bytes] eqn:A3.
  destruct (Mem.alloc m3 0 144) as [m4 unknown] eqn:A4.
  destruct (Mem.alloc m4 0 144) as [m5 signal] eqn:A5.
  destruct (Mem.alloc m5 0 144) as [m6 exited] eqn:A6.
  destruct (Mem.alloc m6 0 144) as [allocated setup] eqn:A7.
  exists {|rb_pipe:=pipe;rb_result:=result;rb_bytes:=bytes;rb_unknown:=unknown;
    rb_signal:=signal;rb_exit:=exited;rb_setup:=setup|},allocated.
  exists m1,m2,m3,m4,m5,m6;cbn;repeat split;assumption.
Qed.

Theorem receiver_entry_source : forall base b allocated output ofs fd bad entered done status k,
  receiver_allocations base b allocated ->
  store_edge result_ge (receiver_initial output ofs fd bad entered done status k base)
    (State f_m4_collect_failure (fn_body f_m4_collect_failure) k (receiver_env b)
      (receiver_temps output ofs fd bad entered done status) allocated).
Proof.
  intros base b allocated output ofs fd bad entered done status k
    [m1 [m2 [m3 [m4 [m5 [m6 [A1 [A2 [A3 [A4 [A5 [A6 A7]]]]]]]]]]]].
  apply function_entry_source_edge;constructor.
  - repeat (apply list_norepet_cons;[simpl;intuition discriminate|]);apply list_norepet_nil.
  - repeat (apply list_norepet_cons;[simpl;intuition discriminate|]);apply list_norepet_nil.
  - unfold list_disjoint,var_names;cbn;intros a c A B;
      repeat match goal with H : _ \/ _ |- _=>destruct H end;
      try contradiction;subst;discriminate.
  - econstructor;[exact A1|]. econstructor;[exact A2|]. econstructor;[exact A3|].
    econstructor;[exact A4|]. econstructor;[exact A5|]. econstructor;[exact A6|].
    econstructor;[exact A7|]. constructor.
  - reflexivity.
Qed.

Definition first_statement s := match s with Ssequence first _=>first|_=>Sskip end.
Definition receiver_init_fd := first_statement (fn_body f_m4_collect_failure).
Definition receiver_init_used := first_statement (statement_drop 1 (fn_body f_m4_collect_failure)).
Definition receiver_loop := first_statement (statement_drop 2 (fn_body f_m4_collect_failure)).
Definition receiver_after_loop := statement_drop 3 (fn_body f_m4_collect_failure).
Definition receiver_close := first_statement receiver_after_loop.
Definition receiver_after_close := statement_drop 1 receiver_after_loop.
Definition receiver_classify := first_statement receiver_after_close.
Definition receiver_copy_return := statement_drop 1 receiver_after_close.
Definition receiver_loop_test := match receiver_loop with Sloop test _=>test|_=>Sskip end.
Definition receiver_loop_body := match receiver_loop_test with Ssequence _ body=>body|_=>Sskip end.
Definition receiver_loop_cont k := Kseq receiver_after_loop k.
Definition receiver_body_cont k := Kloop1 receiver_loop_test Sskip (receiver_loop_cont k).
Definition receiver_loop_state b le k m :=
  State f_m4_collect_failure receiver_loop (receiver_loop_cont k) (receiver_env b) le m.
Definition receiver_closed_state b le k m :=
  State f_m4_collect_failure receiver_after_loop k (receiver_env b) le m.

Theorem receiver_source_body : fn_body f_m4_collect_failure =
  Ssequence receiver_init_fd (Ssequence receiver_init_used
    (Ssequence receiver_loop (Ssequence receiver_close
      (Ssequence receiver_classify receiver_copy_return)))).
Proof. reflexivity. Qed.

Definition receiver_request b cell fd used :=
  {|operation:=reading;descriptor:=fd;buffer_block:=rb_bytes b;buffer_offset:=used;
    requested:=9-used;errno_block:=tls_block cell;errno_offset:=tls_offset cell|}.
Theorem receiver_request_remaining : forall b cell fd used,
  0<=used<9 -> 0<requested (receiver_request b cell fd used)<=9 /\
  buffer_offset (receiver_request b cell fd used)+requested (receiver_request b cell fd used)=9.
Proof. intros;change (0<9-used<=9 /\ used+(9-used)=9);lia. Qed.
