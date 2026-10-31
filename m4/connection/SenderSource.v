(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.encoding: Actual sender entry, by-value parameter and zero initialization body. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Slice Machine ClightSteps WriteAll StoreSteps LocalAccess CallAccess ResultLayout
  FrameRecord FrameCopy.
Import ListNotations.
Open Scope Z_scope.
Definition sender_env result_local bytes_local :=
  PTree.set _bytes (bytes_local,tarray tuchar 160)
    (PTree.set _result__1 (result_local,result_type) empty_env).
Definition sender_temps fd sequence input ofs :=
  PTree.set _result__1 (Vptr input (Ptrofs.repr ofs))
    (PTree.set _sequence (Vlong sequence)
      (PTree.set _fd (Vint fd) (create_undef_temps (fn_temps f_send_frame)))).
Definition sender_initial fd sequence input ofs k m :=
  Callstate (Internal f_send_frame) [Vint fd;Vlong sequence;Vptr input (Ptrofs.repr ofs)] k m.
Definition sender_copy_statement := match fn_body f_send_frame with Ssequence s _ => s|_=>Sskip end.
Definition sender_zero_tail := match fn_body f_send_frame with Ssequence _ s=>s|_=>Sskip end.
Fixpoint statement_drop n s := match n with
  | O=>s|S rest=>match s with Ssequence _ tail=>statement_drop rest tail|_=>Sskip end end.
Definition sender_after_zero := statement_drop 160 sender_zero_tail.
Definition sender_zero_store index := Sassign
  (Ederef (Ebinop Oadd (Evar _bytes (tarray tuchar 160))
    (Econst_int (Int.repr (Z.of_nat index)) tint) (tptr tuchar)) tuchar)
  (Econst_int Int.zero tint).
Fixpoint sender_zero_sequence index count tail := match count with
  |O=>tail|S rest=>Ssequence (sender_zero_store index) (sender_zero_sequence (S index) rest tail) end.
Theorem sender_body_parts : fn_body f_send_frame=
  Ssequence sender_copy_statement (sender_zero_sequence 0 160 sender_after_zero).
Proof. reflexivity. Qed.
Theorem sender_source_entry : forall base first result_local allocated bytes_local fd sequence input ofs k,
  Mem.alloc base 0 144=(first,result_local) -> Mem.alloc first 0 160=(allocated,bytes_local) ->
  store_edge result_ge (sender_initial fd sequence input ofs k base)
    (State f_send_frame (fn_body f_send_frame) k (sender_env result_local bytes_local)
      (sender_temps fd sequence input ofs) allocated).
Proof.
  intros. apply function_entry_source_edge;constructor.
  - repeat (apply list_norepet_cons;[simpl;intuition discriminate|]);apply list_norepet_nil.
  - repeat (apply list_norepet_cons;[simpl;intuition discriminate|]);apply list_norepet_nil.
  - unfold list_disjoint,var_names;cbn. intros a b A B.
    destruct A as [A|[A|[A|A]]];repeat match goal with H : _ \/ _ |- _=>destruct H end;
      try contradiction;subst;discriminate.
  - econstructor;[exact H|]. econstructor;[exact H0|constructor].
  - reflexivity.
Qed.
Lemma sender_parameter_copy_edge : forall allocated copied result_local bytes_local fd sequence input ofs k,
  assign_loc result_ge result_type allocated result_local Ptrofs.zero Full (Vptr input (Ptrofs.repr ofs)) copied ->
  store_edge result_ge
    (State f_send_frame sender_copy_statement k (sender_env result_local bytes_local)
      (sender_temps fd sequence input ofs) allocated)
    (State f_send_frame Sskip k (sender_env result_local bytes_local)
      (sender_temps fd sequence input ofs) copied).
Proof.
  intros. unfold sender_copy_statement;cbn [fn_body]. eapply assignment_source_edge.
  - eapply local_location_value;unfold sender_env;WriteAll.lookup.
  - apply old_expression_value;unfold sender_temps;WriteAll.expression.
  - reflexivity.
  - exact H.
Qed.
