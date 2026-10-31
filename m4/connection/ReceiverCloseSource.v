(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.memory: The real close attempt discards both success and failure return values. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Slice Machine ClightSteps StoreSteps WriteAll LocalAccess CallAccess ResultLayout LibraryMachine
  SenderSource ReceiverSource ReceiverReadSource.
Import ListNotations.
Open Scope Z_scope.

Definition receiver_close_cont b le k :=
  Kcall None f_m4_collect_failure(receiver_env b)le(Kseq receiver_after_close k).
Theorem receiver_close_symbol : exists symbol,
  Genv.find_symbol result_ge _close=Some symbol /\
  Genv.find_funct result_ge(Vptr symbol Ptrofs.zero)=Some close_definition.
Proof. eexists;split;vm_compute;reflexivity. Qed.

Theorem receiver_to_close : forall b le k m fd,
  Mem.load Mint32 m(rb_pipe b)0=Some(Vint fd) ->
  exists count,store_path result_ge(fun after=>after=m)
    (receiver_closed_state b le k m)count
    (Callstate close_definition[Vint fd](receiver_close_cont b(PTree.set _t'25(Vint fd)le)k)m).
Proof.
  intros b le k m fd FD;destruct receiver_close_symbol as[symbol[SYM FUN]].
  eexists;unfold receiver_closed_state,receiver_after_loop,receiver_close_cont;cbn [statement_drop].
  receiver_route. receiver_route.
  eapply store_next;[reflexivity|eapply certified_set_edge|].
  - eapply location_read_value;[receiver_location|].
    apply deref_loc_value with(chunk:=Mint32);[reflexivity|exact FD].
  - receiver_route;eapply store_next;[reflexivity| |].
    + eapply certified_call_edge;[reflexivity|
        apply old_expression_value;eapply value_function;
          [unfold receiver_env;cbn;reflexivity|exact SYM|reflexivity]| |exact FUN|reflexivity].
      eapply cons_argument_values;[receiver_expression|reflexivity|apply no_argument_values].
    + apply store_done;reflexivity.
Qed.

Theorem receiver_close_ignored : forall b le k m value,
  store_path result_ge(fun after=>after=m)
    (Returnstate value(receiver_close_cont b le k)m)2
    (State f_m4_collect_failure receiver_after_close k(receiver_env b)le m).
Proof.
  intros;unfold receiver_close_cont;receiver_route;receiver_route;apply store_done;reflexivity.
Qed.

Lemma receiver_close_keeps : forall le fd,
  receiver_kept le(PTree.set _t'25(Vint fd)le) /\
  (PTree.set _t'25(Vint fd)le)!_bad=le!_bad /\
  (PTree.set _t'25(Vint fd)le)!_used=le!_used.
Proof. intros;split;[receiver_keep|]. split;WriteAll.lookup. Qed.
