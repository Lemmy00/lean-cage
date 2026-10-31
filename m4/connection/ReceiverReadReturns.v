(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.reads: Compose every read reply with its actual source continuation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Clight.
Require Import Slice IO Machine ClightSteps StoreSteps WriteAll ResultLayout ReceiverSource
  ReceiverReadSource ReceiverReadMemory ReceiverReadControl ReceiverRouting.
Import ListNotations.
Open Scope Z_scope.

Definition receiver_reads_preserve cell b fd (P : mem -> Prop) :=
  forall m bytes reply after,P m -> receiver_buffer cell b m bytes -> (length bytes<9)%nat ->
    io_return(receiver_request b cell fd(Z.of_nat(length bytes)))m reply after -> P after.
Definition receiver_descriptor b fd (P : mem -> Prop) :=
  forall m,P m -> Mem.load Mint32 m (rb_pipe b)0=Some(Vint fd).

Theorem receiver_return_routed : forall cell b fd original bad k P prefix le m reply after,
  receiver_reads_preserve cell b fd P -> receiver_descriptor b fd P ->
  (length prefix<9)%nat -> P m -> receiver_buffer cell b m prefix ->
  receiver_registers original bad prefix le ->
  io_return(receiver_request b cell fd(Z.of_nat(length prefix)))m reply after ->
  receiver_routed cell b fd original bad k P (prefix++receiver_reply_bytes reply)
    (Returnstate(Vlong(returned reply))(receiver_read_cont b le k)after).
Proof.
  intros cell b fd original bad k P prefix le m reply after PRESERVE DESCRIPTOR SHORT PM BUFFER
    [KEPT [BAD USED]] EFFECT.
  pose proof(PRESERVE _ _ _ _ PM BUFFER SHORT EFFECT)as PA.
  pose proof(receiver_buffer_reply _ _ _ _ _ _ _ BUFFER EFFECT)as BUFFER'.
  destruct reply as[bytes error|error|error].
  - assert(SIZE : 0<Z.of_nat(length bytes)<=9-Z.of_nat(length prefix)).
    { inversion EFFECT;subst;try discriminate;assumption. }
    destruct(receiver_positive_to_loop b le k after (Z.of_nat(length prefix))bytes error USED ltac:(lia)SIZE)
      as[count[next[KEEP'[BAD'[USED' PATH]]]]].
    eapply receiver_routed_prepend;[eapply constant_store_path;exact PATH|].
    eapply receiver_loop_routed;[exact PA|apply DESCRIPTOR;exact PA|exact BUFFER'|].
    split;[eapply receiver_kept_trans;eassumption|]. split;[rewrite BAD';exact BAD|].
    cbn [receiver_reply_bytes];rewrite app_length,Nat2Z.inj_add;exact USED'.
  - cbn [receiver_reply_bytes]in *;rewrite app_nil_r in BUFFER';rewrite app_nil_r.
    exists(receiver_errno_state b(receiver_saved le(failure error))k after);split.
    + destruct(receiver_read_to_errno b le k after error)as[count PATH];eapply constant_store_path;exact PATH.
    + eapply receiver_errno with(error:=error);[exact SHORT|exact PA|exact BUFFER'| | |].
      * destruct(receiver_saved_registers le(failure error))as[KEEP'[USED'[BAD' N']]].
        split;[eapply receiver_kept_trans;eassumption|]. split;[rewrite BAD';exact BAD|rewrite USED';exact USED].
      * exact(proj2(proj2(proj2(receiver_saved_registers le(failure error))))).
      * exact(failure_errno _ _ _ _ EFFECT).
  - cbn [receiver_reply_bytes]in *;rewrite app_nil_r in BUFFER';rewrite app_nil_r.
    destruct(receiver_zero_to_close b le k after (Z.of_nat(length prefix))error USED)
      as[count[next[KEEP'[BAD'[USED' PATH]]]]].
    exists(receiver_closed_state b next k after);split;[eapply constant_store_path;exact PATH|].
    eapply receiver_stopped with(reason:=receive_eof);[exact SHORT|exact PA|exact BUFFER'|].
    split;[eapply receiver_kept_trans;eassumption|]. split;[rewrite BAD';exact BAD|exact USED'].
Qed.

Theorem receiver_errno_return_routed : forall cell b fd original bad k P prefix le m error,
  receiver_descriptor b fd P -> (length prefix<9)%nat -> P m ->
  receiver_buffer cell b m prefix -> receiver_registers original bad prefix le ->
  le!_n=Some(Vlong Int64.mone) ->
  Mem.load Mint32 m (tls_block cell)(tls_offset cell)=Some(Vint error) ->
  receiver_routed cell b fd original bad k P prefix
    (Returnstate(Vptr(tls_block cell)(Ptrofs.repr(tls_offset cell)))(receiver_errno_cont b le k)m).
Proof.
  intros cell b fd original bad k P prefix le m error DESCRIPTOR SHORT PM BUFFER [KEPT[BAD USED]] N LOAD.
  assert(LOADV : Mem.loadv Mint32 m(Vptr(tls_block cell)(Ptrofs.repr(tls_offset cell)))=Some(Vint error)).
  { exact(errno_loadv (receiver_request b cell fd(Z.of_nat(length prefix)))m error
      (receiver_read_owned _ _ _ _ _ BUFFER SHORT)LOAD). }
  destruct(Int.eq_dec error(Int.repr 4))as[RETRY|FAILED].
  - subst error;destruct(receiver_errno_retry_to_loop b cell le k m (Z.of_nat(length prefix))USED N LOADV)
      as[count[next[KEEP'[BAD'[USED' PATH]]]]].
    eapply receiver_routed_prepend;[eapply constant_store_path;exact PATH|].
    eapply receiver_loop_routed;[exact PM|apply DESCRIPTOR;exact PM|exact BUFFER|].
    split;[eapply receiver_kept_trans;eassumption|]. split;[rewrite BAD';exact BAD|exact USED'].
  - destruct(receiver_errno_failure_to_close b cell le k m (Z.of_nat(length prefix))error USED N FAILED LOADV)
      as[count[next[KEEP'[BAD'[USED' PATH]]]]].
    exists(receiver_closed_state b next k m);split;[eapply constant_store_path;exact PATH|].
    eapply receiver_stopped with(reason:=receive_error error);[split;assumption|exact PM|exact BUFFER|].
    split;[eapply receiver_kept_trans;eassumption|]. split;[exact BAD'|exact USED'].
Qed.
