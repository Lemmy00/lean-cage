(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.reads: Actual read-loop endpoints retain bytes, input controls and stop reasons. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Clight.
Require Import Slice IO Machine ClightSteps StoreSteps WriteAll Deterministic ResultLayout
  LibraryMachine LibraryControl ProcessEffects ReceiverSource ReceiverReadSource
  ReceiverReadMemory ReceiverReadControl.
Import ListNotations.
Open Scope Z_scope.

Inductive receiver_stop := receive_full | receive_eof | receive_error (error : int).
Definition receiver_stop_valid reason (bytes : list Byte.int) := match reason with
  |receive_full=>length bytes=9%nat
  |receive_eof=>(length bytes<9)%nat
  |receive_error error=>(length bytes<9)%nat /\ error<>Int.repr 4
  end.
Definition receiver_bad initial reason := match reason with receive_error _=>Int.one|_=>initial end.
Definition receiver_registers original bad (bytes : list Byte.int) le :=
  receiver_kept original le /\ le!_bad=Some(Vint bad) /\
  le!_used=Some(Vlong(Int64.repr(Z.of_nat(length bytes)))).

Inductive receiver_endpoint cell b fd original bad k (P : mem -> Prop) bytes : Clight.state -> Prop :=
| receiver_ready : forall le m,
    (length bytes<9)%nat -> P m -> receiver_buffer cell b m bytes ->
    receiver_registers original bad bytes le ->
    receiver_endpoint cell b fd original bad k P bytes
      (receiver_read_state b cell fd (Z.of_nat(length bytes)) le k m)
| receiver_errno : forall le m error,
    (length bytes<9)%nat -> P m -> receiver_buffer cell b m bytes ->
    receiver_registers original bad bytes le -> le!_n=Some(Vlong Int64.mone) ->
    Mem.load Mint32 m (tls_block cell)(tls_offset cell)=Some(Vint error) ->
    receiver_endpoint cell b fd original bad k P bytes (receiver_errno_state b le k m)
| receiver_stopped : forall le m reason,
    receiver_stop_valid reason bytes -> P m -> receiver_buffer cell b m bytes ->
    receiver_registers original (receiver_bad bad reason) bytes le ->
    receiver_endpoint cell b fd original bad k P bytes (receiver_closed_state b le k m).

Definition receiver_routed cell b fd original bad k P bytes s :=
  exists last,path result_ge s last /\ receiver_endpoint cell b fd original bad k P bytes last.

Lemma receiver_kept_trans : forall a b c,
  receiver_kept a b -> receiver_kept b c -> receiver_kept a c.
Proof. intros a b c AB BC id IN;rewrite(BC _ IN);apply AB;exact IN. Qed.

Lemma receiver_endpoint_facts : forall cell b fd original bad k P bytes s,
  receiver_endpoint cell b fd original bad k P bytes s ->
  P(memory_of s) /\ receiver_buffer cell b (memory_of s) bytes.
Proof. intros;inversion H;subst;split;assumption. Qed.
Lemma receiver_routed_facts : forall cell b fd original bad k P bytes s,
  receiver_routed cell b fd original bad k P bytes s ->
  P(memory_of s) /\ receiver_buffer cell b (memory_of s) bytes.
Proof.
  intros cell b fd original bad k P bytes s [last [PATH END]].
  pose proof(path_memory _ _ _ PATH)as EQ;rewrite <-EQ;apply(receiver_endpoint_facts _ _ _ _ _ _ _ _ _ END).
Qed.
Lemma receiver_routed_prepend : forall cell b fd original bad k P bytes a c,
  path result_ge a c -> receiver_routed cell b fd original bad k P bytes c ->
  receiver_routed cell b fd original bad k P bytes a.
Proof.
  intros cell b fd original bad k P bytes a c AC [last [CL END]].
  exists last;split;[eapply path_trans;eassumption|exact END].
Qed.

Theorem receiver_loop_routed : forall cell b fd original bad k P bytes le m,
  P m -> Mem.load Mint32 m (rb_pipe b) 0=Some(Vint fd) ->
  receiver_buffer cell b m bytes -> receiver_registers original bad bytes le ->
  receiver_routed cell b fd original bad k P bytes (receiver_loop_state b le k m).
Proof.
  intros cell b fd original bad k P bytes le m PM FD BUFFER [KEPT [BAD USED]].
  pose proof BUFFER as [LIMIT _]. destruct(Nat.eq_dec(length bytes)9)as[FULL|SHORT].
  - exists(receiver_closed_state b le k m);split.
    + destruct(receiver_full_to_close b le k m)as[count PATH];[rewrite FULL in USED;exact USED|].
      eapply constant_store_path;exact PATH.
    + eapply receiver_stopped with(reason:=receive_full);[exact FULL|exact PM|exact BUFFER|].
      split;[exact KEPT|]. split;assumption.
  - assert(LT : (length bytes<9)%nat)by lia.
    exists(receiver_read_state b cell fd (Z.of_nat(length bytes))(PTree.set _t'27(Vint fd)le)k m);split.
    + destruct(receiver_loop_to_read b cell fd (Z.of_nat(length bytes))le k m USED FD ltac:(lia))as[count PATH].
      eapply constant_store_path;exact PATH.
    + apply receiver_ready;[exact LT|exact PM|exact BUFFER|].
      split.
      * intros id IN;rewrite PTree.gso;[apply KEPT;exact IN|].
        cbn in IN;repeat destruct IN as[IN|IN];try contradiction;subst id;discriminate.
      * split;WriteAll.lookup.
Qed.
