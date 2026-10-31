(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.input: Receiver entry requires ownership and stable globals, never a prepared execution. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata Globalenvs Clight.
Require Import Slice IO Machine ProcessEffects FreshMemory WriteEffects ResultLayout ResultSource ResultSafety
  ResultOwnership SenderReportMemory ReceiverSource ReceiverAllocation ReceiverPreparation
  ReceiverMemory ReceiverReadMemory ReceiverReadReturns.
Import ListNotations.
Open Scope Z_scope.
Definition receiver_input cell base output ofs run uid :=
  result_destination base output ofs /\ tls_ready cell base /\
  exists rb ub,Genv.find_symbol result_ge _run_id=Some rb /\
    Genv.find_symbol result_ge _run_uid=Some ub /\ result_globals base rb ub run uid /\
    rb<>tls_block cell /\ ub<>tls_block cell.
Definition receiver_live_memory cell base b output ofs fd m :=
  sender_preserved cell base m /\ receiver_slots_owned base b m /\
  result_destination m output ofs /\ Mem.load Mint32 m(rb_pipe b)0=Some(Vint fd).
Theorem receiver_live_result_input : forall cell base b output ofs fd run uid m,
  receiver_input cell base output ofs run uid -> receiver_live_memory cell base b output ofs fd m ->
  result_input m output ofs run uid.
Proof.
  intros cell base b output ofs fd run uid m [DEST[TLS[rb[ub[RS[US[[RUN UID][RN UN]]]]]]]]
    [OLD[SLOTS[DEST' FD]]];split;[exact DEST'|]. exists rb,ub;split;[exact RS|]. split;[exact US|]. split.
  - eapply Mem.load_unchanged_on;[exact OLD| |exact RUN]. intros pos RANGE;split.
    + eapply Mem.perm_valid_block;apply(proj1(Mem.load_valid_access _ _ _ _ _ RUN));exact RANGE.
    + left;exact RN.
  - eapply Mem.load_unchanged_on;[exact OLD| |exact UID]. intros pos RANGE;split.
    + eapply Mem.perm_valid_block;apply(proj1(Mem.load_valid_access _ _ _ _ _ UID));exact RANGE.
    + left;exact UN.
Qed.
Lemma io_old_permissions : forall q before reply after,
  io_return q before reply after -> old_permissions before after.
Proof.
  intros q before reply after EFFECT object pos pk permission PERM;inversion EFFECT;subst.
  all:match goal with ERR : errno_change _ _ _ _ |- _=>inversion ERR;subst end;
    eauto using Mem.perm_store_1,Mem.perm_storebytes_1.
Qed.
Lemma receiver_pipe_separate : forall base b m,
  receiver_slots_owned base b m -> rb_pipe b<>rb_bytes b.
Proof.
  intros base b m [DISTINCT OWN];unfold receiver_objects in DISTINCT;cbn in DISTINCT.
  inversion DISTINCT as[|? ? NOTIN REST];subst;cbn in NOTIN;intuition congruence.
Qed.
Lemma receiver_io_preserves_pipe : forall cell b fd used before reply after,
  rb_pipe b<>rb_bytes b -> rb_pipe b<>tls_block cell ->
  Mem.load Mint32 before(rb_pipe b)0=Some(Vint fd) ->
  io_return(receiver_request b cell fd used)before reply after ->
  Mem.load Mint32 after(rb_pipe b)0=Some(Vint fd).
Proof.
  intros cell b fd used before reply after NE NT LOAD EFFECT;inversion EFFECT;subst;try discriminate.
  all:match goal with ERR : errno_change _ _ _ _ |- _=>inversion ERR;subst end.
  all:try(erewrite Mem.load_store_other;[|eassumption|left;exact NT]).
  all:try exact LOAD.
  all:erewrite Mem.load_storebytes_other;[exact LOAD|eassumption|left;exact NE].
Qed.
Theorem receiver_live_read : forall cell base b output ofs fd,
  tls_ready cell base -> receiver_reads_preserve cell b fd(receiver_live_memory cell base b output ofs fd).
Proof.
  intros cell base b output ofs fd TLS m bytes reply after [OLD[SLOTS[DEST FD]]] BUFFER SHORT EFFECT.
  destruct(receiver_slot base b m (rb_bytes b)9 SLOTS ltac:(unfold receiver_objects;cbn;tauto))as[BFRESH BPERMS].
  assert(PFRESH : ~Mem.valid_block base(rb_pipe b)).
  { exact(proj1(receiver_slot base b m (rb_pipe b)4 SLOTS ltac:(unfold receiver_objects;cbn;tauto))). }
  split;[eapply receiver_io_old_preserved;[exact BFRESH|exact OLD|exact EFFECT]|].
  split;[eapply receiver_slots_permissions;[exact SLOTS|eapply io_old_permissions;exact EFFECT]|].
  split;[eapply receiver_destination_permissions;[exact DEST|eapply io_old_permissions;exact EFFECT]|].
  eapply receiver_io_preserves_pipe;[eapply receiver_pipe_separate;exact SLOTS|
    eapply fresh_tls_separate;[exact TLS|exact PFRESH]|exact FD|exact EFFECT].
Qed.
Theorem receiver_live_descriptor : forall cell base b output ofs fd,
  receiver_descriptor b fd(receiver_live_memory cell base b output ofs fd).
Proof. intros cell base b output ofs fd m [OLD[SLOTS[DEST FD]]];exact FD. Qed.
