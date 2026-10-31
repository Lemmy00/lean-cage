(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.reads: Retain every actual read, wait, errno and partial-loss transition. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Slice IO Machine ClightSteps StoreSteps WriteAll Deterministic LibraryMachine
  LibraryPreservation LibraryControl ResultLayout ReceiverSource ReceiverReadSource
  ReceiverReadMemory.
Import ListNotations.
Open Scope Z_scope.

Theorem constant_store_path : forall ge m s count last,
  store_path ge (fun after=>after=m) s count last -> path ge s last.
Proof.
  intros ge m s count last RUN;induction RUN;[constructor|].
  eapply path_next;[|exact IHRUN].
  destruct H0 as [IN [REAL UNIQUE]];split;[exact IN|]. split;[exact REAL|]. split;[|exact UNIQUE].
  pose proof (store_path_initial _ _ _ _ _ RUN);congruence.
Qed.

Definition read_call_state q k m :=
  Callstate (External (io_function reading) [tint;tptr tvoid;tulong] tlong cc_default)
    (request_args q) k m.
Theorem read_call_cases : forall ge q k m ev target,
  operation q=reading -> owned q m ->
  Machine.step ge (cell_of q) (live (read_call_state q k m)) ev target ->
  (exists reply after,io_return q m reply after /\
    ev=io_step q reply /\ target=live(Returnstate(Vlong(returned reply))k after)) \/
  (ev=wait_step /\ target=live(read_call_state q k m)) \/
  (ev=loss_step /\ target=dead m) \/
  (exists bytes error after,io_return q m (transfer bytes error) after /\
    ev=partial_loss q bytes error /\ target=dead after).
Proof.
  intros ge q k m ev target READ OWN STEP.
  inversion STEP;subst;try contradiction.
  2:right;left;auto.
  2:right;right;left;auto.
  all:assert (OP : operation q0=reading) by (destruct (operation q0);[reflexivity|discriminate]).
  all:assert (Q : q0=q).
  1,3:(
    match goal with B : boundary _ _ _ |- _=>inversion B;subst end;
    eapply request_injective;
      [match goal with E : io_return _ _ _ _ |- _=>inversion E;eassumption end|
       exact OWN|congruence|assumption|assumption|];
    change (Ptrofs.unsigned(Ptrofs.repr(buffer_offset q0))=Ptrofs.unsigned(Ptrofs.repr(buffer_offset q))) in H3;
    apply(f_equal Ptrofs.repr)in H3;repeat rewrite Ptrofs.repr_unsigned in H3;
    change (Int64.unsigned(Int64.repr(requested q0))=Int64.unsigned(Int64.repr(requested q))) in H4;
    apply(f_equal Int64.repr)in H4;repeat rewrite Int64.repr_unsigned in H4;
    unfold request_args;cbn;congruence).
  - subst q0;left;eauto 8.
  - subst q0;right;right;right;eauto 8.
Qed.

Theorem receiver_read_original : forall ge b cell fd used le k m ev target,
  library_step ge cell (live(receiver_read_state b cell fd used le k m)) ev target ->
  exists old,ev=original_event old /\
    Machine.step ge cell (live(receiver_read_state b cell fd used le k m)) old target.
Proof.
  intros;eapply original_boundary_exact;[right;left;exists reading;
    eexists;eexists;eexists;reflexivity|exact H].
Qed.

Theorem receiver_errno_cases : forall ge b cell le k m ev target,
  library_step ge cell (live(receiver_errno_state b le k m)) ev target ->
  (ev=original_event errno_step /\
    target=live(Returnstate(Vptr(tls_block cell)(Ptrofs.repr(tls_offset cell)))
      (receiver_errno_cont b le k)m)) \/
  (ev=original_event loss_step /\ target=dead m).
Proof.
  intros ge b cell le k m ev target STEP.
  assert (BOUND : original_boundary (receiver_errno_state b le k m)).
  { right;right;eexists;eexists;reflexivity. }
  destruct (original_boundary_exact _ _ _ _ _ BOUND STEP) as [old [EV ORIGINAL]].
  subst ev;inversion ORIGINAL;subst;cbn in *;try contradiction;auto;
    match goal with B : boundary _ _ _ |- _=>inversion B;subst;destruct(operation q);discriminate end.
Qed.

Theorem receiver_read_ordinary : forall ge b cell fd used le k m,
  owned (receiver_request b cell fd used) m ->
  exists ev target,control_progress ev /\
    library_step ge cell (live(receiver_read_state b cell fd used le k m)) ev target.
Proof.
  intros ge b cell fd used le k m OWN.
  exists (original_event(io_step(receiver_request b cell fd used)(zero None))),
    (live(Returnstate(Vlong Int64.zero)(receiver_read_cont b le k)m));split.
  - unfold control_progress;cbn;repeat split;discriminate.
  - apply original_step;eapply effect with(q:=receiver_request b cell fd used)(r:=zero None);
      [constructor;reflexivity|apply zero_return_exists;exact OWN].
Qed.

Theorem receiver_errno_ordinary : forall ge b cell le k m,
  ProcessEffects.tls_ready cell m ->
  exists ev target,control_progress ev /\
    library_step ge cell (live(receiver_errno_state b le k m)) ev target.
Proof.
  intros ge b cell le k m [LOW [HIGH ACCESS]].
  exists (original_event errno_step),
    (live(Returnstate(Vptr(tls_block cell)(Ptrofs.repr(tls_offset cell)))(receiver_errno_cont b le k)m));split.
  - unfold control_progress;cbn;repeat split;discriminate.
  - apply original_step;apply errno_address;assumption.
Qed.
