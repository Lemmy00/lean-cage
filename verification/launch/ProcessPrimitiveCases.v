(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.effects: Extra primitive names cannot use the accepted external-call semantics. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine IO LibraryMachine LibraryPreservation WriteAll.
From EntryNative Require Import NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessCalls.
Import ListNotations.
Open Scope Z_scope.

Lemma ptrace_entry_only_loss ge cell before request child address data k event target :
  entry_handoff_step ge cell
    (live (Callstate process_ptrace_definition [Vint request;Vint child;address;data] k before))
    event target ->
  event = entry_library (original_event loss_step) /\ target = dead before.
Proof.
  intro STEP; inversion STEP; subst; try discriminate.
  match goal with LIB : library_step _ _ _ _ _ |- _ => inversion LIB; subst; try discriminate end.
  - match goal with ORIGINAL : Machine.step _ _ _ _ _ |- _ =>
      inversion ORIGINAL; subst; cbn in *; try contradiction;
        try match goal with BOUND : boundary _ _ _ |- _ => inversion BOUND end
    end; auto.
  - match goal with READY : library_ready _ _ |- _ => inversion READY end.
Qed.

Lemma process_write_boundary_identifies cell q before k query :
  owned q before -> owned query before -> operation q = writing ->
  errno_block q = tls_block cell -> errno_offset q = tls_offset cell ->
  boundary cell (Callstate (External (io_function writing)
    [tint;tptr tvoid;tulong] tlong cc_default) (request_args q) k before) query ->
  query=q.
Proof.
  intros OWN OTHER WRITE BLOCK OFFSET BOUND;inversion BOUND;subst.
  assert (OP:operation query=writing) by (destruct(operation query);[discriminate|reflexivity]).
  eapply request_injective;[exact OTHER|exact OWN|congruence|congruence|congruence|].
  change (Ptrofs.unsigned(Ptrofs.repr(buffer_offset query))=
    Ptrofs.unsigned(Ptrofs.repr(buffer_offset q))) in H3.
  change (Int64.unsigned(Int64.repr(requested query))=
    Int64.unsigned(Int64.repr(requested q))) in H4.
  repeat match goal with
  | SAME:Ptrofs.unsigned ?a=Ptrofs.unsigned ?b |- _ =>
      apply (f_equal Ptrofs.repr) in SAME;repeat rewrite Ptrofs.repr_unsigned in SAME
  | SAME:Int64.unsigned ?a=Int64.unsigned ?b |- _ =>
      apply (f_equal Int64.repr) in SAME;repeat rewrite Int64.repr_unsigned in SAME
  end.
  unfold request_args;cbn;congruence.
Qed.

Theorem process_write_cases ge cell q before k event target :
  owned q before -> operation q=writing ->
  errno_block q=tls_block cell -> errno_offset q=tls_offset cell ->
  process_step ge cell (live (Callstate (External (io_function writing)
    [tint;tptr tvoid;tulong] tlong cc_default) (request_args q) k before)) event target ->
  (exists reply after, io_return q before reply after /\
    event=process_entry(entry_library(original_event(io_step q reply))) /\
    target=live(Returnstate(Vlong(returned reply))k after)) \/
  (event=process_entry(entry_library(original_event wait_step)) /\
    target=live(Callstate(External(io_function writing)
      [tint;tptr tvoid;tulong]tlong cc_default)(request_args q)k before)) \/
  (event=process_entry(entry_library(original_event loss_step)) /\target=dead before) \/
  (exists bytes error after,io_return q before(transfer bytes error)after /\
    event=process_entry(entry_library(original_event(partial_loss q bytes error))) /\target=dead after).
Proof.
  intros OWN WRITE BLOCK OFFSET STEP.
  assert(BOUND:original_boundary(Callstate(External(io_function writing)
    [tint;tptr tvoid;tulong]tlong cc_default)(request_args q)k before)).
  { right;left;do 4 eexists;reflexivity. }
  destruct(process_original_boundary_exact _ _ _ _ _ BOUND STEP)as[original[EVENT REAL]].
  subst event;inversion REAL;subst;try contradiction;auto 12.
  all:assert(OP:operation q0=writing)by(destruct(operation q0);[discriminate|reflexivity]).
  all:assert(SAME:q0=q)by(
    match goal with IOBOUND:boundary _ _ _|-_=>inversion IOBOUND;subst end;
    eapply request_injective;
    [match goal with EFFECT:io_return _ _ _ _|-_=>inversion EFFECT;eassumption end|
     exact OWN|congruence|congruence|congruence|];
    change(Ptrofs.unsigned(Ptrofs.repr(buffer_offset q0))=
      Ptrofs.unsigned(Ptrofs.repr(buffer_offset q)))in H3;
    apply(f_equal Ptrofs.repr)in H3;repeat rewrite Ptrofs.repr_unsigned in H3;
    change(Int64.unsigned(Int64.repr(requested q0))=
      Int64.unsigned(Int64.repr(requested q)))in H4;
    apply(f_equal Int64.repr)in H4;repeat rewrite Int64.repr_unsigned in H4;
    unfold request_args;cbn;congruence).
  all:subst q0;eauto 12.
Qed.

Theorem process_ptrace_cases ge cell before request child address data k event target :
  process_step ge cell
    (live (Callstate process_ptrace_definition [Vint request;Vint child;address;data] k before))
    event target ->
  (exists returned after, process_ptrace_frame cell request data before after /\
    entry_errno_ready cell after /\
    event = process_traced request child address data returned /\
    target = live (Returnstate (Vlong returned) k after)) \/
  (event = process_waiting /\ target = live
    (Callstate process_ptrace_definition [Vint request;Vint child;address;data] k before)) \/
  (event = process_entry (entry_library (original_event loss_step)) /\ target = dead before) \/
  (exists after, event = process_trace_lost request child address data /\
    process_ptrace_partial cell request data before after /\ target = dead after).
Proof.
  intro STEP; inversion STEP; subst; try discriminate; eauto 12.
  destruct (ptrace_entry_only_loss _ _ _ _ _ _ _ _ _ _ H) as [EVENT TARGET]; subst; auto.
Qed.

Lemma wait_entry_only_loss ge cell before requested status offset options k event target :
  entry_handoff_step ge cell
    (live (Callstate process_wait_definition [Vint requested;Vptr status offset;Vint options] k before))
    event target ->
  event = entry_library (original_event loss_step) /\ target = dead before.
Proof.
  intro STEP; inversion STEP; subst; try discriminate.
  match goal with LIB : library_step _ _ _ _ _ |- _ => inversion LIB; subst; try discriminate end.
  - match goal with ORIGINAL : Machine.step _ _ _ _ _ |- _ =>
      inversion ORIGINAL; subst; cbn in *; try contradiction;
        try match goal with BOUND : boundary _ _ _ |- _ => inversion BOUND end
    end; auto.
  - match goal with READY : library_ready _ _ |- _ => inversion READY end.
Qed.

Theorem process_wait_cases ge cell before requested status offset options k event target :
  process_step ge cell
    (live (Callstate process_wait_definition [Vint requested;Vptr status offset;Vint options] k before))
    event target ->
  (exists observation after, process_wait_effect cell status offset before observation after /\
    entry_errno_ready cell after /\
    event = process_waited requested status offset options observation /\
    target = live (Returnstate (Vint (wait_return observation)) k after)) \/
  (event = process_waiting /\ target = live
    (Callstate process_wait_definition [Vint requested;Vptr status offset;Vint options] k before)) \/
  (event = process_entry (entry_library (original_event loss_step)) /\ target = dead before) \/
  (exists after, event = process_wait_lost requested status offset options /\
    process_wait_partial cell status offset before after /\ target = dead after).
Proof.
  intro STEP; inversion STEP; subst; try discriminate; eauto 12.
  destruct (wait_entry_only_loss _ _ _ _ _ _ _ _ _ _ H) as [EVENT TARGET]; subst; auto.
Qed.

Theorem process_stopped_return_only_loss ge cell value before event target :
  process_step ge cell (live (Returnstate value Kstop before)) event target ->
  event = process_entry (entry_library (original_event loss_step)) /\ target = dead before.
Proof.
  intro STEP.
  assert (INTERNAL : internal_state (Returnstate value Kstop before)) by exact I.
  destruct (process_internal_step_exact _ _ _ _ _ INTERNAL STEP) as [original [EVENT REAL]].
  subst event; inversion REAL; subst; try contradiction;
    try match goal with SOURCE : step2 _ _ _ _ |- _ => inversion SOURCE end;
    try match goal with BOUND : boundary _ _ _ |- _ => inversion BOUND end; auto.
Qed.

Theorem process_return_statement_terminates ge cell fn expression k e le before event target :
  call_cont k = Kstop ->
  process_step ge cell (live (State fn (Sreturn (Some expression)) k e le before)) event target ->
  (event = process_entry (entry_library (original_event (source_step E0))) /\
    exists value after, target = live (Returnstate value Kstop after)) \/
  (event = process_entry (entry_library (original_event loss_step)) /\ target = dead before).
Proof.
  intros CLOSED STEP.
  assert (INTERNAL : internal_state (State fn (Sreturn (Some expression)) k e le before)) by exact I.
  destruct (process_internal_step_exact _ _ _ _ _ INTERNAL STEP) as [original [EVENT REAL]].
  subst event; inversion REAL; subst; try contradiction;
    try match goal with BOUND : boundary _ _ _ |- _ => inversion BOUND end; auto.
  match goal with SOURCE : step2 _ _ _ _ |- _ => inversion SOURCE;subst end.
  all: try solve [match goal with IMPOSSIBLE : _ = _ \/ _ = _ |- _ =>
    destruct IMPOSSIBLE; discriminate end].
  left; split; [reflexivity|]. rewrite CLOSED; eauto.
Qed.
