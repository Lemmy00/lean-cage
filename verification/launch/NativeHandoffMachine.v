(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.effects: Exact fixed-ABI primitive extensions of the accepted source machine. *)
From Stdlib Require Import ZArith List String Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps ErrorNumber ProcessEffects LibraryMachine.
From EntryNative Require Import EntrySource.
From LeanCageMainNumber Require Import NumberMemory.
Import ListNotations.
Open Scope Z_scope.

Definition entry_decimal_definition : Clight.fundef := External
  (EF_external "entry_decimal" (mksignature [Xptr; Xlong] Xint cc_default))
  [tptr tschar; tulong] tint cc_default.

Definition entry_flags_definition : Clight.fundef := External
  (EF_external "entry_descriptor_flags" (mksignature [Xint; Xint] Xint cc_default))
  [tint; tint] tint cc_default.

Definition entry_exec_definition : Clight.fundef := External
  (EF_external "execve" (mksignature [Xptr; Xptr; Xptr] Xint cc_default))
  [tptr tschar; tptr (tptr tschar); tptr (tptr tschar)] tint cc_default.

Definition entry_outside cell output offset count block position :=
  (block <> output \/ position < offset \/ offset + count <= position) /\
  (block <> tls_block cell \/ position < tls_offset cell \/ tls_offset cell + 4 <= position).

Definition entry_format_owned (m : mem) output offset :=
  Ptrofs.unsigned offset + 32 <= Ptrofs.modulus /\
  Mem.range_perm m output (Ptrofs.unsigned offset) (Ptrofs.unsigned offset + 32) Cur Writable.

Definition entry_errno_ready cell m := exists error, initialized_errno cell m error.

Lemma entry_errno_ready_tls cell m : entry_errno_ready cell m -> tls_ready cell m.
Proof.
  intros [error [LOW [HIGH [ACCESS LOAD]]]]; unfold tls_ready.
  split; [exact LOW|]. split; [exact HIGH|exact ACCESS].
Qed.

(* Numeric meaning is deliberately absent.  The application must parse the
   actual produced bytes and compare the value before handing them to Lean. *)
Record entry_format_result cell before output offset returned after : Prop := {
  entry_format_frame : Mem.unchanged_on
    (entry_outside cell output (Ptrofs.unsigned offset) 32) before after;
  entry_format_permissions : forall block position kind permission,
    Mem.perm after block position kind permission <->
    Mem.perm before block position kind permission;
  entry_format_errno : entry_errno_ready cell after;
  entry_format_string : 0 < Int.signed returned < 32 ->
    exists bytes,
      Z.of_nat (length bytes) = Int.signed returned /\
      number_input after output offset bytes
}.

Definition entry_errno_frame cell before after :=
  Mem.unchanged_on (fun block position =>
    block <> tls_block cell \/ position < tls_offset cell \/ tls_offset cell + 4 <= position)
    before after.

Record entry_format_partial cell before output offset after : Prop := {
  entry_format_partial_frame : Mem.unchanged_on
    (entry_outside cell output (Ptrofs.unsigned offset) 32) before after;
  entry_format_partial_permissions : forall block position kind permission,
    Mem.perm after block position kind permission <->
    Mem.perm before block position kind permission
}.

Record entry_errno_partial cell before after : Prop := {
  entry_errno_partial_frame : entry_errno_frame cell before after;
  entry_errno_partial_permissions : forall block position kind permission,
    Mem.perm after block position kind permission <->
    Mem.perm before block position kind permission
}.

Inductive entry_handoff_event :=
| entry_library (event : library_event)
| entry_formatted (output : block) (offset : Ptrofs.int) (value : int64) (returned : int)
| entry_format_lost (output : block) (offset : Ptrofs.int) (value : int64)
| entry_flags_returned (descriptor flags returned : int)
| entry_flags_lost (descriptor flags : int)
| entry_exec_returned (path arguments environment : val) (returned : int)
| entry_exec_lost (path arguments environment : val)
| entry_image (path arguments environment : val)
| entry_primitive_wait.

Inductive entry_handoff_step ge cell : machine -> entry_handoff_event -> machine -> Prop :=
| entry_library_step : forall before event after,
    library_step ge cell before event after ->
    entry_handoff_step ge cell before (entry_library event) after
| entry_format_step : forall before output offset value k returned after,
    entry_format_owned before output offset ->
    entry_format_result cell before output offset returned after ->
    entry_handoff_step ge cell
      (live (Callstate entry_decimal_definition [Vptr output offset; Vlong value] k before))
      (entry_formatted output offset value returned)
      (live (Returnstate (Vint returned) k after))
| entry_format_loss_step : forall before output offset value k after,
    entry_format_owned before output offset ->
    entry_format_partial cell before output offset after ->
    entry_handoff_step ge cell
      (live (Callstate entry_decimal_definition [Vptr output offset; Vlong value] k before))
      (entry_format_lost output offset value) (dead after)
| entry_flags_step : forall before descriptor flags k returned after,
    entry_errno_frame cell before after ->
    entry_errno_ready cell after ->
    entry_handoff_step ge cell
      (live (Callstate entry_flags_definition [Vint descriptor; Vint flags] k before))
      (entry_flags_returned descriptor flags returned)
      (live (Returnstate (Vint returned) k after))
| entry_flags_loss_step : forall before descriptor flags k after,
    entry_errno_partial cell before after ->
    entry_handoff_step ge cell
      (live (Callstate entry_flags_definition [Vint descriptor; Vint flags] k before))
      (entry_flags_lost descriptor flags) (dead after)
| entry_exec_error_step : forall before path arguments environment k returned after,
    entry_errno_frame cell before after ->
    entry_errno_ready cell after ->
    entry_handoff_step ge cell
      (live (Callstate entry_exec_definition [path; arguments; environment] k before))
      (entry_exec_returned path arguments environment returned)
      (live (Returnstate (Vint returned) k after))
(* This is loss before image replacement.  A committed replacement uses entry_image,
   including when the new image subsequently dies before an observer receives a result. *)
| entry_exec_loss_step : forall before path arguments environment k after,
    entry_errno_partial cell before after ->
    entry_handoff_step ge cell
      (live (Callstate entry_exec_definition [path; arguments; environment] k before))
      (entry_exec_lost path arguments environment) (dead after)
| entry_exec_image_step : forall before path arguments environment k,
    entry_handoff_step ge cell
      (live (Callstate entry_exec_definition [path; arguments; environment] k before))
      (entry_image path arguments environment) (dead before)
| entry_format_wait : forall before output offset value k,
    entry_format_owned before output offset ->
    entry_handoff_step ge cell
      (live (Callstate entry_decimal_definition [Vptr output offset; Vlong value] k before))
      entry_primitive_wait
      (live (Callstate entry_decimal_definition [Vptr output offset; Vlong value] k before))
| entry_flags_wait : forall before descriptor flags k,
    entry_handoff_step ge cell
      (live (Callstate entry_flags_definition [Vint descriptor; Vint flags] k before))
      entry_primitive_wait
      (live (Callstate entry_flags_definition [Vint descriptor; Vint flags] k before))
| entry_exec_wait : forall before path arguments environment k,
    entry_handoff_step ge cell
      (live (Callstate entry_exec_definition [path; arguments; environment] k before))
      entry_primitive_wait
      (live (Callstate entry_exec_definition [path; arguments; environment] k before)).

Inductive entry_handoff_steps ge cell : machine -> list entry_handoff_event -> machine -> Prop :=
| entry_handoff_steps_nil : forall state, entry_handoff_steps ge cell state [] state
| entry_handoff_steps_cons : forall before event middle rest after,
    entry_handoff_step ge cell before event middle ->
    entry_handoff_steps ge cell middle rest after ->
    entry_handoff_steps ge cell before (event :: rest) after.

Theorem entry_original_steps_preserved ge cell before events after :
  Machine.steps ge cell before events after ->
  entry_handoff_steps ge cell before (map (fun event => entry_library (original_event event)) events) after.
Proof.
  intros RUN; induction RUN; cbn; [constructor|].
  econstructor; [apply entry_library_step; apply original_step; exact H|exact IHRUN].
Qed.

Theorem entry_handoff_loss_everywhere ge cell state :
  entry_handoff_step ge cell (live state) (entry_library (original_event loss_step)) (dead (memory_of state)).
Proof. apply entry_library_step; apply library_loss_everywhere. Qed.

Theorem entry_handoff_dead_cannot_resume ge cell m event after :
  ~ entry_handoff_step ge cell (dead m) event after.
Proof.
  intros STEP; inversion STEP; subst; eapply library_dead_cannot_resume; eassumption.
Qed.

Theorem entry_handoff_dead_steps ge cell m events after :
  entry_handoff_steps ge cell (dead m) events after -> events = [] /\ after = dead m.
Proof.
  intros RUN; inversion RUN; subst; auto.
  exfalso; eapply entry_handoff_dead_cannot_resume; eassumption.
Qed.

Theorem entry_internal_step_exact ge cell state event after :
  internal_state state ->
  entry_handoff_step ge cell (live state) event after ->
  exists original,
    event = entry_library (original_event original) /\
    Machine.step ge cell (live state) original after.
Proof.
  intros INTERNAL STEP; inversion STEP; subst; cbn in INTERNAL; try contradiction.
  destruct (internal_boundary_unchanged _ _ _ _ _ INTERNAL H)
    as [original [EVENT REAL]]; subst; eauto.
Qed.

Theorem entry_store_edge_cases ge cell state next event after :
  store_edge ge state next ->
  entry_handoff_step ge cell (live state) event after ->
  (event = entry_library (original_event (source_step E0)) /\ after = live next) \/
  (event = entry_library (original_event loss_step) /\ after = dead (memory_of state)).
Proof.
  intros EDGE STEP.
  destruct (entry_internal_step_exact _ _ _ _ _ (proj1 EDGE) STEP)
    as [original [EVENT REAL]]; subst.
  destruct (store_edge_cases _ _ _ _ _ _ EDGE REAL) as [[EVENT AFTER]|[EVENT AFTER]];
    subst; auto.
Qed.
