(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-library.machine: Explicit extension; no stock external-call bypass. *)
From Coq Require Import ZArith List String Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events
  Ctypes Ctypesdefs Clight.
Require Import Slice IO Machine Library ProcessEffects.
Import ListNotations.
Open Scope Z_scope.

Definition strcmp_definition : Clight.fundef := External
  (EF_external "strcmp" (mksignature [Xptr; Xptr] Xint cc_default))
  [tptr tschar; tptr tschar] tint cc_default.
Definition memcmp_definition : Clight.fundef := External
  (EF_external "memcmp" (mksignature [Xptr; Xptr; Xlong] Xint cc_default))
  [tptr tvoid; tptr tvoid; tulong] tint cc_default.
Definition memcpy_definition : Clight.fundef := External
  (EF_external "memcpy" (mksignature [Xptr; Xptr; Xlong] Xptr cc_default))
  [tptr tvoid; tptr tvoid; tulong] (tptr tvoid) cc_default.
Definition close_definition : Clight.fundef := External
  (EF_external "close" (mksignature [Xint] Xint cc_default)) [tint] tint cc_default.
Definition exit_definition : Clight.fundef := External
  (EF_external "_exit" (mksignature [Xint] Xvoid cc_default)) [tint] tvoid cc_default.

Definition comparison_args left right count :=
  [address_value left; address_value right; Vlong (Int64.repr count)].
Definition copy_args source destination (bytes : list Byte.int) :=
  [address_value destination; address_value source; Vlong (Int64.repr (Z.of_nat (length bytes)))].

Inductive library_ready cell : Clight.state -> Prop :=
| strcmp_ready : forall m left right k,
    strcmp_owned m left right ->
    library_ready cell (Callstate strcmp_definition [address_value left; address_value right] k m)
| memcmp_ready : forall m left right count k,
    memcmp_owned m left right count ->
    library_ready cell (Callstate memcmp_definition (comparison_args left right count) k m)
| memcpy_ready : forall m source destination bytes k,
    copy_owned m source destination bytes ->
    library_ready cell (Callstate memcpy_definition (copy_args source destination bytes) k m)
| close_ready : forall m fd k, tls_ready cell m ->
    library_ready cell (Callstate close_definition [Vint fd] k m)
| exit_ready : forall m code k, library_ready cell (Callstate exit_definition [Vint code] k m).

Inductive library_event :=
| original_event (ev : Machine.event)
| strcmp_returned (left right : address) (value : int)
| memcmp_returned (left right : address) (count : Z) (value : int)
| memcpy_returned (source destination : address) (bytes : list Byte.int)
| memcpy_lost (source destination : address) (bytes : list Byte.int) (schedule : list nat)
| close_returned (fd : int) (reply : close_reply)
| exit_requested (code : int)
| library_wait.

Inductive library_step ge cell : machine -> library_event -> machine -> Prop :=
| original_step : forall s ev target,
    Machine.step ge cell s ev target -> library_step ge cell s (original_event ev) target
| strcmp_step : forall m left right k value,
    strcmp_result m left right value ->
    library_step ge cell
      (live (Callstate strcmp_definition [address_value left; address_value right] k m))
      (strcmp_returned left right value) (live (Returnstate (Vint value) k m))
| memcmp_step : forall m left right count k value,
    memcmp_result m left right count value ->
    library_step ge cell (live (Callstate memcmp_definition (comparison_args left right count) k m))
      (memcmp_returned left right count value) (live (Returnstate (Vint value) k m))
| memcpy_step : forall m source destination bytes k after,
    copy_result m source destination bytes after ->
    library_step ge cell (live (Callstate memcpy_definition (copy_args source destination bytes) k m))
      (memcpy_returned source destination bytes)
      (live (Returnstate (address_value destination) k after))
| memcpy_loss_step : forall m source destination bytes k schedule after,
    copy_owned m source destination bytes -> partial_copy destination bytes m schedule after ->
    library_step ge cell (live (Callstate memcpy_definition (copy_args source destination bytes) k m))
      (memcpy_lost source destination bytes schedule) (dead after)
| close_step : forall m fd reply k after,
    close_effect cell m reply after ->
    library_step ge cell (live (Callstate close_definition [Vint fd] k m))
      (close_returned fd reply) (live (Returnstate (Vint (close_value reply)) k after))
| exit_step : forall m code k,
    library_step ge cell (live (Callstate exit_definition [Vint code] k m))
      (exit_requested code) (dead m)
| library_wait_step : forall s,
    library_ready cell s -> library_step ge cell (live s) library_wait (live s).

Inductive library_steps ge cell : machine -> list library_event -> machine -> Prop :=
| library_steps_nil : forall s, library_steps ge cell s [] s
| library_steps_cons : forall s ev mid rest last,
    library_step ge cell s ev mid -> library_steps ge cell mid rest last ->
    library_steps ge cell s (ev :: rest) last.

Theorem original_runs_preserved : forall ge cell s events target,
  Machine.steps ge cell s events target ->
  library_steps ge cell s (map original_event events) target.
Proof.
  intros ge cell s events target RUN; induction RUN; cbn; [constructor|].
  econstructor; [constructor; exact H|exact IHRUN].
Qed.

Theorem original_event_exact : forall ge cell s ev target,
  library_step ge cell s (original_event ev) target <-> Machine.step ge cell s ev target.
Proof. split; intros; [inversion H; subst; assumption|constructor; assumption]. Qed.

Theorem library_ready_is_external : forall cell s,
  library_ready cell s -> ~ internal_state s.
Proof. intros cell s READY; inversion READY; cbn; tauto. Qed.

Theorem internal_boundary_unchanged : forall ge cell s ev target,
  internal_state s -> library_step ge cell (live s) ev target ->
  exists original, ev = original_event original /\ Machine.step ge cell (live s) original target.
Proof.
  intros ge cell s ev target IN STEP; inversion STEP; subst; cbn in IN; try contradiction; eauto.
  exfalso; eapply library_ready_is_external; eassumption.
Qed.

Theorem no_library_builtin_bypass : forall ge cell f opt ef types args k e le m ev target,
  library_step ge cell (live (State f (Sbuiltin opt ef types args) k e le m)) ev target ->
  ev = original_event loss_step /\ target = dead m.
Proof.
  intros ge cell f opt ef types args k e le m ev target STEP; inversion STEP; subst.
  - match goal with H : Machine.step _ _ _ _ _ |- _ => inversion H; subst; cbn in * end;
      try contradiction; auto; match goal with H : boundary _ _ _ |- _ => inversion H end.
  - match goal with H : library_ready _ _ |- _ => inversion H end.
Qed.

Theorem library_dead_cannot_resume : forall ge cell m ev target,
  ~ library_step ge cell (dead m) ev target.
Proof.
  intros ge cell m ev target STEP; inversion STEP; subst.
  eapply dead_cannot_resume; eassumption.
Qed.

Theorem library_loss_everywhere : forall ge cell s,
  library_step ge cell (live s) (original_event loss_step) (dead (memory_of s)).
Proof. intros; constructor; constructor. Qed.

Definition library_ordinary ev :=
  match ev with
  | original_event _ | library_wait | memcpy_lost _ _ _ _ => False
  | _ => True
  end.

Theorem library_ready_progress : forall ge cell s,
  library_ready cell s ->
  exists ev target, library_ordinary ev /\ library_step ge cell (live s) ev target.
Proof.
  intros ge cell s READY; inversion READY; subst.
  - destruct (strcmp_progress _ _ _ H) as [value RESULT].
    eexists; eexists; split; [|apply strcmp_step; exact RESULT]; exact I.
  - destruct (memcmp_progress _ _ _ _ H) as [value RESULT].
    eexists; eexists; split; [|apply memcmp_step; exact RESULT]; exact I.
  - destruct (copy_progress _ _ _ _ H) as [after RESULT].
    eexists; eexists; split; [|apply memcpy_step; exact RESULT]; exact I.
  - destruct (close_progress _ _ (close_ok None) H) as [after RESULT].
    eexists; eexists; split; [|apply close_step; exact RESULT]; exact I.
  - eexists; eexists; split; [|apply exit_step]; exact I.
Qed.

Theorem library_arbitrary_wait_then_loss : forall ge cell s n,
  library_ready cell s ->
  library_steps ge cell (live s) (repeat library_wait n ++ [original_event loss_step])
    (dead (memory_of s)).
Proof.
  intros ge cell s n READY; induction n; cbn.
  - econstructor; [apply library_loss_everywhere|constructor].
  - econstructor; [constructor; assumption|assumption].
Qed.

Theorem copy_loss_is_terminal : forall ge cell s source destination bytes schedule target,
  library_step ge cell s (memcpy_lost source destination bytes schedule) target ->
  exists after, target = dead after.
Proof. intros; inversion H; subst; eauto. Qed.

Theorem exit_never_returns : forall ge cell m code k ev target,
  library_step ge cell (live (Callstate exit_definition [Vint code] k m)) ev target ->
  (ev = library_wait /\ target = live (Callstate exit_definition [Vint code] k m)) \/
  (ev = exit_requested code /\ target = dead m) \/
  (ev = original_event loss_step /\ target = dead m).
Proof.
  intros ge cell m code k ev target STEP; inversion STEP; subst; try discriminate; auto.
  match goal with H : Machine.step _ _ _ _ _ |- _ => inversion H; subst; cbn in * end;
    try contradiction; auto;
    match goal with H : boundary _ _ _ |- _ => inversion H; subst; destruct (operation q); discriminate end.
Qed.

Theorem source_strcmp_signature : source_definition _strcmp = Some (_strcmp, Gfun strcmp_definition).
Proof. reflexivity. Qed.
Theorem source_memcmp_signature : source_definition _memcmp = Some (_memcmp, Gfun memcmp_definition).
Proof. reflexivity. Qed.
Theorem source_memcpy_signature : source_definition _memcpy = Some (_memcpy, Gfun memcpy_definition).
Proof. reflexivity. Qed.
Theorem source_close_signature : source_definition _close = Some (_close, Gfun close_definition).
Proof. reflexivity. Qed.
Theorem source_exit_signature : source_definition __exit = Some (__exit, Gfun exit_definition).
Proof. reflexivity. Qed.

Lemma strcmp_original_step : forall ge cell left right k m ev target,
  Machine.step ge cell
    (live (Callstate strcmp_definition [address_value left; address_value right] k m)) ev target ->
  ev = loss_step /\ target = dead m.
Proof.
  intros ge cell left right k m ev target STEP. inversion STEP; subst; cbn in *;
    try contradiction; auto;
    match goal with H : boundary _ _ _ |- _ => inversion H; subst; destruct (operation q); discriminate end.
Qed.

Theorem strcmp_boundary_cases : forall ge cell left right xs ys k m ev target,
  c_string m left xs -> c_string m right ys ->
  library_step ge cell
    (live (Callstate strcmp_definition [address_value left; address_value right] k m)) ev target ->
  (exists value, strcmp_result m left right value /\
    ev = strcmp_returned left right value /\ target = live (Returnstate (Vint value) k m)) \/
  (ev = library_wait /\ target = live (Callstate strcmp_definition [address_value left; address_value right] k m)) \/
  (ev = original_event loss_step /\ target = dead m).
Proof.
  intros ge cell left right xs ys k m ev target LEFT RIGHT STEP.
  inversion STEP; subst; try discriminate; auto.
  - destruct (strcmp_original_step _ _ _ _ _ _ _ _ H) as [EV TARGET]; subst; auto.
  - left. exists value.
    destruct H7 as [a [b [A [B RESULT]]]].
    assert (L : left0 = left).
    { eapply readable_address_components; [exact (proj2 A)|exact (proj2 LEFT)|exact H|exact H1]. }
    assert (R : right0 = right).
    { eapply readable_address_components; [exact (proj2 B)|exact (proj2 RIGHT)|exact H2|exact H3]. }
    subst. split; [exists a, b; auto|auto].
Qed.
