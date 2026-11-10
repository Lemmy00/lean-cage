(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Physical source resumption has a process/image
   incarnation; symbolic C control alone does not assert liveness. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Ctypes Clight.
From HostGateway Require Import GatewayMachine GatewaySpawnHistory.
Import ListNotations.

Record gateway_source_activation := {
  gateway_activation_process : nat;
  gateway_activation_image : nat;
  (* This incarnation changes on exec even when the same image is selected. *)
  gateway_activation_incarnation : nat
}.

(* The physical ABI samples the current process/image incarnation and code
   mapping, independently of the symbolic Clight memory. *)
Record gateway_activation_snapshot := {
  gateway_snapshot_process : nat;
  gateway_snapshot_image : nat;
  gateway_snapshot_incarnation : nat;
  gateway_snapshot_running : bool;
  gateway_snapshot_code_mapped : bool
}.

Definition gateway_activation_matches snapshot activation : Prop :=
  gateway_snapshot_process snapshot = gateway_activation_process activation /\
  gateway_snapshot_image snapshot = gateway_activation_image activation /\
  gateway_snapshot_incarnation snapshot = gateway_activation_incarnation activation /\
  gateway_snapshot_running snapshot = true /\ gateway_snapshot_code_mapped snapshot = true.

Definition gateway_snapshot_active {World}
    (view : World -> nat -> option gateway_activation_snapshot)
    (world : World) (activation : gateway_source_activation) : Prop :=
  exists snapshot, view world (gateway_activation_process activation) = Some snapshot /\
    gateway_activation_matches snapshot activation.

Definition gateway_source_resumes {Event} (event : gateway_event Event) : Prop :=
  match event with gateway_source _ | gateway_primitive _ => True | _ => False end.

(* Active/ended are kernel process+mapping observations for the SAME code
   activation. An ended activation may retain historical logical C memory;
   this says nothing about teardown completion, queue release or reaping. *)
Record gateway_activation_runtime {World Event} (backend : gateway_backend World Event)
    (active ended : World -> gateway_source_activation -> Prop) : Prop := {
  gateway_activation_distinct : forall world activation, ended world activation -> ~ active world activation;
  gateway_activation_ambient_end : forall before world after next activation,
    gateway_interference backend before world after next -> ended world activation -> ended next activation;
  gateway_activation_external_end : forall ef types result_type convention arguments before world result after next event activation,
    gateway_external backend ef types result_type convention arguments before world result after next event ->
    ended world activation -> ended next activation;
  gateway_activation_builtin_end : forall ef types arguments before world result after next event activation,
    gateway_builtin backend ef types arguments before world result after next event ->
    ended world activation -> ended next activation
}.

(* This is the observed source-resumption boundary of ONE actual transition,
   beside its unmodified broad GatewayMachine transition. It is deliberately
   absent for committed loss: the same external effect can end the activation. *)
Inductive gateway_activation_step {World Event} (backend : gateway_backend World Event) ge
    (active : World -> gateway_source_activation -> Prop) (activation : gateway_source_activation) :
    gateway_state World -> gateway_event Event -> gateway_state World -> Prop :=
| gateway_activation_observed : forall first event last,
    gateway_step backend ge first event last ->
    (gateway_source_resumes event ->
      active (gateway_state_world first) activation /\ active (gateway_state_world last) activation) ->
    gateway_activation_step backend ge active activation first event last.

Inductive gateway_activation_steps {World Event} (backend : gateway_backend World Event) ge
    (active : World -> gateway_source_activation -> Prop) (activation : gateway_source_activation) :
    gateway_state World -> list (gateway_event Event) -> gateway_state World -> Prop :=
| gateway_activation_nil : forall source,
    gateway_activation_steps backend ge active activation source [] source
| gateway_activation_cons : forall first observed middle rest last,
    gateway_activation_step backend ge active activation first observed middle ->
    gateway_activation_steps backend ge active activation middle rest last ->
    gateway_activation_steps backend ge active activation first (observed :: rest) last.

Theorem gateway_activation_trace_erase {World Event} (backend : gateway_backend World Event) ge
    active activation first events last :
  gateway_activation_steps backend ge active activation first events last -> gateway_steps backend ge first events last.
Proof.
  intro RUN; induction RUN; [constructor |].
  inversion H; subst; econstructor; eassumption.
Qed.

Theorem gateway_activation_step_ended {World Event} (backend : gateway_backend World Event) ge
    active ended (runtime : gateway_activation_runtime backend active ended)
    activation first observed last :
  gateway_step backend ge first observed last -> ended (gateway_state_world first) activation ->
  ended (gateway_state_world last) activation.
Proof.
  intros STEP ENDED; inversion STEP; subst; cbn [gateway_state_world] in *; try exact ENDED.
  - eapply gateway_activation_external_end; eassumption.
  - eapply gateway_activation_builtin_end; eassumption.
  - eapply gateway_activation_ambient_end; eassumption.
  - eapply gateway_activation_external_end; eassumption.
  - eapply gateway_activation_builtin_end; eassumption.
Qed.

(* A real old-image source/SDK resumption is impossible after exec/exit. The
   run may still record actual ambient progress, pending committed loss or
   its terminal lost marker; no cleanup/reap outcome is strengthened. *)
Theorem gateway_ended_activation_no_resume {World Event} (backend : gateway_backend World Event) ge
    active ended (runtime : gateway_activation_runtime backend active ended)
    activation first events last :
  gateway_activation_steps backend ge active activation first events last ->
  ended (gateway_state_world first) activation -> Forall (fun event => ~ gateway_source_resumes event) events.
Proof.
  intro RUN; induction RUN; intro ENDED; [constructor |].
  inversion H as [before event after STEP RESUMED]; subst.
  constructor.
  - intro RESUME; destruct (RESUMED RESUME) as [ACTIVE AFTER].
    exact (gateway_activation_distinct _ _ _ runtime _ _ ENDED ACTIVE).
  - apply IHRUN; eapply gateway_activation_step_ended; eassumption.
Qed.

Theorem gateway_observed_resumption_same_activation {World Event} (backend : gateway_backend World Event) ge
    active activation first event last :
  gateway_activation_step backend ge active activation first event last -> gateway_source_resumes event ->
  active (gateway_state_world first) activation /\ active (gateway_state_world last) activation.
Proof. intros OBSERVED RESUME; inversion OBSERVED; subst; auto. Qed.

Theorem gateway_activation_committed_loss {World Event} (backend : gateway_backend World Event) ge
    active activation first observed last :
  gateway_step backend ge first (gateway_committed_lost observed) last ->
  gateway_activation_step backend ge active activation first (gateway_committed_lost observed) last.
Proof. intro STEP; constructor; [exact STEP |cbn [gateway_source_resumes]; contradiction]. Qed.
