(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Actual C fcntl calls use status commands or CLOEXEC duplication. *)
From Stdlib Require Import List Bool.
From compcert Require Import Coqlib Maps AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySpawnABI GatewayFcntlProfile
  GatewayFcntlControl GatewayFcntlLabels GatewayFcntlArguments.
Import ListNotations.

Theorem gateway_internal_fcntl_source source observed target :
  internal_state source -> gateway_fcntl_source source ->
  step2 (Clight.globalenv prog) source observed target -> gateway_fcntl_source target.
Proof.
  intros INTERNAL GOOD STEP; inversion STEP; subst;
    cbn [internal_state] in INTERNAL; try contradiction;
    cbn [gateway_fcntl_source] in GOOD |- *.
  all: try (destruct GOOD as [WHOLE [CURRENT CONTINUATION]]).
  all: try (pose proof CURRENT as SOURCE_AST; cbn [gateway_fcntl_statement gateway_fcntl_local] in CURRENT;
    repeat rewrite andb_true_iff in CURRENT).
  all: try (cbn [gateway_fcntl_cont] in CONTINUATION).
  all: cbn [gateway_fcntl_source gateway_fcntl_cont gateway_fcntl_statement gateway_fcntl_local].
  all: repeat rewrite andb_true_iff.
  all: try solve [repeat split; assumption || reflexivity || tauto].
  - split; [eapply gateway_actual_fcntl_function; eassumption |].
    split; [split; assumption |].
    intro FCNTL; subst fd.
    match goal with TYPE : type_of_fundef (gateway_spawn_signature gateway_fcntl_api) = _ |- _ =>
      cbn [gateway_spawn_signature type_of_fundef] in TYPE; inversion TYPE; subst end.
    eapply gateway_fcntl_evaluated_command; eassumption.
  - destruct b; repeat split; tauto.
  - apply gateway_fcntl_call_cont; exact CONTINUATION.
  - apply gateway_fcntl_call_cont; exact CONTINUATION.
  - split; [exact WHOLE |]. split.
    + apply gateway_fcntl_switch; exact (proj2 CURRENT).
    + exact CONTINUATION.
  - destruct (gateway_fcntl_find_label lbl (fn_body f) (call_cont k) s' k' WHOLE
      (gateway_fcntl_call_cont _ CONTINUATION) H) as [BODY CONT].
    repeat split; assumption.
  - cbn [gateway_fcntl_cont gateway_fcntl_definition] in *; tauto.
Qed.

Definition gateway_fcntl_state {World} (state : gateway_state World) : Prop :=
  match state with gateway_live source _ => gateway_fcntl_source source | gateway_dead _ _ => True end.

Theorem gateway_step_fcntl_source {World Event} (backend : gateway_backend World Event)
    before observed after : gateway_fcntl_state before -> gateway_step backend (Clight.globalenv prog) before observed after ->
    gateway_fcntl_state after.
Proof.
  intros GOOD STEP; inversion STEP; subst; cbn [gateway_fcntl_state gateway_fcntl_source] in GOOD |- *; try exact I.
  - eapply gateway_internal_fcntl_source; eassumption.
  - tauto.
  - destruct GOOD as [WHOLE [CURRENT CONTINUATION]].
    cbn [gateway_fcntl_statement gateway_fcntl_local]; repeat split; assumption || reflexivity.
  - destruct source; exact GOOD.
  - exact GOOD.
Qed.

Theorem gateway_actual_pending_fcntl_command {World Event} (backend : gateway_backend World Event)
    source world events arguments continuation memory current :
  gateway_fcntl_source source ->
  gateway_steps backend (Clight.globalenv prog) (gateway_live source world) events
    (gateway_live (Callstate (gateway_spawn_signature gateway_fcntl_api) arguments continuation memory) current) ->
  gateway_fcntl_values arguments.
Proof.
  intros INITIAL RUN.
  assert (FINAL : gateway_fcntl_state
    (gateway_live (Callstate (gateway_spawn_signature gateway_fcntl_api) arguments continuation memory) current)).
  { change (gateway_fcntl_state (gateway_live source world)) in INITIAL.
    induction RUN; [exact INITIAL |]. apply IHRUN; eapply gateway_step_fcntl_source; eassumption. }
  cbn [gateway_fcntl_state gateway_fcntl_source] in FINAL; exact (proj2 (proj2 FINAL) eq_refl).
Qed.

Theorem gateway_actual_function_fcntl_prefix {World Event} (backend : gateway_backend World Event)
    value function environment temporaries before world events arguments continuation memory current :
  Genv.find_funct (Clight.globalenv prog) value = Some (Internal function) ->
  gateway_steps backend (Clight.globalenv prog)
    (gateway_live (State function (fn_body function) Kstop environment temporaries before) world) events
    (gateway_live (Callstate (gateway_spawn_signature gateway_fcntl_api) arguments continuation memory) current) ->
  gateway_fcntl_values arguments.
Proof.
  intros FOUND PREFIX.
  pose proof (gateway_actual_fcntl_function _ _ FOUND) as BODY.
  cbn [gateway_fcntl_definition] in BODY.
  eapply gateway_actual_pending_fcntl_command; [|exact PREFIX].
  cbn [gateway_fcntl_source gateway_fcntl_cont]; tauto.
Qed.
