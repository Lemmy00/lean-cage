(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: A failed private initializer cannot become a successful public return. *)
From Stdlib Require Import List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayInitializationSource GatewayInitializationEntrySource
  GatewaySourceSegments GatewaySourceSegmentAutomation GatewayFramedRuntime GatewayReturns GatewayAssignmentCut.
Import ListNotations.

Theorem gateway_initialization_null_to_clear {World Event} (backend : gateway_backend World Event) ge parameters memory :
  exists changed_parameters,
    gateway_source_segment backend ge (fun _ _ => True)
      (Returnstate Vnullptr (initialization_body_cont parameters) memory)
      (State f_PyInit__host initialization_clear (Kseq initialization_return Kstop) empty_env changed_parameters memory)
      (fun _ _ => True) /\ changed_parameters ! _result = Some Vnullptr.
Proof.
  assert (CLOSED : gateway_ambient_closed backend (fun _ _ => True)) by (unfold gateway_ambient_closed; intros; exact I).
  eexists; split.
  - gateway_segment_dynamic CLOSED ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
  - unfold set_opttemp; apply PTree.gss.
Qed.

Theorem gateway_initialization_null_return_script ge parameters memory :
  parameters ! _result = Some Vnullptr ->
  gateway_constant_path ge Vnullptr
    (State f_PyInit__host Sskip (Kseq initialization_return Kstop) empty_env parameters memory).
Proof.
  intro RESULT.
  eapply gateway_constant_next with (next := State f_PyInit__host initialization_return Kstop empty_env parameters memory).
  - cbn; tauto.
  - intros; apply unchanged_store_edge, edge_skip_seq.
  - eapply gateway_constant_at_return with (value := Vnullptr).
    + reflexivity.
    + intros; apply old_expression_value, value_temp; exact RESULT.
    + intros; reflexivity.
Qed.

Theorem gateway_actual_initialization_null_body {World Event} (backend : gateway_backend World Event) ge
    parameters before world events value after next :
  gateway_steps backend ge
    (gateway_live (Returnstate Vnullptr (initialization_body_cont parameters) before) world) events
    (gateway_live (Returnstate value Kstop after) next) -> value = Vnullptr.
Proof.
  intro RUN.
  destruct (gateway_initialization_null_to_clear backend ge parameters before) as [changed_parameters [SEGMENT RESULT]].
  destruct (gateway_source_segment_cut backend ge _ _ _ _ SEGMENT before world events value after next I RUN)
    as (prefix & rest & memory & owner & EVENTS & QUIET & PREFIX & READY & FROM_CLEAR).
  destruct (gateway_actual_assignment_cut backend ge f_PyInit__host
    (Evar _host_initializing Ctypesdefs.tint) (Econst_int Int.zero Ctypesdefs.tint)
    (Kseq initialization_return Kstop) empty_env changed_parameters memory owner rest value after next FROM_CLEAR)
    as (pending & suffix & called & current & trace & changed & REST_EVENTS & AMBIENT & PENDING & REST).
  eapply gateway_constant_path_actual; [apply gateway_initialization_null_return_script; exact RESULT |exact REST].
Qed.

Theorem gateway_actual_initialization_body_nonnull {World Event} (backend : gateway_backend World Event) ge
    parameters returned before world events value after next :
  gateway_steps backend ge
    (gateway_live (Returnstate returned (initialization_body_cont parameters) before) world) events
    (gateway_live (Returnstate value Kstop after) next) -> value <> Vnullptr -> returned <> Vnullptr.
Proof.
  intros RUN NONNULL NULL; subst returned; apply NONNULL; eapply gateway_actual_initialization_null_body; exact RUN.
Qed.
