(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual validation returns retain machine-width loop updates. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayOutcomeEntry GatewayOutcomeValidationSource
  GatewayOutcomeValidationPaths GatewaySourceSegments GatewaySourceSegmentAutomation GatewayFramedRuntime.
Import ListNotations.

Definition gateway_validation_after_first parameters word :=
  PTree.set _index (Vint Int.zero) (PTree.set _valid (Vint word) (set_opttemp (Some _t'1) (Vint word) parameters)).
Definition gateway_validation_after_field parameters word :=
  PTree.set _valid (Vint word) (set_opttemp (Some _t'10) (Vint word) parameters).

Theorem gateway_validation_first_loop {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) environment parameters before word :
  gateway_ambient_closed backend property ->
  gateway_source_segment backend ge property
    (Returnstate (Vint word) (gateway_outcome_first_type_cont environment parameters) before)
    (State f_host_outcome_from gateway_outcome_validation_loop
      (Kseq gateway_outcome_after_field_validation Kstop) environment
      (gateway_validation_after_first parameters word) before) property.
Proof. intro CLOSED; gateway_segment_dynamic CLOSED ltac:(fun _ => fail) ltac:(fun _ => reflexivity). Qed.

Theorem gateway_validation_field_update {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) environment parameters before word :
  gateway_ambient_closed backend property ->
  gateway_source_segment backend ge property
    (Returnstate (Vint word) (gateway_outcome_field_type_cont environment parameters) before)
    (State f_host_outcome_from Sskip gateway_validation_iteration_cont environment
      (gateway_validation_after_field parameters word) before) property.
Proof. intro CLOSED; gateway_segment_dynamic CLOSED ltac:(fun _ => fail) ltac:(fun _ => reflexivity). Qed.

(* The update is the real unsigned32 addition, including wraparound. No bound
   or successful helper premise is used to eliminate a machine transition. *)
Theorem gateway_validation_loop_turn {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) environment parameters before index :
  gateway_ambient_closed backend property -> parameters ! _index = Some (Vint index) ->
  gateway_source_segment backend ge property
    (State f_host_outcome_from Sskip gateway_validation_iteration_cont environment parameters before)
    (State f_host_outcome_from gateway_outcome_validation_loop_body gateway_validation_iteration_cont environment
      (PTree.set _index (Vint (Int.add index Int.one)) parameters) before) property.
Proof.
  intros CLOSED INDEX.
  eapply gateway_segment_same with (next := State f_host_outcome_from gateway_outcome_validation_loop_update
    (Kloop2 gateway_outcome_validation_loop_body gateway_outcome_validation_loop_update
      (Kseq gateway_outcome_after_field_validation Kstop)) environment parameters before).
  - exact CLOSED.
  - cbn; tauto.
  - intros; apply unchanged_store_edge, edge_skip_loop1.
  - eapply gateway_segment_same with (next := State f_host_outcome_from Sskip
      (Kloop2 gateway_outcome_validation_loop_body gateway_outcome_validation_loop_update
        (Kseq gateway_outcome_after_field_validation Kstop)) environment
      (PTree.set _index (Vint (Int.add index Int.one)) parameters) before).
    + exact CLOSED.
    + cbn; tauto.
    + intros; apply certified_set_edge.
      eapply binary_expression_value with (v := Vint index) (w := Vint Int.one).
      * apply old_expression_value, value_temp; exact INDEX.
      * apply old_expression_value; constructor.
      * reflexivity.
    + eapply gateway_segment_same with (next := State f_host_outcome_from gateway_outcome_validation_loop
        (Kseq gateway_outcome_after_field_validation Kstop) environment
        (PTree.set _index (Vint (Int.add index Int.one)) parameters) before).
      * exact CLOSED.
      * cbn; tauto.
      * intros; apply unchanged_store_edge, edge_skip_loop2.
      * eapply gateway_segment_same with (next := State f_host_outcome_from gateway_outcome_validation_loop_body
          gateway_validation_iteration_cont environment
          (PTree.set _index (Vint (Int.add index Int.one)) parameters) before).
        -- exact CLOSED.
        -- cbn; tauto.
        -- intros; apply unchanged_store_edge, edge_loop.
        -- apply gateway_segment_here.
Qed.

Theorem gateway_validation_loop_entry {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) environment parameters before :
  gateway_ambient_closed backend property ->
  gateway_source_segment backend ge property
    (State f_host_outcome_from gateway_outcome_validation_loop (Kseq gateway_outcome_after_field_validation Kstop)
      environment parameters before)
    (State f_host_outcome_from gateway_outcome_validation_loop_body gateway_validation_iteration_cont environment parameters before) property.
Proof.
  intro CLOSED; eapply gateway_segment_same; [exact CLOSED |cbn; tauto | |apply gateway_segment_here].
  intros; apply unchanged_store_edge, edge_loop.
Qed.
