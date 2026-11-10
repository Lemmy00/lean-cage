(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Actual successful return sets completed, clears active and returns the same module. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayInitializationSource GatewayInitializationEntrySource
  GatewaySourceSegments GatewaySourceSegmentAutomation GatewayFramedRuntime.
Import ListNotations.

Lemma initialization_completion_segment_compose {World Event} (backend : gateway_backend World Event) ge
    property source middle boundary target result :
  gateway_source_segment backend ge property source middle boundary ->
  gateway_source_segment backend ge boundary middle target result ->
  gateway_source_segment backend ge property source target result.
Proof.
  intro FIRST; induction FIRST; intro SECOND; [exact SECOND |].
  eapply gateway_segment_next; [exact H |exact H0 |exact H1 |apply IHFIRST; exact SECOND].
Qed.

Theorem gateway_initialization_success_frontier {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) parameters object offset memory :
  gateway_ambient_closed backend property ->
  (forall memory world, property memory world -> Mem.weak_valid_pointer memory object (Ptrofs.unsigned offset) = true) ->
  exists changed,
    gateway_source_segment backend ge property
      (Returnstate (Vptr object offset) (initialization_body_cont parameters) memory)
      (State f_PyInit__host (Sassign (Evar _host_initialized tint) (Econst_int Int.one tint))
        (Kseq initialization_after_success Kstop) empty_env changed memory) property /\
    changed ! _result = Some (Vptr object offset).
Proof.
  intros CLOSED LIVE.
  assert (PREFIX : exists changed,
    gateway_source_segment backend ge property
      (Returnstate (Vptr object offset) (initialization_body_cont parameters) memory)
      (State f_PyInit__host initialization_success (Kseq initialization_after_success Kstop) empty_env changed memory) property /\
    changed ! _result = Some (Vptr object offset)).
  { eexists; split.
    - gateway_segment_dynamic CLOSED ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
    - apply PTree.gss. }
  destruct PREFIX as (changed & PREFIX & RESULT); exists changed; split; [|exact RESULT].
  eapply initialization_completion_segment_compose; [exact PREFIX |].
  eapply gateway_segment_same with (next := State f_PyInit__host
    (Sassign (Evar _host_initialized tint) (Econst_int Int.one tint))
    (Kseq initialization_after_success Kstop) empty_env changed memory).
  - exact CLOSED.
  - cbn; tauto.
  - intros current owner GOOD; eapply certified_if_edge with (v := Vptr object offset) (b := true).
    + apply old_expression_value, value_temp; exact RESULT.
    + change ((if Mem.weak_valid_pointer current object (Ptrofs.unsigned offset) then Some true else None) = Some true).
      rewrite (LIVE current owner GOOD); reflexivity.
  - apply gateway_segment_here.
Qed.

Theorem gateway_initialization_success_to_clear {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) parameters memory :
  gateway_ambient_closed backend property ->
  gateway_source_segment backend ge property
    (State f_PyInit__host Sskip (Kseq initialization_after_success Kstop) empty_env parameters memory)
    (State f_PyInit__host initialization_clear (Kseq initialization_return Kstop) empty_env parameters memory) property.
Proof.
  intro CLOSED; gateway_segment_dynamic CLOSED ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
Qed.

Theorem gateway_initialization_success_return {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) parameters object offset memory :
  gateway_ambient_closed backend property -> parameters ! _result = Some (Vptr object offset) ->
  gateway_source_segment backend ge property
    (State f_PyInit__host Sskip (Kseq initialization_return Kstop) empty_env parameters memory)
    (Returnstate (Vptr object offset) Kstop memory) property.
Proof.
  intros CLOSED RESULT.
  eapply gateway_segment_same with (next := State f_PyInit__host initialization_return Kstop empty_env parameters memory);
    [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_skip_seq |].
  eapply gateway_segment_same with (next := Returnstate (Vptr object offset) Kstop memory).
  - exact CLOSED.
  - cbn; tauto.
  - intros; apply unchanged_store_edge; eapply edge_return with (v := Vptr object offset);
      [apply value_temp; exact RESULT |reflexivity].
  - apply gateway_segment_here.
Qed.

Theorem gateway_initialization_failed_frontier {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) parameters memory :
  gateway_ambient_closed backend property ->
  exists changed,
    gateway_source_segment backend ge property
      (Returnstate Vnullptr (initialization_body_cont parameters) memory)
      (State f_PyInit__host initialization_clear (Kseq initialization_return Kstop) empty_env changed memory) property /\
    changed ! _result = Some Vnullptr.
Proof.
  intros CLOSED; eexists; split.
  - gateway_segment_dynamic CLOSED ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
  - apply PTree.gss.
Qed.

Theorem gateway_initialization_failed_return {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) parameters memory :
  gateway_ambient_closed backend property -> parameters ! _result = Some Vnullptr ->
  gateway_source_segment backend ge property
    (State f_PyInit__host Sskip (Kseq initialization_return Kstop) empty_env parameters memory)
    (Returnstate Vnullptr Kstop memory) property.
Proof.
  intros CLOSED RESULT.
  eapply gateway_segment_same with (next := State f_PyInit__host initialization_return Kstop empty_env parameters memory);
    [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_skip_seq |].
  eapply gateway_segment_same with (next := Returnstate Vnullptr Kstop memory).
  - exact CLOSED.
  - cbn; tauto.
  - intros; apply unchanged_store_edge; eapply edge_return with (v := Vnullptr);
      [apply value_temp; exact RESULT |reflexivity].
  - apply gateway_segment_here.
Qed.
