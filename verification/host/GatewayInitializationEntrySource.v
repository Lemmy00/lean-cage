(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Real zero guards precede the source-owned active store and private helper call. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayInterpreterSource GatewayInitializationSource
  GatewaySourceBoundCalls GatewaySourcePaths GatewaySourceSegments GatewaySourceSegmentAutomation GatewayFramedRuntime.
Import ListNotations.

Definition initialization_body_cont parameters :=
  Kcall (Some _t'3) f_PyInit__host empty_env parameters
    (Kseq initialization_bind_result (Kseq initialization_after_body Kstop)).

Theorem gateway_initialization_to_enter {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) parameters memory active complete :
  gateway_ambient_closed backend property ->
  Genv.find_symbol ge _host_initializing = Some active -> Genv.find_symbol ge _host_initialized = Some complete ->
  (forall memory world, property memory world -> Mem.load Mint32 memory active 0 = Some (Vint Int.zero)) ->
  (forall memory world, property memory world -> Mem.load Mint32 memory complete 0 = Some (Vint Int.zero)) ->
  exists called_parameters,
    gateway_source_segment backend ge property
      (Returnstate (Vlong Int64.zero) (gateway_interpreter_id_cont true parameters) memory)
      (State f_PyInit__host initialization_enter (Kseq initialization_after_enter Kstop) empty_env called_parameters memory) property.
Proof.
  intros CLOSED ACTIVE COMPLETE ACTIVE_VALUE COMPLETE_VALUE; eexists.
  gateway_segment_dynamic CLOSED
    ltac:(fun _ => first [eapply initialization_global_word; [exact ACTIVE |eapply ACTIVE_VALUE; eassumption] |
      eapply initialization_global_word; [exact COMPLETE |eapply COMPLETE_VALUE; eassumption]])
    ltac:(fun _ => reflexivity).
Qed.

Theorem gateway_initialization_after_enter_path {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) parameters memory symbol :
  gateway_ambient_closed backend property ->
  Genv.find_symbol ge _host_initialize = Some symbol -> Genv.find_funct_ptr ge symbol = Some (Internal f_host_initialize) ->
  gateway_source_path backend ge (Internal f_host_initialize) [] (initialization_body_cont parameters) property
    (State f_PyInit__host Sskip (Kseq initialization_after_enter Kstop) empty_env parameters memory) property.
Proof.
  intros CLOSED SYMBOL FUNCTION.
  gateway_bound_source_call CLOSED ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
  eapply gateway_source_same with (target := Callstate (Internal f_host_initialize) [] (initialization_body_cont parameters) memory).
  - exact CLOSED.
  - cbn; tauto.
  - intros; eapply actual_initialization_body_edge with (symbol := symbol); assumption.
  - apply gateway_source_reached; auto.
Qed.
