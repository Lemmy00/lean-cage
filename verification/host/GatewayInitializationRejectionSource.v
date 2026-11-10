(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Active and completed entries select the real
   rejection body. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayInitializationSource GatewayInterpreterSource
  GatewaySourceSegments GatewaySourceSegmentAutomation GatewayFramedRuntime GatewayPublicInitializationBoundary
  GatewayReturnBarrier.
Import ListNotations.

Definition initialization_active_denied := match initialization_active_check with
  Ssequence _ (Sifthenelse _ rejected _) => rejected | _ => Sskip end.
Definition initialization_complete_denied := match initialization_complete_check with
  Ssequence _ (Sifthenelse _ rejected _) => rejected | _ => Sskip end.

Theorem actual_initialization_rejection_profiles :
  gateway_barrier_returns public_denial_api initialization_active_denied /\
  gateway_barrier_returns public_denial_api initialization_complete_denied.
Proof. split; vm_compute; tauto. Qed.

Theorem gateway_initialization_active_rejection_source {World Event}
    (backend : gateway_backend World Event) (ge : Clight.genv) (property : mem -> World -> Prop)
    parameters memory active :
  gateway_ambient_closed backend property -> Genv.find_symbol ge _host_initializing = Some active ->
  (forall memory world, property memory world -> Mem.load Mint32 memory active 0 = Some (Vint Int.one)) ->
  exists changed,
    gateway_source_segment backend ge property
      (Returnstate (Vlong Int64.zero) (gateway_interpreter_id_cont true parameters) memory)
      (State f_PyInit__host initialization_active_denied (Kseq initialization_after_active Kstop)
        empty_env changed memory) property.
Proof.
  intros CLOSED SYMBOL LOAD; eexists.
  gateway_segment_dynamic CLOSED
    ltac:(fun _ => eapply initialization_global_word; [exact SYMBOL |eapply LOAD; eassumption])
    ltac:(fun _ => reflexivity).
Qed.

Theorem gateway_initialization_complete_rejection_source {World Event}
    (backend : gateway_backend World Event) (ge : Clight.genv) (property : mem -> World -> Prop)
    parameters memory active complete :
  gateway_ambient_closed backend property ->
  Genv.find_symbol ge _host_initializing = Some active -> Genv.find_symbol ge _host_initialized = Some complete ->
  (forall memory world, property memory world -> Mem.load Mint32 memory active 0 = Some (Vint Int.zero)) ->
  (forall memory world, property memory world -> Mem.load Mint32 memory complete 0 = Some (Vint Int.one)) ->
  exists changed,
    gateway_source_segment backend ge property
      (Returnstate (Vlong Int64.zero) (gateway_interpreter_id_cont true parameters) memory)
      (State f_PyInit__host initialization_complete_denied (Kseq initialization_after_complete Kstop)
        empty_env changed memory) property.
Proof.
  intros CLOSED ACTIVE COMPLETE ACTIVE_LOAD COMPLETE_LOAD; eexists.
  gateway_segment_dynamic CLOSED
    ltac:(fun _ => first [eapply initialization_global_word; [exact ACTIVE |eapply ACTIVE_LOAD; eassumption] |
      eapply initialization_global_word; [exact COMPLETE |eapply COMPLETE_LOAD; eassumption]])
    ltac:(fun _ => reflexivity).
Qed.
