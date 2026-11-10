(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Rejected real entries cannot reach an operational
   callee. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayInitializationSource GatewayInterpreterSource
  GatewayInitializationRejectionSource GatewaySourceBoundaryCuts GatewayFramedRuntime
  GatewayPublicInitializationBoundary GatewayRuntimeABI GatewayReturnBarrier.
Import ListNotations.

Theorem gateway_active_initializer_excludes_operation {World Event}
    (backend : gateway_backend World Event) (property : mem -> World -> Prop)
    parameters before world events active external types result_type convention arguments continuation after next :
  gateway_ambient_closed backend property -> Genv.find_symbol (Clight.globalenv prog) _host_initializing = Some active ->
  (forall memory world, property memory world -> Mem.load Mint32 memory active 0 = Some (Vint Int.one)) ->
  gateway_set_error_definition <> External external types result_type convention -> property before world ->
  gateway_steps backend (Clight.globalenv prog)
    (gateway_live (Returnstate (Vlong Int64.zero) (gateway_interpreter_id_cont true parameters) before) world) events
    (gateway_live (Callstate (External external types result_type convention) arguments continuation after) next) -> False.
Proof.
  intros CLOSED SYMBOL LOAD DIFFERENT INPUT RUN.
  destruct (gateway_initialization_active_rejection_source backend (Clight.globalenv prog) property parameters before active
    CLOSED SYMBOL LOAD) as (changed & SCRIPT).
  destruct (gateway_source_segment_external_cut backend (Clight.globalenv prog) _ _ _ _ SCRIPT
    before world events external types result_type convention arguments continuation after next INPUT RUN)
    as (prefix & suffix & memory & owner & EVENTS & QUIET & PREFIX & AT_DENIAL & SUFFIX).
  eapply gateway_return_barrier_excludes_call with (environment := empty_env) (allowed := public_denial_api)
    (body := initialization_active_denied) (continuation := Kseq initialization_after_active Kstop).
  - apply actual_public_denial_bindings; [reflexivity |exact DIFFERENT].
  - exact (proj1 actual_initialization_rejection_profiles).
  - reflexivity.
  - exact SUFFIX.
Qed.

Theorem gateway_completed_initializer_excludes_operation {World Event}
    (backend : gateway_backend World Event) (property : mem -> World -> Prop)
    parameters before world events active complete external types result_type convention arguments continuation after next :
  gateway_ambient_closed backend property ->
  Genv.find_symbol (Clight.globalenv prog) _host_initializing = Some active ->
  Genv.find_symbol (Clight.globalenv prog) _host_initialized = Some complete ->
  (forall memory world, property memory world -> Mem.load Mint32 memory active 0 = Some (Vint Int.zero)) ->
  (forall memory world, property memory world -> Mem.load Mint32 memory complete 0 = Some (Vint Int.one)) ->
  gateway_set_error_definition <> External external types result_type convention -> property before world ->
  gateway_steps backend (Clight.globalenv prog)
    (gateway_live (Returnstate (Vlong Int64.zero) (gateway_interpreter_id_cont true parameters) before) world) events
    (gateway_live (Callstate (External external types result_type convention) arguments continuation after) next) -> False.
Proof.
  intros CLOSED ACTIVE COMPLETE ACTIVE_LOAD COMPLETE_LOAD DIFFERENT INPUT RUN.
  destruct (gateway_initialization_complete_rejection_source backend (Clight.globalenv prog) property parameters before active complete
    CLOSED ACTIVE COMPLETE ACTIVE_LOAD COMPLETE_LOAD) as (changed & SCRIPT).
  destruct (gateway_source_segment_external_cut backend (Clight.globalenv prog) _ _ _ _ SCRIPT
    before world events external types result_type convention arguments continuation after next INPUT RUN)
    as (prefix & suffix & memory & owner & EVENTS & QUIET & PREFIX & AT_DENIAL & SUFFIX).
  eapply gateway_return_barrier_excludes_call with (environment := empty_env) (allowed := public_denial_api)
    (body := initialization_complete_denied) (continuation := Kseq initialization_after_complete Kstop).
  - apply actual_public_denial_bindings; [reflexivity |exact DIFFERENT].
  - exact (proj2 actual_initialization_rejection_profiles).
  - reflexivity.
  - exact SUFFIX.
Qed.
