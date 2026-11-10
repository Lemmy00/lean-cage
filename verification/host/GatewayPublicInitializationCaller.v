(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Actual callback calls preserve the unavailable flag through entry before rejecting operations. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayPublicInitializationGuard
  GatewayPublicInitializationBoundary GatewayInitializationRegions GatewayInitializationCells GatewayInitializationFailure
  GatewayInitializationAllocation GatewayFunctionEntryBoundary GatewayFramedRuntime GatewayCalls GatewayErrorRuntime GatewayAttachedNative GatewayRuntimeABI.
Import ListNotations.

Theorem gateway_actual_uninitialized_callback {World Event} (backend : gateway_backend World Event)
    native stable rooted
    (runtime : gateway_attached_native_runtime backend native stable rooted)
    symbols active guard arguments before world events external types result convention values continuation after next :
  gateway_initialization_failure_context rooted native symbols active Int.zero before world ->
  gateway_set_error_definition <> External external types result convention ->
  gateway_steps backend (Clight.globalenv prog)
    (gateway_live (Callstate (Internal (public_guard_owner guard)) arguments Kstop before) world) events
    (gateway_live (Callstate (External external types result convention) values continuation after) next) -> False.
Proof.
  intros INPUT DIFFERENT RUN.
  set (property := gateway_initialization_failure_context rooted native symbols active Int.zero).
  assert (CLOSED : gateway_ambient_closed backend property).
  { exact (gateway_initialization_failure_closed backend native stable rooted runtime symbols active Int.zero). }
  destruct (actual_gateway_entry_before_external backend (Clight.globalenv prog) (public_guard_owner guard) arguments Kstop
    before world events external types result convention values continuation after next RUN)
    as (prefix & suffix & memory & owner & environment & parameters & allocated & EVENTS & AMBIENT & PREFIX & ENTRY & BODY).
  assert (AT_ENTRY : property memory owner).
  { exact (gateway_ambient_run_ready backend (Clight.globalenv prog) property CLOSED
      (Callstate (Internal (public_guard_owner guard)) arguments Kstop before) before world prefix memory owner INPUT AMBIENT PREFIX). }
  assert (AT_BODY : property allocated owner).
  { exact (gateway_initialization_rooted_entry backend native stable rooted runtime symbols active Int.zero
      (Clight.globalenv prog) (public_guard_owner guard) arguments memory environment parameters allocated owner ENTRY AT_ENTRY). }
  inversion ENTRY; subst.
  eapply gateway_uninitialized_callback_excludes_operation with (property := property)
    (guard := guard) (environment := environment) (parameters := parameters)
    (allocation_before := memory) (allocated := allocated) (complete := initialization_complete symbols).
  - exact CLOSED.
  - eassumption.
  - exact (initialization_complete_symbol symbols).
  - intros current current_world [_ CELLS]; exact (initialization_cells_complete_value _ _ _ _ _ _ CELLS).
  - exact DIFFERENT.
  - exact AT_BODY.
  - exact BODY.
Qed.
