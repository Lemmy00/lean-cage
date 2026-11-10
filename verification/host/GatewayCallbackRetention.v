(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Arbitrary-depth actual source callbacks derive the private-cell frame. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayGlobalAddresses GatewayLinkedSource
  GatewayRuntimeMemory GatewayCoveredPointers GatewaySourceCallbacks GatewayCallbackGuards
  GatewayGuardedFrames GatewayCallbackInitialization.
Import ListNotations.

Theorem gateway_source_callbacks_memory {World Event} (backend : gateway_backend World Event)
    runtime storage active complete depth :
  gateway_runtime_registration runtime -> gateway_interpreter_result_shapes backend ->
  (forall object, storage object -> ~ gateway_private_cell (Clight.globalenv (gateway_linked_program runtime)) object) ->
  Genv.find_symbol (Clight.globalenv (gateway_linked_program runtime)) _host_initializing = Some active ->
  Genv.find_symbol (Clight.globalenv (gateway_linked_program runtime)) _host_initialized = Some complete ->
  gateway_callback_memory_origin (gateway_private_cell (Clight.globalenv (gateway_linked_program runtime)))
    (gateway_reentry_guard active complete) (gateway_source_callbacks backend runtime storage depth).
Proof.
  intros REGISTERED SHAPES STORAGE ACTIVE COMPLETE; induction depth as [|depth IH];
    intros before arguments after result MEMORY LIVE ARGUMENTS CALLBACK; [contradiction |].
  destruct (gateway_source_callbacks_pointer backend runtime storage (S depth) (proj1 REGISTERED) STORAGE
    before arguments after result MEMORY LIVE ARGUMENTS CALLBACK) as [NEXT [RETAINED RESULT]].
  split; [exact NEXT |split; [exact RETAINED |split; [exact RESULT |]]].
  intro GUARDED.
  destruct CALLBACK as (identifier & body & world & events & target & MEMBER & EXPORTED & ABI & RUN & AFTER & OBSERVATION).
  subst after.
  eapply gateway_control_covered_prefix_frame with
    (first := gateway_live (Callstate (Internal body) arguments Kstop before) world).
  - exact REGISTERED.
  - exact STORAGE.
  - exact IH.
  - intros first last FRAME READY; eapply gateway_reentry_guard_frame; eassumption.
  - eapply gateway_callback_pointer_entry; eassumption.
  - eapply gateway_guarded_callback_control; eassumption.
  - exact GUARDED.
  - exact RUN.
Qed.
