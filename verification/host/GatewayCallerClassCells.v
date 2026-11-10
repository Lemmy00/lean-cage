(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: A real caller prefix retains the class loaded by its constructor. *)
From Stdlib Require Import ZArith List.
From compcert Require Import AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayGlobalAddresses GatewayPointerControl GatewayLinkedSource
  GatewayRuntimeMemory GatewayRuntimeCoverage GatewaySourceCallbacks GatewayCallbackGuards GatewayCallbackRetention
  GatewayGuardedFrames GatewayRuntimeRetention GatewayOrdinarySource GatewayOrdinaryControl GatewaySourceFrames.
Import ListNotations.

Theorem gateway_ordinary_caller_class_load {World Event} (backend : gateway_backend World Event)
    runtime storage depth active complete identifier body arguments before world events target
    class_identifier cell class :
  gateway_runtime_registration runtime -> gateway_interpreter_result_shapes backend ->
  (forall object, storage object -> ~ gateway_private_cell (Clight.globalenv (gateway_linked_program runtime)) object) ->
  Genv.find_symbol (Clight.globalenv (gateway_linked_program runtime)) _host_initializing = Some active ->
  Genv.find_symbol (Clight.globalenv (gateway_linked_program runtime)) _host_initialized = Some complete ->
  In (identifier, Gfun (Internal body)) global_definitions -> gateway_ordinary_function body = true ->
  gateway_private_cell_name class_identifier = true ->
  Genv.find_symbol (Clight.globalenv (gateway_linked_program runtime)) class_identifier = Some cell ->
  Mem.load Mptr before cell 0 = Some class ->
  gateway_runtime_memory_scope (gateway_private_cell (Clight.globalenv (gateway_linked_program runtime))) before arguments ->
  gateway_reentry_guard active complete before ->
  gateway_covered_steps backend (Clight.globalenv (gateway_linked_program runtime)) storage
    (gateway_source_callbacks backend runtime storage depth)
    (gateway_live (Callstate (Internal body) arguments Kstop before) world) events target ->
  Mem.load Mptr (gateway_state_memory target) cell 0 = Some class.
Proof.
  intros REGISTERED SHAPES STORAGE ACTIVE COMPLETE MEMBER ORDINARY PRIVATE SYMBOL LOAD SCOPE GUARDED RUN.
  eapply gateway_private_pointer_cell_frame; [exact PRIVATE |exact SYMBOL | |exact LOAD].
  eapply (gateway_control_covered_prefix_frame backend runtime storage
    (gateway_source_callbacks backend runtime storage depth) (gateway_reentry_guard active complete)
    (gateway_live (Callstate (Internal body) arguments Kstop before) world) events target).
  - exact REGISTERED.
  - exact STORAGE.
  - apply gateway_source_callbacks_memory; assumption.
  - intros first last FRAME READY; eapply gateway_reentry_guard_frame; eassumption.
  - destruct SCOPE as [MEMORY [LIVE ARGUMENTS]]; eapply gateway_callback_pointer_entry; eassumption.
  - left; split; [split; [exact ORDINARY |exists identifier; exact MEMBER] |exact I].
  - exact GUARDED.
  - exact RUN.
Qed.
