(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Actual callback entries produce their own guarded source control. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayRegistry GatewayMachine GatewayGlobalAddresses GatewayBindings GatewayRuntimeABI
  GatewayInterpreterSource GatewayLinkedSource GatewayCallbackEntries GatewayCallbackGuards GatewayRuntimeMemory
  GatewayScopedBackend GatewaySourceFrames GatewayGuardedFrames GatewayGuardedInitializer GatewayNoStoreControl.
Import ListNotations.

Theorem gateway_linked_initializer_apis runtime :
  gateway_runtime_registration runtime ->
  gateway_function_binding (Clight.globalenv (gateway_linked_program runtime))
    _PyInterpreterState_Get gateway_interpreter_get_definition /\
  gateway_function_binding (Clight.globalenv (gateway_linked_program runtime))
    _PyInterpreterState_GetID gateway_interpreter_id_definition /\
  gateway_function_binding (Clight.globalenv (gateway_linked_program runtime))
    _PyErr_SetString gateway_set_error_definition.
Proof.
  intro REGISTERED; repeat split; eapply gateway_linked_source_binding; [exact REGISTERED | |exact REGISTERED | |exact REGISTERED |].
  all: apply gateway_program_definition_present; vm_compute; reflexivity.
Qed.

Theorem gateway_guarded_callback_control {World Event} (backend : gateway_backend World Event)
    runtime storage callback identifier body arguments before world active complete :
  gateway_runtime_registration runtime -> gateway_interpreter_result_shapes backend ->
  (forall object, storage object -> ~ gateway_private_cell (Clight.globalenv (gateway_linked_program runtime)) object) ->
  Genv.find_symbol (Clight.globalenv (gateway_linked_program runtime)) _host_initializing = Some active ->
  Genv.find_symbol (Clight.globalenv (gateway_linked_program runtime)) _host_initialized = Some complete ->
  gateway_callback_memory_origin (gateway_private_cell (Clight.globalenv (gateway_linked_program runtime)))
    (gateway_reentry_guard active complete) callback ->
  In (identifier, Gfun (Internal body)) global_definitions -> gateway_callback_registered identifier = true ->
  length arguments = length (fn_params body) -> gateway_reentry_guard active complete before ->
  gateway_source_frame_control backend (Clight.globalenv (gateway_linked_program runtime)) storage callback
    (gateway_live (Callstate (Internal body) arguments Kstop before) world).
Proof.
  intros REGISTERED SHAPES STORAGE ACTIVE COMPLETE CALLBACK MEMBER EXPORTED ABI GUARDED.
  destruct (gateway_actual_callback_kind identifier body MEMBER EXPORTED) as [ORDINARY |INITIALIZER].
  - left; split; [split; [exact ORDINARY |exists identifier; exact MEMBER] |exact I].
  - subst body; change (length arguments = 0%nat) in ABI; apply length_zero_iff_nil in ABI; subst arguments.
    destruct (gateway_linked_initializer_apis runtime REGISTERED) as [GET [ID ERROR]].
    set (ge := Clight.globalenv (gateway_linked_program runtime)) in *.
    assert (GUARD_FRAME : forall before after,
      Mem.unchanged_on (fun object _ => gateway_private_cell ge object) before after ->
      gateway_reentry_guard active complete before -> gateway_reentry_guard active complete after).
    { intros; eapply gateway_reentry_guard_frame; eassumption. }
    right; destruct GUARDED as [RUNNING |[IDLE FINISHED]].
    + set (property := fun (memory : mem) (_ : World) => Mem.load Mint32 memory active 0 = Some (Vint Int.one)).
      assert (READY : forall memory world, property memory world -> gateway_reentry_guard active complete memory).
      { intros; left; exact H. }
      assert (RETAINS : forall before after world next,
        Mem.unchanged_on (fun object _ => gateway_private_cell ge object) before after ->
        property before world -> property after next).
      { intros; eapply gateway_private_flag_frame with (identifier := _host_initializing); eassumption || reflexivity. }
      exists property; split; [exact RUNNING |].
      eapply gateway_active_initializer_no_stores.
      * eapply gateway_scoped_property_closed; eassumption.
      * eapply gateway_scoped_query_laws; eassumption.
      * exact GET.
      * exact ID.
      * exact ERROR.
      * exact ACTIVE.
      * intros; exact H.
    + set (property := fun (memory : mem) (_ : World) =>
        Mem.load Mint32 memory active 0 = Some (Vint Int.zero) /\
        Mem.load Mint32 memory complete 0 = Some (Vint Int.one)).
      assert (READY : forall memory world, property memory world -> gateway_reentry_guard active complete memory).
      { intros; right; exact H. }
      assert (RETAINS : forall before after world next,
        Mem.unchanged_on (fun object _ => gateway_private_cell ge object) before after ->
        property before world -> property after next).
      { intros before0 after0 first next FRAME [ZERO ONE]; split.
        - eapply gateway_private_flag_frame with (identifier := _host_initializing); eassumption || reflexivity.
        - eapply gateway_private_flag_frame with (identifier := _host_initialized); eassumption || reflexivity. }
      exists property; split; [exact (conj IDLE FINISHED) |].
      eapply gateway_complete_initializer_no_stores.
      * eapply gateway_scoped_property_closed; eassumption.
      * eapply gateway_scoped_query_laws; eassumption.
      * exact GET.
      * exact ID.
      * exact ERROR.
      * exact ACTIVE.
      * exact COMPLETE.
      * intros memory0 world0 [ZERO ONE]; exact ZERO.
      * intros memory0 world0 [ZERO ONE]; exact ONE.
Qed.
