(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Source callback trees supply the same original program's private-cell frame. *)
From Stdlib Require Import ZArith List.
From compcert Require Import AST Values Memory Events Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayGlobalAddresses GatewayLinkedSource
  GatewayLinkedAddresses GatewayPointerEquivalence GatewayRuntimeMemory GatewaySourceCallbacks GatewayCallbackGuards
  GatewayCallbackRetention.
Import ListNotations.

Theorem gateway_registered_callback_origin {World Event} (backend : gateway_backend World Event)
    runtime storage active complete depth :
  gateway_runtime_registration runtime -> gateway_interpreter_result_shapes backend ->
  (forall object, storage object -> ~ gateway_private_cell (Clight.globalenv prog) object) ->
  Genv.find_symbol (Clight.globalenv prog) _host_initializing = Some active ->
  Genv.find_symbol (Clight.globalenv prog) _host_initialized = Some complete ->
  gateway_callback_memory_origin (gateway_private_cell (Clight.globalenv prog))
    (gateway_reentry_guard active complete) (gateway_source_callbacks backend runtime storage depth).
Proof.
  intros REGISTERED SHAPES STORAGE ACTIVE COMPLETE.
  eapply gateway_callback_origin_equivalent.
  - intro object; apply gateway_linked_private_cells; exact REGISTERED.
  - apply gateway_source_callbacks_memory.
    + exact REGISTERED.
    + exact SHAPES.
    + intros object FOREIGN PRIVATE; apply (STORAGE object FOREIGN).
      apply (proj1 (gateway_linked_private_cells runtime object REGISTERED)); exact PRIVATE.
    + rewrite (gateway_linked_private_symbol runtime _host_initializing REGISTERED eq_refl); exact ACTIVE.
    + rewrite (gateway_linked_private_symbol runtime _host_initialized REGISTERED eq_refl); exact COMPLETE.
Qed.

Theorem gateway_actual_runtime_cell_frame {World Event} (backend : gateway_backend World Event)
    runtime storage active complete depth before arguments after pool :
  gateway_runtime_registration runtime -> gateway_interpreter_result_shapes backend ->
  (forall object, storage object -> ~ gateway_private_cell (Clight.globalenv prog) object) ->
  Genv.find_symbol (Clight.globalenv prog) _host_initializing = Some active ->
  Genv.find_symbol (Clight.globalenv prog) _host_initialized = Some complete ->
  gateway_runtime_memory_scope (gateway_private_cell (Clight.globalenv prog)) before arguments ->
  gateway_runtime_memory_steps (Clight.globalenv prog) storage (gateway_source_callbacks backend runtime storage depth)
    before arguments after pool -> gateway_reentry_guard active complete before ->
  gateway_runtime_memory_scope (gateway_private_cell (Clight.globalenv prog)) after pool /\
  Mem.unchanged_on (fun object _ => gateway_private_cell (Clight.globalenv prog) object) before after.
Proof.
  intros REGISTERED SHAPES STORAGE ACTIVE COMPLETE READY RUN GUARD.
  destruct (gateway_runtime_memory_steps_origin (Clight.globalenv prog) storage _ _
    (gateway_reentry_guard active complete) before arguments after pool STORAGE
    (gateway_registered_callback_origin backend runtime storage active complete depth REGISTERED SHAPES STORAGE ACTIVE COMPLETE)
    (fun first last FRAME GUARD => gateway_reentry_guard_frame (Clight.globalenv prog) active complete
      first last ACTIVE COMPLETE FRAME GUARD) READY RUN) as [SCOPE FRAME].
  split; [exact SCOPE |apply FRAME; exact GUARD].
Qed.

Lemma gateway_private_pointer_cell_frame (ge : Clight.genv) identifier cell value before after :
  gateway_private_cell_name identifier = true -> Genv.find_symbol ge identifier = Some cell ->
  Mem.unchanged_on (fun object _ => gateway_private_cell ge object) before after ->
  Mem.load Mptr before cell 0 = Some value -> Mem.load Mptr after cell 0 = Some value.
Proof.
  intros PRIVATE SYMBOL FRAME LOAD; eapply Mem.load_unchanged_on; [exact FRAME | |exact LOAD].
  intros position RANGE; exists identifier; split; assumption.
Qed.

Theorem gateway_runtime_class_cell_current {World Event} (backend : gateway_backend World Event)
    runtime storage active complete depth before arguments after pool identifier cell class :
  gateway_runtime_registration runtime -> gateway_interpreter_result_shapes backend ->
  (forall object, storage object -> ~ gateway_private_cell (Clight.globalenv prog) object) ->
  Genv.find_symbol (Clight.globalenv prog) _host_initializing = Some active ->
  Genv.find_symbol (Clight.globalenv prog) _host_initialized = Some complete ->
  gateway_private_cell_name identifier = true -> Genv.find_symbol (Clight.globalenv prog) identifier = Some cell ->
  Mem.load Mptr before cell 0 = Some class ->
  gateway_runtime_memory_scope (gateway_private_cell (Clight.globalenv prog)) before arguments ->
  gateway_runtime_memory_steps (Clight.globalenv prog) storage (gateway_source_callbacks backend runtime storage depth)
    before arguments after pool -> gateway_reentry_guard active complete before ->
  Mem.load Mptr after cell 0 = Some class.
Proof.
  intros REGISTERED SHAPES STORAGE ACTIVE COMPLETE PRIVATE SYMBOL LOAD READY RUN GUARD.
  eapply gateway_private_pointer_cell_frame; [exact PRIVATE |exact SYMBOL | |exact LOAD].
  exact (proj2 (gateway_actual_runtime_cell_frame backend runtime storage active complete depth before arguments after pool
    REGISTERED SHAPES STORAGE ACTIVE COMPLETE READY RUN GUARD)).
Qed.
