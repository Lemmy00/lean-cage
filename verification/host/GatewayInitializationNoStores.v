(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Real guarded reentry has no own C stores on any prefix. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayInitializationSource GatewayInterpreterSource
  GatewayInitializationRejectionSource GatewayPublicInitializationBoundary GatewayRuntimeABI GatewayBindings
  GatewayNoStoreControl GatewayNoStoreAutomation GatewayReadOnlyBarrier GatewayFramedRuntime.
Import ListNotations.

Lemma gateway_initialization_denial_bindings ge :
  gateway_function_binding ge _PyErr_SetString gateway_set_error_definition ->
  gateway_readonly_bindings ge empty_env public_denial_api (Internal f_host_initialize).
Proof.
  intros [symbol [SYMBOL FUNCTION]] identifier ALLOWED; unfold public_denial_api in ALLOWED.
  apply Pos.eqb_eq in ALLOWED; subst identifier; split; [reflexivity |].
  exists symbol, gateway_set_error_definition; split; [exact SYMBOL |]. split; [exact FUNCTION |].
  split; [repeat eexists; reflexivity |discriminate].
Qed.

Ltac gateway_initialization_denial closed bindings :=
  eapply gateway_nostore_adapt with (original := fun _ _ => True);
    [exact closed |intros; exact I |];
  eapply gateway_readonly_selected_certificate with
    (allowed := public_denial_api) (denied := Internal f_host_initialize);
    [exact bindings |vm_compute; tauto |reflexivity].

Theorem gateway_initialization_active_no_stores {World Event} (backend : gateway_backend World Event)
    ge (property : mem -> World -> Prop) parameters memory active :
  gateway_ambient_closed backend property ->
  gateway_function_binding ge _PyErr_SetString gateway_set_error_definition ->
  Genv.find_symbol ge _host_initializing = Some active ->
  (forall memory world, property memory world -> Mem.load Mint32 memory active 0 = Some (Vint Int.one)) ->
  gateway_nostore_control backend ge property
    (Returnstate (Vlong Int64.zero) (gateway_interpreter_id_cont true parameters) memory).
Proof.
  intros CLOSED ERROR SYMBOL LOAD; pose proof (gateway_initialization_denial_bindings ge ERROR) as BINDINGS.
  gateway_nostore_dynamic CLOSED
    ltac:(fun _ => eapply initialization_global_word; [exact SYMBOL |eapply LOAD; eassumption])
    ltac:(fun _ => reflexivity) ltac:(fun _ => gateway_initialization_denial CLOSED BINDINGS).
Qed.

Theorem gateway_initialization_complete_no_stores {World Event} (backend : gateway_backend World Event)
    ge (property : mem -> World -> Prop) parameters memory active complete :
  gateway_ambient_closed backend property ->
  gateway_function_binding ge _PyErr_SetString gateway_set_error_definition ->
  Genv.find_symbol ge _host_initializing = Some active -> Genv.find_symbol ge _host_initialized = Some complete ->
  (forall memory world, property memory world -> Mem.load Mint32 memory active 0 = Some (Vint Int.zero)) ->
  (forall memory world, property memory world -> Mem.load Mint32 memory complete 0 = Some (Vint Int.one)) ->
  gateway_nostore_control backend ge property
    (Returnstate (Vlong Int64.zero) (gateway_interpreter_id_cont true parameters) memory).
Proof.
  intros CLOSED ERROR ACTIVE COMPLETE ACTIVE_LOAD COMPLETE_LOAD.
  pose proof (gateway_initialization_denial_bindings ge ERROR) as BINDINGS.
  gateway_nostore_dynamic CLOSED
    ltac:(fun _ => first [eapply initialization_global_word; [exact ACTIVE |eapply ACTIVE_LOAD; eassumption] |
      eapply initialization_global_word; [exact COMPLETE |eapply COMPLETE_LOAD; eassumption]])
    ltac:(fun _ => reflexivity) ltac:(fun _ => gateway_initialization_denial CLOSED BINDINGS).
Qed.

Theorem gateway_initialization_nonzero_no_stores {World Event} (backend : gateway_backend World Event)
    ge (property : mem -> World -> Prop) parameters memory identifier :
  gateway_ambient_closed backend property ->
  gateway_function_binding ge _PyErr_SetString gateway_set_error_definition -> identifier <> Int64.zero ->
  gateway_nostore_control backend ge property
    (Returnstate (Vlong identifier) (gateway_interpreter_id_cont true parameters) memory).
Proof.
  intros CLOSED ERROR NONZERO; pose proof (gateway_initialization_denial_bindings ge ERROR) as BINDINGS.
  assert (ZERO : Int64.eq identifier Int64.zero = false) by (apply Int64.eq_false; exact NONZERO).
  pose proof ZERO as ZERO_REPR; change (Int64.eq identifier (Int64.repr 0) = false) in ZERO_REPR.
  gateway_nostore_dynamic CLOSED ltac:(fun _ => fail)
    ltac:(fun _ => cbn -[Int64.eq];
      change (Int64.repr (Int.signed (Int.repr 0))) with Int64.zero;
      rewrite ?ZERO, ?ZERO_REPR; reflexivity)
    ltac:(fun _ => gateway_initialization_denial CLOSED BINDINGS).
Qed.
