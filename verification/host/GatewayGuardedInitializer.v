(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Original reentry excludes own stores before any return. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayInterpreterSource GatewayBindings GatewayRuntimeABI
  GatewayNoStoreControl GatewayNoStoreEntry GatewayInitializationNoStores GatewayInitializationQueryControl
  GatewayFramedRuntime.
Import ListNotations.

Theorem gateway_active_initializer_no_stores {World Event} (backend : gateway_backend World Event)
    ge (property : mem -> World -> Prop) memory active :
  gateway_ambient_closed backend property -> gateway_initialization_query_laws backend property ->
  gateway_function_binding ge _PyInterpreterState_Get gateway_interpreter_get_definition ->
  gateway_function_binding ge _PyInterpreterState_GetID gateway_interpreter_id_definition ->
  gateway_function_binding ge _PyErr_SetString gateway_set_error_definition ->
  Genv.find_symbol ge _host_initializing = Some active ->
  (forall memory world, property memory world -> Mem.load Mint32 memory active 0 = Some (Vint Int.one)) ->
  gateway_nostore_control backend ge property (Callstate (Internal f_PyInit__host) [] Kstop memory).
Proof.
  intros CLOSED QUERIES GET ID ERROR SYMBOL LOAD.
  apply gateway_nostore_local_free_entry; [reflexivity |exact CLOSED |].
  intros parameters before; eapply gateway_initialization_queries_no_stores; try eassumption.
  intros changed after identifier; destruct (Int64.eq_dec identifier Int64.zero) as [ZERO |NONZERO].
  - subst identifier; eapply gateway_initialization_active_no_stores; eassumption.
  - eapply gateway_initialization_nonzero_no_stores; eassumption.
Qed.

Theorem gateway_complete_initializer_no_stores {World Event} (backend : gateway_backend World Event)
    ge (property : mem -> World -> Prop) memory active complete :
  gateway_ambient_closed backend property -> gateway_initialization_query_laws backend property ->
  gateway_function_binding ge _PyInterpreterState_Get gateway_interpreter_get_definition ->
  gateway_function_binding ge _PyInterpreterState_GetID gateway_interpreter_id_definition ->
  gateway_function_binding ge _PyErr_SetString gateway_set_error_definition ->
  Genv.find_symbol ge _host_initializing = Some active -> Genv.find_symbol ge _host_initialized = Some complete ->
  (forall memory world, property memory world -> Mem.load Mint32 memory active 0 = Some (Vint Int.zero)) ->
  (forall memory world, property memory world -> Mem.load Mint32 memory complete 0 = Some (Vint Int.one)) ->
  gateway_nostore_control backend ge property (Callstate (Internal f_PyInit__host) [] Kstop memory).
Proof.
  intros CLOSED QUERIES GET ID ERROR ACTIVE COMPLETE ACTIVE_LOAD COMPLETE_LOAD.
  apply gateway_nostore_local_free_entry; [reflexivity |exact CLOSED |].
  intros parameters before; eapply gateway_initialization_queries_no_stores; try eassumption.
  intros changed after identifier; destruct (Int64.eq_dec identifier Int64.zero) as [ZERO |NONZERO].
  - subst identifier; eapply gateway_initialization_complete_no_stores; eassumption.
  - eapply gateway_initialization_nonzero_no_stores; eassumption.
Qed.

(* The source safety conclusion applies to EVERY finite live prefix. This
   includes a pending query, a pending error API and all interleaved callbacks;
   loss is already admitted by gateway_nostore_prefix. *)
Theorem gateway_guarded_initializer_prefix {World Event} (backend : gateway_backend World Event)
    ge (property : mem -> World -> Prop) before world events source next :
  property before world ->
  gateway_nostore_control backend ge property (Callstate (Internal f_PyInit__host) [] Kstop before) ->
  gateway_steps backend ge (gateway_live (Callstate (Internal f_PyInit__host) [] Kstop before) world)
    events (gateway_live source next) -> gateway_not_assignment source.
Proof.
  intros READY CONTROL RUN; apply (gateway_nostore_current backend ge source next).
  eapply (gateway_nostore_prefix backend ge
    (gateway_live (Callstate (Internal f_PyInit__host) [] Kstop before) world)
    events (gateway_live source next)); [exists property; split; [exact READY |exact CONTROL] |exact RUN].
Qed.
