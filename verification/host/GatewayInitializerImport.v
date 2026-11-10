(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: The actual initializer imports and owns its module
   reference. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayInitializationBootstrap GatewayInitializerObjectsSource
  GatewayInitializerObjectFailures GatewayInitializerObjectLiterals GatewayInitializerSDK
  GatewaySourcePaths GatewayFramedRuntime GatewayBindings GatewayExternalFrontier GatewayOperations
  GatewayContexts GatewayModuleRegions GatewayPython GatewayObjects GatewayReferenceRuntime GatewayRuntime.
Import ListNotations.

Theorem gateway_actual_initializer_import {World Event} (backend : gateway_backend World Event)
    python objects normal attached module_descriptor exported
    (sdk : gateway_initializer_sdk backend python objects normal attached module_descriptor exported)
    (property : mem -> World -> Prop) parameters before world events value after next :
  gateway_ambient_closed backend property ->
  (forall memory world, property memory world -> normal memory world /\
    gateway_module_descriptor_regions (Clight.globalenv prog) memory) ->
  property before world ->
  gateway_steps backend (Clight.globalenv prog)
    (gateway_live (Returnstate (Vint Int.zero) (initializer_bootstrap_cont parameters) before) world) events
    (gateway_live (Returnstate value Kstop after) next) -> value <> Vnullptr ->
  exists prefix pending suffix called_parameters name memory called_world result changed changed_world observed,
    events = prefix ++ pending ++ gateway_primitive observed :: suffix /\
    Forall (fun event => event = gateway_source E0 \/ event = gateway_ambient) prefix /\
    Forall gateway_pending_event pending /\
    Genv.find_symbol (Clight.globalenv prog) ___stringlit_127 = Some name /\
    gateway_steps backend (Clight.globalenv prog)
      (gateway_live (Returnstate (Vint Int.zero) (initializer_bootstrap_cont parameters) before) world)
      (prefix ++ pending)
      (gateway_live (Callstate initializer_import_definition [Vptr name Ptrofs.zero]
        (initializer_import_cont called_parameters) memory) called_world) /\
    property memory called_world /\
    gateway_runtime_operation backend initializer_import_definition [Vptr name Ptrofs.zero]
      memory called_world result changed changed_world observed /\
    result <> Vnullptr /\ normal changed changed_world /\
    gateway_reference_credit (python called_world) (python changed_world) result /\
    gateway_rooted (python changed_world) (objects changed_world) result /\
    gateway_steps backend (Clight.globalenv prog)
      (gateway_live (Returnstate result (initializer_import_cont called_parameters) changed) changed_world) suffix
      (gateway_live (Returnstate value Kstop after) next).
Proof.
  intros CLOSED READY INPUT RUN NONNULL.
  assert (BINDING : gateway_function_binding (Clight.globalenv prog) _PyImport_ImportModule initializer_import_definition)
    by (apply gateway_actual_function_binding; vm_compute; reflexivity).
  destruct BINDING as (symbol & SYMBOL & FUNCTION).
  assert (NAME : exists name, Genv.find_symbol (Clight.globalenv prog) ___stringlit_127 = Some name)
    by (eexists; vm_compute; reflexivity).
  destruct NAME as (name & NAME).
  destruct (gateway_initializer_import_source backend (Clight.globalenv prog) property parameters before symbol name
    CLOSED SYMBOL FUNCTION NAME) as (called_parameters & SOURCE & TEMPS).
  destruct (gateway_source_path_cut backend (Clight.globalenv prog) _ _ _ _ _ _ SOURCE before world events value after next INPUT RUN)
    as (prefix & rest & called & current & EVENTS & QUIET & PREFIX & CALLED & REST).
  destruct (gateway_actual_external_frontier backend (Clight.globalenv prog) _ _ _ _ _
    (initializer_import_cont called_parameters) called current rest value after next I ltac:(cbn; lia) REST)
    as (pending & suffix & memory & called_world & result & changed & changed_world & observed & TAIL & PENDING & WAITING & OPERATION & SUFFIX).
  assert (AT_CALL : property memory called_world).
  { eapply (gateway_pending_run_ready backend (Clight.globalenv prog) property CLOSED
      (Callstate initializer_import_definition [Vptr name Ptrofs.zero] (initializer_import_cont called_parameters) called)
      called current pending memory called_world); [exact CALLED |exact PENDING |exact WAITING]. }
  assert (RESULT : result <> Vnullptr).
  { intro NULL; subst result; apply NONNULL.
    eapply (gateway_initializer_import_failed backend (Clight.globalenv prog) (fun _ _ => True)
      called_parameters changed ltac:(unfold gateway_ambient_closed; intros; exact I)); [exact I |exact SUFFIX]. }
  destruct (READY memory called_world AT_CALL) as (NORMAL & REGIONS).
  assert (STRING : GatewayErrorRuntime.gateway_error_cstring memory (Vptr name Ptrofs.zero)
    (map Byte.repr [112; 97; 116; 104; 108; 105; 98])).
  { eapply gateway_initializer_object_name_bytes with (identifier := ___stringlit_127);
      [exact REGIONS |left; reflexivity |exact NAME]. }
  destruct (gateway_initializer_import_effect _ _ _ _ _ _ _ sdk memory called_world
    (Vptr name Ptrofs.zero) _ result changed changed_world observed NORMAL STRING OPERATION)
    as (ATTACHED & [(NULL & COUNTS) |(NEXT_NORMAL & CREDIT & ROOT)]); [contradiction |].
  exists prefix, pending, suffix, called_parameters, name, memory, called_world, result, changed, changed_world, observed.
  split; [rewrite EVENTS, TAIL; reflexivity |]. split; [exact QUIET |]. split; [exact PENDING |].
  split; [exact NAME |]. split.
  - eapply gateway_steps_append; eassumption.
  - exact (conj AT_CALL (conj OPERATION (conj RESULT (conj NEXT_NORMAL (conj CREDIT (conj ROOT SUFFIX)))))).
Qed.
