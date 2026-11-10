(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: The actual private initializer consumes retained current regions, not a new loader boundary. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayInterpreterSource GatewayInterpreterRuntime
  GatewayInitializationInterpreter GatewayInitializationContext GatewayInitializationRegions GatewayInitializationBootstrap
  GatewaySourceBoundCalls GatewaySourcePaths GatewaySourceSegmentAutomation GatewayFramedRuntime GatewayBindings
  GatewayBootstrapFlagged GatewayBootstrapReference GatewayBootstrapReferenceScope GatewayBootstrapLoaderSetup GatewayBootstrapRuntime
  GatewayBootstrapBuffers GatewayInitializerProtection GatewayProtectedMemory GatewayModuleRegions
  GatewayReferenceThreads GatewayReferenceHistoryThreads GatewayThreadRuntime GatewayReturns GatewayReturnTypes GatewayNoLocalEntry.
Import ListNotations.

Theorem gateway_initializer_zero_to_bootstrap {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) parameters memory symbol :
  gateway_ambient_closed backend property -> Genv.find_symbol ge _host_bootstrap = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some (Internal f_host_bootstrap) ->
  exists called_parameters,
    gateway_source_path backend ge (Internal f_host_bootstrap) [] (initializer_bootstrap_cont called_parameters) property
      (Returnstate (Vlong Int64.zero) (gateway_interpreter_id_cont false parameters) memory) property.
Proof.
  intros CLOSED SYMBOL FUNCTION; eexists.
  gateway_bound_source_call CLOSED ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
  eapply gateway_source_same with (target := Callstate (Internal f_host_bootstrap) [] (initializer_bootstrap_cont _) memory).
  - exact CLOSED.
  - cbn; tauto.
  - intros; eapply actual_initializer_bootstrap_call_edge with (symbol := symbol); assumption.
  - apply gateway_source_reached; auto.
Qed.

Theorem gateway_actual_initializer_prepared_bootstrap {World Event} (backend : gateway_backend World Event)
    io native stable base thread_errno heap_allocation python objects current identifier
    module_filename canonicalizes
    (threads : gateway_thread_runtime backend io native stable base thread_errno)
    (reference_threads : gateway_reference_thread_contract backend native stable base heap_allocation python objects)
    (interpreter : gateway_interpreter_runtime backend io native stable base python objects current identifier)
    (runtime : gateway_bootstrap_runtime backend io native stable base module_filename canonicalizes)
    (profile : gateway_bootstrap_python_profile native base python objects)
    (references : gateway_bootstrap_reference_runtime backend python objects)
    symbols snapshot active complete decimal_float ledger retired held pointer number before world events value after next :
  gateway_initialization_context native stable base symbols snapshot active complete
    python objects decimal_float ledger retired held current identifier pointer number before world ->
  gateway_steps backend (Clight.globalenv prog)
    (gateway_live (Callstate (Internal f_host_initialize) [] Kstop before) world) events
    (gateway_live (Returnstate value Kstop after) next) -> value <> Vnullptr ->
  exists prefix bootstrap suffix parameters called called_world changed changed_world entry,
    events = prefix ++ bootstrap ++ suffix /\
    gateway_steps backend (Clight.globalenv prog)
      (gateway_live (Callstate (Internal f_host_initialize) [] Kstop before) world) prefix
      (gateway_live (Callstate (Internal f_host_bootstrap) [] (initializer_bootstrap_cont parameters) called) called_world) /\
    gateway_steps backend (Clight.globalenv prog)
      (gateway_live (Callstate (Internal f_host_bootstrap) [] Kstop called) called_world) bootstrap
      (gateway_live (Returnstate (Vint Int.zero) Kstop changed) changed_world) /\
    gateway_steps backend (Clight.globalenv prog)
      (gateway_live (Returnstate (Vint Int.zero) (initializer_bootstrap_cont parameters) changed) changed_world) suffix
      (gateway_live (Returnstate value Kstop after) next) /\
    Genv.find_symbol (Clight.globalenv prog) _PyInit__host = Some entry /\
    gateway_bootstrap_named_paths native base module_filename canonicalizes entry
      (initialization_root symbols) (initialization_engine symbols) (initialization_results symbols) changed changed_world /\
    gateway_module_descriptor_regions (Clight.globalenv prog) changed /\
    gateway_reference_history_scope python objects decimal_float ledger retired held changed_world /\
    gateway_initialization_flag_state native base symbols active complete changed changed_world.
Proof.
  intros INPUT RUN NONNULL.
  set (property := gateway_initialization_context native stable base symbols snapshot active complete
    python objects decimal_float ledger retired held current identifier pointer number).
  assert (CLOSED : gateway_ambient_closed backend property).
  { eapply gateway_initialization_context_ambient; eassumption. }
  destruct (gateway_actual_no_local_entry backend (Clight.globalenv prog) f_host_initialize [] property before world events value after next
    eq_refl CLOSED INPUT RUN) as (p0 & rest0 & entered & entry_world & parameters & EVENTS0 & PREFIX0 & READY0 & BODY).
  destruct (gateway_actual_initialization_interpreter backend io native stable base thread_errno heap_allocation python objects current identifier
    threads reference_threads interpreter symbols snapshot active complete decimal_float ledger retired held pointer number false parameters
    entered entry_world rest0 value after next READY0 BODY NONNULL)
    as [MAIN (p1 & rest1 & checked & checked_world & EVENTS1 & PREFIX1 & READY1 & AFTER_CHECK)].
  assert (BOOTSTRAP_BINDING : gateway_function_binding (Clight.globalenv prog) _host_bootstrap (Internal f_host_bootstrap))
    by (apply gateway_actual_function_binding; vm_compute; reflexivity).
  destruct BOOTSTRAP_BINDING as [symbol [SYMBOL FUNCTION]].
  destruct (gateway_initializer_zero_to_bootstrap backend (Clight.globalenv prog) property (PTree.set _t'1 pointer parameters) checked symbol
    CLOSED SYMBOL FUNCTION) as [bootstrap_parameters PATH].
  destruct (gateway_source_path_cut backend (Clight.globalenv prog) _ _ _ _ _ _ PATH checked checked_world rest1 value after next READY1 AFTER_CHECK)
    as (p2 & rest2 & called & called_world & EVENTS2 & QUIET2 & PREFIX2 & CALLED & FROM_BOOTSTRAP).
  destruct (gateway_return_cut backend (Clight.globalenv prog) (Internal f_host_bootstrap) []
    (initializer_bootstrap_cont bootstrap_parameters) called called_world rest2 (Returnstate value Kstop after) next I ltac:(cbn; lia) FROM_BOOTSTRAP)
    as (bootstrap & suffix & returned & changed & changed_world & EVENTS3 & BOOTSTRAP & REST).
  pose proof (gateway_actual_int_return backend (Clight.globalenv prog) f_host_bootstrap [] called called_world bootstrap returned changed changed_world
    actual_bootstrap_integer_profile BOOTSTRAP) as RETURN_TYPE.
  pose proof (actual_initializer_derives_bootstrap_zero backend (Clight.globalenv prog) bootstrap_parameters changed changed_world suffix returned value
    after next RETURN_TYPE NONNULL REST) as ZERO; subst returned.
  destruct CALLED as [REGIONS [HISTORY [CURRENT IDENTIFIER]]].
  assert (ENTRY_BINDING : gateway_function_binding (Clight.globalenv prog) _PyInit__host (Internal f_PyInit__host))
    by (apply gateway_actual_function_binding; vm_compute; reflexivity).
  destruct ENTRY_BINDING as [entry [ENTRY ENTRY_FUNCTION]].
  destruct (gateway_actual_bootstrap_flagged backend io native stable base thread_errno heap_allocation module_filename canonicalizes
    python objects decimal_float ledger retired held threads runtime profile reference_threads references symbols snapshot active complete entry
    called called_world bootstrap changed changed_world ENTRY REGIONS HISTORY BOOTSTRAP)
    as [PATHS [FINAL_DESCRIPTORS [FINAL_HISTORY FLAGS]]].
  exists (p0 ++ p1 ++ p2), bootstrap, suffix, bootstrap_parameters, called, called_world, changed, changed_world, entry.
  split; [rewrite EVENTS0, EVENTS1, EVENTS2, EVENTS3; repeat rewrite app_assoc; reflexivity |]. split.
  - eapply gateway_steps_append; [exact PREFIX0 |]. eapply gateway_steps_append; [exact PREFIX1 |exact PREFIX2].
  - split; [exact BOOTSTRAP |]. split; [exact REST |]. split; [exact ENTRY |]. split; [exact PATHS |].
    split; [exact FINAL_DESCRIPTORS |]. split; assumption.
Qed.
