(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: One public caller trace consumes the whole source bootstrap and retained references. *)
From Stdlib Require Import List.
From compcert Require Import Integers Values Memory Globalenvs Ctypes Clight.
Require Import Machine CallContexts.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayInitializationCaller GatewayInitializerPrepared
  GatewayInitializationEntrySource GatewayInitializationBootstrap GatewayInitializationContext GatewayInitializationRegions
  GatewayInterpreterRuntime GatewayBootstrapReference GatewayBootstrapReferenceScope GatewayBootstrapLoaderSetup GatewayBootstrapRuntime
  GatewayModuleRegions GatewayReferenceHistoryThreads GatewayReferenceThreads GatewayThreadRuntime GatewayLoaderRegions
  GatewayBootstrapRegions GatewayInitializerProtection GatewayBootstrapFlagged.
Import ListNotations.

Theorem gateway_actual_public_bootstrap_connection {World Event} (backend : gateway_backend World Event)
    io native stable base thread_errno heap_allocation python objects current identifier
    module_filename canonicalizes
    (threads : gateway_thread_runtime backend io native stable base thread_errno)
    (reference_threads : gateway_reference_thread_contract backend native stable base heap_allocation python objects)
    (interpreter : gateway_interpreter_runtime backend io native stable base python objects current identifier)
    (runtime : gateway_bootstrap_runtime backend io native stable base module_filename canonicalizes)
    (profile : gateway_bootstrap_python_profile native base python objects)
    (references : gateway_bootstrap_reference_runtime backend python objects)
    decimal_float ledger retired held before world events value after next :
  gateway_native_loader_boundary (Clight.globalenv prog) before ->
  gateway_native_readonly_mapping (Clight.globalenv prog) before ->
  gateway_native_storage_boundary native (Clight.globalenv prog) before world -> base None before world ->
  gateway_reference_history_scope python objects decimal_float ledger retired held world ->
  gateway_steps backend (Clight.globalenv prog)
    (gateway_live (Callstate (Internal f_PyInit__host) [] Kstop before) world) events
    (gateway_live (Returnstate value Kstop after) next) -> value <> Vnullptr ->
  identifier world = Int64.zero /\
  exists symbols entry parameters outer_parameters prefix bootstrap suffix called called_world changed changed_world,
    events = prefix ++ bootstrap ++ suffix /\
    gateway_steps backend (Clight.globalenv prog)
      (gateway_live (Callstate (Internal f_PyInit__host) [] Kstop before) world) prefix
      (gateway_live (Callstate (Internal f_host_bootstrap) []
        (plug_cont (initializer_bootstrap_cont parameters) (initialization_body_cont outer_parameters)) called) called_world) /\
    gateway_steps backend (Clight.globalenv prog)
      (gateway_live (Callstate (Internal f_host_bootstrap) [] Kstop called) called_world) bootstrap
      (gateway_live (Returnstate (Vint Int.zero) Kstop changed) changed_world) /\
    gateway_steps backend (Clight.globalenv prog)
      (gateway_live (Returnstate (Vint Int.zero)
        (plug_cont (initializer_bootstrap_cont parameters) (initialization_body_cont outer_parameters)) changed) changed_world) suffix
      (gateway_live (Returnstate value Kstop after) next) /\
    Genv.find_symbol (Clight.globalenv prog) _PyInit__host = Some entry /\
    gateway_bootstrap_named_paths native base module_filename canonicalizes entry
      (initialization_root symbols) (initialization_engine symbols) (initialization_results symbols) changed changed_world /\
    gateway_module_descriptor_regions (Clight.globalenv prog) changed /\
    gateway_reference_history_scope python objects decimal_float ledger retired held changed_world /\
    gateway_initialization_flag_state native base symbols Int.one Int.zero changed changed_world.
Proof.
  intros LOADER READONLY STORAGE SIDE HISTORY RUN NONNULL.
  destruct (gateway_actual_loaded_initialization_body backend io native stable base thread_errno heap_allocation python objects current identifier
    threads reference_threads interpreter decimal_float ledger retired held before world events value after next LOADER READONLY STORAGE SIDE HISTORY RUN NONNULL)
    as [MAIN (symbols & outer_prefix & body & outer_suffix & outer_parameters & body_before & body_world & returned & body_after & body_next &
      EVENTS0 & OUTER_PREFIX & CONTEXT & BODY & BODY_NONNULL & OUTER_REST)].
  destruct (gateway_actual_initializer_prepared_bootstrap backend io native stable base thread_errno heap_allocation python objects current identifier
    module_filename canonicalizes threads reference_threads interpreter runtime profile references symbols before Int.one Int.zero
    decimal_float ledger retired held (current world) (identifier world) body_before body_world body returned body_after body_next CONTEXT BODY BODY_NONNULL)
    as (inner_prefix & bootstrap & inner_suffix & parameters & called & called_world & changed & changed_world & entry &
      EVENTS1 & INNER_PREFIX & BOOTSTRAP & INNER_REST & ENTRY & PATHS & DESCRIPTORS & FINAL_HISTORY & FLAGS).
  split; [exact MAIN |].
  exists symbols, entry, parameters, outer_parameters, (outer_prefix ++ inner_prefix), bootstrap, (inner_suffix ++ outer_suffix),
    called, called_world, changed, changed_world.
  split; [rewrite EVENTS0, EVENTS1; repeat rewrite app_assoc; reflexivity |]. split.
  - eapply gateway_steps_append; [exact OUTER_PREFIX |].
    exact (gateway_plug_steps backend (Clight.globalenv prog) _ _ _ (initialization_body_cont outer_parameters) I INNER_PREFIX).
  - split; [exact BOOTSTRAP |]. split.
    + eapply gateway_steps_append; [|exact OUTER_REST].
      exact (gateway_plug_steps backend (Clight.globalenv prog) _ _ _ (initialization_body_cont outer_parameters) I INNER_REST).
    + split; [exact ENTRY |]. split; [exact PATHS |]. split; [exact DESCRIPTORS |]. split; assumption.
Qed.
