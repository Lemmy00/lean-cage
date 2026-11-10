(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: The real initializer's guard consumes the source bootstrap history guarantee. *)
From Stdlib Require Import List Lia.
From compcert Require Import Integers Values Memory Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayReturns GatewayReturnTypes GatewayInitializationBootstrap
  GatewayBootstrapHistory GatewayBootstrapRuntime GatewayBootstrapLoaderSetup GatewayBootstrapRegions GatewayLoaderRegions
  GatewayModuleRegions GatewayInitializerProtection GatewayThreadRuntime GatewayReferenceHistoryThreads
  GatewayReferenceThreads GatewayBootstrapReferenceScope GatewayBootstrapReference.
Import ListNotations.

Theorem actual_initializer_bootstrap_reference_history {World Event} (backend : gateway_backend World Event)
    io native stable base thread_errno heap_allocation module_filename canonicalizes
    python objects decimal_float ledger retired held
    (threads : gateway_thread_runtime backend io native stable base thread_errno)
    (runtime : gateway_bootstrap_runtime backend io native stable base module_filename canonicalizes)
    (profile : gateway_bootstrap_python_profile native base python objects)
    (reference_threads : gateway_reference_thread_contract backend native stable base heap_allocation python objects)
    (references : gateway_bootstrap_reference_runtime backend python objects)
    temporaries before world events value after next :
  gateway_native_loader_boundary (Clight.globalenv prog) before ->
  gateway_native_readonly_mapping (Clight.globalenv prog) before ->
  gateway_native_storage_boundary native (Clight.globalenv prog) before world ->
  base None before world ->
  gateway_reference_history_scope python objects decimal_float ledger retired held world ->
  value <> Vnullptr ->
  gateway_steps backend (Clight.globalenv prog)
    (gateway_live (Callstate (Internal f_host_bootstrap) [] (initializer_bootstrap_cont temporaries) before) world) events
    (gateway_live (Returnstate value Kstop after) next) ->
  exists prefix rest memory current entry root engine results,
    events = prefix ++ rest /\
    gateway_steps backend (Clight.globalenv prog)
      (gateway_live (Callstate (Internal f_host_bootstrap) [] Kstop before) world) prefix
      (gateway_live (Returnstate (Vint Int.zero) Kstop memory) current) /\
    gateway_steps backend (Clight.globalenv prog)
      (gateway_live (Returnstate (Vint Int.zero) (initializer_bootstrap_cont temporaries) memory) current) rest
      (gateway_live (Returnstate value Kstop after) next) /\
    Genv.find_symbol (Clight.globalenv prog) _PyInit__host = Some entry /\
    Genv.find_symbol (Clight.globalenv prog) _host_root = Some root /\
    Genv.find_symbol (Clight.globalenv prog) _host_engine = Some engine /\
    Genv.find_symbol (Clight.globalenv prog) _host_default_results = Some results /\
    gateway_bootstrap_named_paths native base module_filename canonicalizes entry root engine results memory current /\
    gateway_module_descriptor_regions (Clight.globalenv prog) memory /\
    gateway_reference_history_scope python objects decimal_float ledger retired held current /\
    Mem.unchanged_on (fun object _ => gateway_descriptor_object (Clight.globalenv prog) object) before memory.
Proof.
  intros LOADER READONLY STORAGE SIDE HISTORY NONNULL RUN.
  destruct (gateway_return_cut backend (Clight.globalenv prog) (Internal f_host_bootstrap) []
    (initializer_bootstrap_cont temporaries) before world events (Returnstate value Kstop after) next I ltac:(cbn; lia) RUN)
    as (prefix & rest & returned & memory & current & EVENTS & BOOTSTRAP & REST).
  pose proof (gateway_actual_int_return backend (Clight.globalenv prog) f_host_bootstrap [] before world prefix returned memory current
    actual_bootstrap_integer_profile BOOTSTRAP) as TYPE.
  pose proof (actual_initializer_derives_bootstrap_zero backend (Clight.globalenv prog) temporaries memory current rest returned
    value after next TYPE NONNULL REST) as ZERO; subst returned.
  destruct (actual_loaded_bootstrap_reference_history backend io native stable base thread_errno heap_allocation module_filename canonicalizes
    python objects decimal_float ledger retired held threads runtime profile reference_threads references
    before world prefix memory current LOADER READONLY STORAGE SIDE HISTORY BOOTSTRAP)
    as (entry & root & engine & results & ENTRY & ROOT & ENGINE & RESULTS & PATHS & DESCRIPTORS & FINAL_HISTORY & FRAME).
  exists prefix, rest, memory, current, entry, root, engine, results.
  split; [exact EVENTS |]. split; [exact BOOTSTRAP |]. split; [exact REST |].
  split; [exact ENTRY |]. split; [exact ROOT |]. split; [exact ENGINE |]. split; [exact RESULTS |].
  split; [exact PATHS |]. split; [exact DESCRIPTORS |]. split; assumption.
Qed.
