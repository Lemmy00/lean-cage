(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Earlier source stores retain only the regions bootstrap actually needs. *)
From Stdlib Require Import List.
From compcert Require Import Integers Values Memory Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewayLoaderRegions GatewayModuleRegions
  GatewayBootstrapRegions GatewayBootstrapGuarantee GatewayBootstrapLoaderSetup GatewayBootstrapBuffers GatewayBootstrapRuntime
  GatewayThreadRuntime GatewayProtectedMemory GatewayProtectedThreads GatewayProtectedBootstrap GatewayInitializerProtection
  GatewayReferenceHistoryThreads GatewayReferenceThreads GatewayBootstrapHistory GatewayBootstrapReferenceScope GatewayBootstrapReference.

Theorem actual_prepared_bootstrap_descriptors {World Event} (backend : gateway_backend World Event)
    io native stable base thread_errno module_filename canonicalizes
    (threads : gateway_thread_runtime backend io native stable base thread_errno)
    (runtime : gateway_bootstrap_runtime backend io native stable base module_filename canonicalizes)
    entry root engine results suffix executable results_literal before world events after next :
  Genv.find_symbol (Clight.globalenv prog) _PyInit__host = Some entry ->
  Genv.find_symbol (Clight.globalenv prog) _host_root = Some root ->
  Genv.find_symbol (Clight.globalenv prog) _host_engine = Some engine ->
  Genv.find_symbol (Clight.globalenv prog) _host_default_results = Some results ->
  Genv.find_symbol (Clight.globalenv prog) _suffix = Some suffix ->
  Genv.find_symbol (Clight.globalenv prog) _executable = Some executable ->
  Genv.find_symbol (Clight.globalenv prog) _results = Some results_literal ->
  gateway_module_descriptor_regions (Clight.globalenv prog) before ->
  gateway_protected_memory native (gateway_descriptor_object (Clight.globalenv prog))
    (gateway_immutable_object (Clight.globalenv prog)) before before world ->
  gateway_bootstrap_buffers native stable base (bootstrap_loaded_capacities root engine results suffix executable results_literal)
    (bootstrap_loaded_literals suffix executable results_literal) before world ->
  gateway_steps backend (Clight.globalenv prog)
    (gateway_live (Callstate (Internal f_host_bootstrap) nil Kstop before) world) events
    (gateway_live (Returnstate (Vint Int.zero) Kstop after) next) ->
  gateway_bootstrap_named_paths native base module_filename canonicalizes entry root engine results after next /\
  gateway_module_descriptor_regions (Clight.globalenv prog) after /\
  Mem.unchanged_on (fun object _ => gateway_descriptor_object (Clight.globalenv prog) object) before after.
Proof.
  intros ENTRY ROOT ENGINE RESULTS SUFFIX EXECUTABLE RESULTS_LITERAL DESCRIPTORS STATE BUFFERS RUN.
  pose proof (gateway_bootstrap_protected_inputs native stable base root engine results suffix executable results_literal
    before world ROOT ENGINE RESULTS SUFFIX EXECUTABLE RESULTS_LITERAL STATE BUFFERS) as INPUT.
  pose proof (actual_bootstrap_call_return backend io
    (gateway_protected_native native (gateway_descriptor_object (Clight.globalenv prog)) (gateway_immutable_object (Clight.globalenv prog)))
    stable (gateway_protected_discipline base native (gateway_descriptor_object (Clight.globalenv prog))
      (gateway_immutable_object (Clight.globalenv prog)) before)
    thread_errno module_filename canonicalizes
    (gateway_protected_threads backend io native stable base thread_errno threads
      (gateway_descriptor_object (Clight.globalenv prog)) (gateway_immutable_object (Clight.globalenv prog)) before)
    (gateway_protected_bootstrap backend io native stable base module_filename canonicalizes runtime
      (gateway_descriptor_object (Clight.globalenv prog)) (gateway_immutable_object (Clight.globalenv prog)) before)
    entry root engine results suffix executable results_literal ENTRY ROOT ENGINE RESULTS SUFFIX EXECUTABLE RESULTS_LITERAL
    before world events after next INPUT RUN) as RESULT.
  destruct (gateway_bootstrap_named_unprotect native base (gateway_descriptor_object (Clight.globalenv prog))
    (gateway_immutable_object (Clight.globalenv prog)) before module_filename canonicalizes
    entry root engine results after next RESULT) as [PATHS FINAL].
  split; [exact PATHS |]. split.
  - eapply gateway_protected_descriptors; [exact DESCRIPTORS |exact FINAL].
  - exact (gateway_protected_snapshot _ _ _ _ _ _ FINAL).
Qed.

Theorem actual_prepared_bootstrap_history {World Event} (backend : gateway_backend World Event)
    io native stable base thread_errno heap_allocation module_filename canonicalizes
    python objects decimal_float ledger retired held
    (threads : gateway_thread_runtime backend io native stable base thread_errno)
    (runtime : gateway_bootstrap_runtime backend io native stable base module_filename canonicalizes)
    (profile : gateway_bootstrap_python_profile native base python objects)
    (reference_threads : gateway_reference_thread_contract backend native stable base heap_allocation python objects)
    (references : gateway_bootstrap_reference_runtime backend python objects)
    entry root engine results suffix executable results_literal before world events after next :
  Genv.find_symbol (Clight.globalenv prog) _PyInit__host = Some entry ->
  Genv.find_symbol (Clight.globalenv prog) _host_root = Some root ->
  Genv.find_symbol (Clight.globalenv prog) _host_engine = Some engine ->
  Genv.find_symbol (Clight.globalenv prog) _host_default_results = Some results ->
  Genv.find_symbol (Clight.globalenv prog) _suffix = Some suffix ->
  Genv.find_symbol (Clight.globalenv prog) _executable = Some executable ->
  Genv.find_symbol (Clight.globalenv prog) _results = Some results_literal ->
  gateway_module_descriptor_regions (Clight.globalenv prog) before ->
  gateway_protected_memory native (gateway_descriptor_object (Clight.globalenv prog))
    (gateway_immutable_object (Clight.globalenv prog)) before before world ->
  gateway_bootstrap_buffers native stable base (bootstrap_loaded_capacities root engine results suffix executable results_literal)
    (bootstrap_loaded_literals suffix executable results_literal) before world ->
  gateway_reference_history_scope python objects decimal_float ledger retired held world ->
  gateway_steps backend (Clight.globalenv prog)
    (gateway_live (Callstate (Internal f_host_bootstrap) nil Kstop before) world) events
    (gateway_live (Returnstate (Vint Int.zero) Kstop after) next) ->
  gateway_bootstrap_named_paths native base module_filename canonicalizes entry root engine results after next /\
  gateway_module_descriptor_regions (Clight.globalenv prog) after /\
  gateway_reference_history_scope python objects decimal_float ledger retired held next /\
  Mem.unchanged_on (fun object _ => gateway_descriptor_object (Clight.globalenv prog) object) before after.
Proof.
  intros ENTRY ROOT ENGINE RESULTS SUFFIX EXECUTABLE RESULTS_LITERAL DESCRIPTORS STATE [SIDE BUFFERS] HISTORY RUN.
  set (extended := fun mode memory current => base mode memory current /\
    gateway_reference_history_scope python objects decimal_float ledger retired held current).
  assert (THREADS : gateway_thread_runtime backend io native stable extended thread_errno).
  { apply gateway_thread_with_reference_history with (heap_allocation := heap_allocation);
      [exact reference_threads |exact threads]. }
  assert (RUNTIME : gateway_bootstrap_runtime backend io native stable extended module_filename canonicalizes).
  { apply gateway_bootstrap_with_reference_history; assumption. }
  destruct (actual_prepared_bootstrap_descriptors backend io native stable extended thread_errno module_filename canonicalizes THREADS RUNTIME
    entry root engine results suffix executable results_literal before world events after next
    ENTRY ROOT ENGINE RESULTS SUFFIX EXECUTABLE RESULTS_LITERAL DESCRIPTORS STATE (conj (conj SIDE HISTORY) BUFFERS) RUN)
    as [PATHS [FINAL_DESCRIPTORS FRAME]].
  destruct (gateway_bootstrap_named_discipline native extended base module_filename canonicalizes
    entry root engine results after next ltac:(intros mode memory current [BASE INVARIANT]; exact BASE) PATHS)
    as [[FINAL_BASE FINAL_HISTORY] FINAL_PATHS].
  split; [exact FINAL_PATHS |]. split; [exact FINAL_DESCRIPTORS |]. split; assumption.
Qed.
