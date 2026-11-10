(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: The whole actual bootstrap retains initialized descriptor regions. *)
From Stdlib Require Import List.
From compcert Require Import Integers Values Memory Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewayLoaderRegions
  GatewayModuleRegions GatewayBootstrapRegions GatewayBootstrapGuarantee GatewayBootstrapLoaderSetup
  GatewayBootstrapBuffers GatewayBootstrapRuntime GatewayThreadRuntime GatewayProtectedMemory GatewayProtectedThreads
  GatewayProtectedBootstrap GatewayInitializerProtection.

Theorem actual_loaded_bootstrap_descriptors {World Event} (backend : gateway_backend World Event)
    io native stable discipline thread_errno module_filename canonicalizes
    (threads : gateway_thread_runtime backend io native stable discipline thread_errno)
    (runtime : gateway_bootstrap_runtime backend io native stable discipline module_filename canonicalizes)
    before world events after next :
  gateway_native_loader_boundary (Clight.globalenv prog) before ->
  gateway_native_readonly_mapping (Clight.globalenv prog) before ->
  gateway_native_storage_boundary native (Clight.globalenv prog) before world ->
  discipline None before world ->
  gateway_steps backend (Clight.globalenv prog)
    (gateway_live (Callstate (Internal f_host_bootstrap) nil Kstop before) world) events
    (gateway_live (Returnstate (Vint Int.zero) Kstop after) next) ->
  exists entry root engine results,
    Genv.find_symbol (Clight.globalenv prog) _PyInit__host = Some entry /\
    Genv.find_symbol (Clight.globalenv prog) _host_root = Some root /\
    Genv.find_symbol (Clight.globalenv prog) _host_engine = Some engine /\
    Genv.find_symbol (Clight.globalenv prog) _host_default_results = Some results /\
    gateway_bootstrap_named_paths native discipline module_filename canonicalizes entry root engine results after next /\
    gateway_module_descriptor_regions (Clight.globalenv prog) after /\
    Mem.unchanged_on (fun object _ => gateway_descriptor_object (Clight.globalenv prog) object) before after.
Proof.
  intros LOADER READONLY STORAGE SIDE RUN.
  pose proof (gateway_descriptors_initial native (Clight.globalenv prog) before world LOADER READONLY STORAGE) as STATE.
  destruct (actual_bootstrap_loaded_buffers native stable discipline before world LOADER STORAGE SIDE)
    as (root & engine & results & suffix & executable & results_literal & ROOT & ENGINE & RESULTS &
      SUFFIX & EXECUTABLE & RESULTS_LITERAL & BUFFERS).
  pose proof (gateway_bootstrap_protected_inputs native stable discipline root engine results suffix executable results_literal
    before world ROOT ENGINE RESULTS SUFFIX EXECUTABLE RESULTS_LITERAL STATE BUFFERS) as INPUT.
  assert (BINDING : gateway_function_binding (Clight.globalenv prog) _PyInit__host (Internal f_PyInit__host)).
  { apply gateway_actual_function_binding; vm_compute; reflexivity. }
  destruct BINDING as [entry [ENTRY FUNCTION]].
  pose proof (actual_bootstrap_call_return backend io
    (gateway_protected_native native (gateway_descriptor_object (Clight.globalenv prog)) (gateway_immutable_object (Clight.globalenv prog)))
    stable (gateway_protected_discipline discipline native (gateway_descriptor_object (Clight.globalenv prog))
      (gateway_immutable_object (Clight.globalenv prog)) before)
    thread_errno module_filename canonicalizes
    (gateway_protected_threads backend io native stable discipline thread_errno threads
      (gateway_descriptor_object (Clight.globalenv prog)) (gateway_immutable_object (Clight.globalenv prog)) before)
    (gateway_protected_bootstrap backend io native stable discipline module_filename canonicalizes runtime
      (gateway_descriptor_object (Clight.globalenv prog)) (gateway_immutable_object (Clight.globalenv prog)) before)
    entry root engine results suffix executable results_literal ENTRY ROOT ENGINE RESULTS SUFFIX EXECUTABLE RESULTS_LITERAL
    before world events after next INPUT RUN) as RESULT.
  destruct (gateway_bootstrap_named_unprotect native discipline (gateway_descriptor_object (Clight.globalenv prog))
    (gateway_immutable_object (Clight.globalenv prog)) before module_filename canonicalizes
    entry root engine results after next RESULT) as [PATHS FINAL].
  exists entry, root, engine, results.
  split; [exact ENTRY |]. split; [exact ROOT |]. split; [exact ENGINE |]. split; [exact RESULTS |].
  split; [exact PATHS |]. split.
  - eapply gateway_protected_descriptors; [apply gateway_module_regions_loaded; exact LOADER |exact FINAL].
  - exact (gateway_protected_snapshot _ _ _ _ _ _ FINAL).
Qed.
