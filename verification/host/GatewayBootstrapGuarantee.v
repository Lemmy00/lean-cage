(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A real successful bootstrap returns source-validated, loader-originated paths. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewaySetupPaths
  GatewaySetupComposition GatewaySourcePaths GatewaySourceAutomation GatewayFramedRuntime GatewayCalls
  GatewayFunctionEntry GatewayBootstrapABI GatewayBootstrapSource GatewayBootstrapFilename
  GatewayBootstrapRegions GatewayBootstrapStorageNames GatewayBootstrapAllocation GatewayBootstrapBuffers
  GatewayBootstrapLoaderSetup GatewayBootstrapRuntime GatewayThreadRuntime GatewayLoaderRegions.
Import ListNotations.
Open Scope Z_scope.

Section BootstrapGuarantee.
Context {World Event} (backend : gateway_backend World Event) io native stable discipline thread_errno
    module_filename canonicalizes
    (threads : gateway_thread_runtime backend io native stable discipline thread_errno)
    (runtime : gateway_bootstrap_runtime backend io native stable discipline module_filename canonicalizes).
Let ge := Clight.globalenv prog.
Variables entry root engine results suffix executable results_literal : block.
Hypotheses
  (ENTRY_SYMBOL : Genv.find_symbol ge _PyInit__host = Some entry)
  (ROOT_SYMBOL : Genv.find_symbol ge _host_root = Some root)
  (ENGINE_SYMBOL : Genv.find_symbol ge _host_engine = Some engine)
  (RESULTS_SYMBOL : Genv.find_symbol ge _host_default_results = Some results)
  (SUFFIX_SYMBOL : Genv.find_symbol ge _suffix = Some suffix)
  (EXECUTABLE_SYMBOL : Genv.find_symbol ge _executable = Some executable)
  (RESULTS_LITERAL_SYMBOL : Genv.find_symbol ge _results = Some results_literal).
Let globals := bootstrap_loaded_capacities root engine results suffix executable results_literal.
Let literals := bootstrap_loaded_literals suffix executable results_literal.
Let result := gateway_bootstrap_named_paths native discipline module_filename canonicalizes entry root engine results.

Theorem actual_bootstrap_body_setup information resolved memory :
  NoDup (information :: resolved :: bootstrap_storage_names root engine results suffix executable results_literal) ->
  let property := gateway_bootstrap_buffers native stable discipline
    ((information, 32, Freeable) :: (resolved, 4096, Freeable) :: globals) literals in
  gateway_setup_path backend ge result property
    (State f_host_bootstrap (fn_body f_host_bootstrap) Kstop
      (bootstrap_environment information resolved) bootstrap_temporaries memory).
Proof.
  intro STORAGE_DISTINCT; cbn zeta.
  set (property := gateway_bootstrap_buffers native stable discipline
    ((information, 32, Freeable) :: (resolved, 4096, Freeable) :: globals) literals).
  assert (CLOSED : gateway_ambient_closed backend property) by
    (eapply gateway_bootstrap_buffers_ambient; exact threads).
  destruct (actual_bootstrap_bindings gateway_loader_address_api) as [loader_symbol [LOADER_SYMBOL LOADER_FUNCTION]].
  destruct (actual_bootstrap_bindings gateway_bounded_length_api) as [length_symbol [LENGTH_SYMBOL LENGTH_FUNCTION]].
  destruct (actual_bootstrap_bindings gateway_memory_compare_api) as [comparison_symbol [COMPARISON_SYMBOL COMPARISON_FUNCTION]].
  destruct (actual_bootstrap_bindings gateway_canonical_path_api) as [realpath_symbol [REALPATH_SYMBOL REALPATH_FUNCTION]].
  destruct (actual_bootstrap_bindings gateway_memory_copy_api) as [copy_symbol [COPY_SYMBOL COPY_FUNCTION]].
  eapply gateway_setup_after_source with
    (definition := gateway_bootstrap_signature gateway_loader_address_api)
    (arguments := [Vptr entry Ptrofs.zero; Vptr information Ptrofs.zero])
    (continuation := bootstrap_loader_cont information resolved) (boundary := property).
  - do 3 gateway_source_structure CLOSED.
    eapply gateway_source_same with (target := Callstate
      (gateway_bootstrap_signature gateway_loader_address_api)
      [Vptr entry Ptrofs.zero; Vptr information Ptrofs.zero]
      (bootstrap_loader_cont information resolved) memory).
    + exact CLOSED.
    + cbn; tauto.
    + intros; eapply actual_bootstrap_loader_edge with (symbol := loader_symbol);
        [exact LOADER_SYMBOL |exact LOADER_FUNCTION |exact ENTRY_SYMBOL].
    + constructor; intros; assumption.
  - exact CLOSED.
  - exact CLOSED.
  - intro current; eapply actual_bootstrap_loader_setup;
      [exact threads |exact runtime |exact actual_bootstrap_information_size |
       exact actual_bootstrap_filename_member |exact STORAGE_DISTINCT |
       exact ROOT_SYMBOL |exact ENGINE_SYMBOL |exact RESULTS_SYMBOL |exact SUFFIX_SYMBOL |
       exact EXECUTABLE_SYMBOL |exact RESULTS_LITERAL_SYMBOL |
       exact LENGTH_SYMBOL |exact LENGTH_FUNCTION |exact COMPARISON_SYMBOL |exact COMPARISON_FUNCTION |
       exact REALPATH_SYMBOL |exact REALPATH_FUNCTION |exact COPY_SYMBOL |exact COPY_FUNCTION].
Qed.

Theorem actual_bootstrap_call_return before world events after next :
  gateway_bootstrap_buffers native stable discipline globals literals before world ->
  gateway_steps backend ge
    (gateway_live (Callstate (Internal f_host_bootstrap) [] Kstop before) world)
    events (gateway_live (Returnstate (Vint Int.zero) Kstop after) next) ->
  result after next.
Proof.
  intros INPUT RUN.
  destruct (actual_gateway_function_entry_ambient backend ge f_host_bootstrap [] Kstop before world events
    (Vint Int.zero) Kstop after next RUN)
    as (prefix & rest & entry_memory & entry_world & environment & temporaries & allocated &
      EVENTS & AMBIENT & PREFIX & ENTRY & REST).
  assert (READY : gateway_bootstrap_buffers native stable discipline globals literals entry_memory entry_world).
  { eapply gateway_ambient_run_ready with (source := Callstate (Internal f_host_bootstrap) [] Kstop before);
      [eapply gateway_bootstrap_buffers_ambient; exact threads |exact INPUT |exact AMBIENT |exact PREFIX]. }
  destruct (actual_bootstrap_entry_buffers backend io native stable discipline thread_errno threads ge
    entry_memory entry_world environment temporaries allocated globals literals actual_bootstrap_information_size READY ENTRY)
    as (information & middle & resolved & ENV & TEMPS & INFO & RESOLVED & DIFFERENT & INFO_FRESH & RESOLVED_FRESH & BUFFERS).
  subst environment temporaries.
  assert (NAMES : NoDup (information :: resolved ::
    bootstrap_storage_names root engine results suffix executable results_literal)).
  { eapply bootstrap_allocated_storage_names;
      [exact READY |eapply actual_bootstrap_global_names;
        [exact ROOT_SYMBOL |exact ENGINE_SYMBOL |exact RESULTS_SYMBOL |exact SUFFIX_SYMBOL |
         exact EXECUTABLE_SYMBOL |exact RESULTS_LITERAL_SYMBOL] |
       exact DIFFERENT |exact INFO_FRESH |exact RESOLVED_FRESH]. }
  eapply gateway_setup_return_exact with
    (source := State f_host_bootstrap (fn_body f_host_bootstrap) Kstop
      (bootstrap_environment information resolved) bootstrap_temporaries allocated);
    [exact BUFFERS |apply actual_bootstrap_body_setup; exact NAMES |exact REST].
Qed.
End BootstrapGuarantee.

Theorem actual_loaded_bootstrap_return {World Event} (backend : gateway_backend World Event)
    io native stable discipline thread_errno module_filename canonicalizes
    (threads : gateway_thread_runtime backend io native stable discipline thread_errno)
    (runtime : gateway_bootstrap_runtime backend io native stable discipline module_filename canonicalizes)
    before world events after next :
  gateway_native_loader_boundary (Clight.globalenv prog) before ->
  gateway_native_storage_boundary native (Clight.globalenv prog) before world ->
  discipline None before world ->
  gateway_steps backend (Clight.globalenv prog)
    (gateway_live (Callstate (Internal f_host_bootstrap) [] Kstop before) world)
    events (gateway_live (Returnstate (Vint Int.zero) Kstop after) next) ->
  exists entry root engine results,
    Genv.find_symbol (Clight.globalenv prog) _PyInit__host = Some entry /\
    Genv.find_symbol (Clight.globalenv prog) _host_root = Some root /\
    Genv.find_symbol (Clight.globalenv prog) _host_engine = Some engine /\
    Genv.find_symbol (Clight.globalenv prog) _host_default_results = Some results /\
    gateway_bootstrap_named_paths native discipline module_filename canonicalizes entry root engine results after next.
Proof.
  intros LOADER STORAGE SIDE RUN.
  destruct (actual_bootstrap_loaded_buffers native stable discipline before world LOADER STORAGE SIDE)
    as (root & engine & results & suffix & executable & results_literal & ROOT & ENGINE & RESULTS &
      SUFFIX & EXECUTABLE & RESULTS_LITERAL & BUFFERS).
  assert (BINDING : gateway_function_binding (Clight.globalenv prog) _PyInit__host (Internal f_PyInit__host)).
  { apply gateway_actual_function_binding; vm_compute; reflexivity. }
  destruct BINDING as [entry [ENTRY FUNCTION]].
  exists entry, root, engine, results.
  split; [exact ENTRY |]. split; [exact ROOT |]. split; [exact ENGINE |]. split; [exact RESULTS |].
  eapply actual_bootstrap_call_return;
    [exact threads |exact runtime |exact ENTRY |exact ROOT |exact ENGINE |exact RESULTS |
     exact SUFFIX |exact EXECUTABLE |exact RESULTS_LITERAL |exact BUFFERS |exact RUN].
Qed.
