(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Actual bootstrap writes exclude additional source-owned flag cells. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers Values Memory Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBootstrapRegions GatewayBootstrapGuarantee
  GatewayBootstrapLoaderSetup GatewayBootstrapBuffers GatewayBootstrapRuntime GatewayThreadRuntime GatewayProtectedMemory
  GatewayProtectedThreads GatewayProtectedBootstrap GatewayInitializerProtection GatewayModuleRegions GatewayLoaderRegions
  GatewayBootstrapHistory GatewayReferenceHistoryThreads GatewayReferenceThreads GatewayBootstrapReferenceScope GatewayBootstrapReference.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_bootstrap_protected_buffers {World} native stable base protected immutable buffers literals before (world : World) :
  gateway_bootstrap_buffers native stable base buffers literals before world ->
  gateway_protected_memory native protected immutable before before world ->
  (forall object amount access, In (object, amount, access) buffers -> protected object -> immutable object) ->
  (forall object bytes, In (object, bytes) literals -> immutable object) ->
  gateway_bootstrap_buffers (gateway_protected_native native protected immutable) stable
    (gateway_protected_discipline base native protected immutable before) buffers literals before world.
Proof.
  intros [SIDE [CAPACITIES LITERALS]] STATE SAFE CONSTANTS.
  split; [split; assumption |]. split.
  - intros object amount access MEMBER; destruct (CAPACITIES object amount access MEMBER) as [PRIVATE REST].
    split; [split; [exact PRIVATE |eapply SAFE; exact MEMBER] |exact REST].
  - intros object bytes MEMBER; destruct (LITERALS object bytes MEMBER) as [actual [offset [POINTER [BYTES OWNED]]]].
    inversion POINTER; subst actual.
    exists object, offset; split; [exact POINTER |]. split; [exact BYTES |].
    intros position RANGE; destruct (OWNED position RANGE) as [PRIVATE |READONLY].
    + left; split; [exact PRIVATE |intros; eapply CONSTANTS; exact MEMBER].
    + right; exact READONLY.
Qed.

Theorem gateway_actual_protected_bootstrap_history {World Event} (backend : gateway_backend World Event)
    io native stable base thread_errno heap_allocation module_filename canonicalizes
    python objects decimal_float ledger retired held protected immutable
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
  (forall object, gateway_descriptor_object (Clight.globalenv prog) object -> protected object) ->
  gateway_protected_memory native protected immutable before before world ->
  (forall object amount access,
    In (object, amount, access) (bootstrap_loaded_capacities root engine results suffix executable results_literal) ->
    protected object -> immutable object) ->
  (forall object bytes, In (object, bytes) (bootstrap_loaded_literals suffix executable results_literal) -> immutable object) ->
  gateway_bootstrap_buffers native stable base (bootstrap_loaded_capacities root engine results suffix executable results_literal)
    (bootstrap_loaded_literals suffix executable results_literal) before world ->
  gateway_reference_history_scope python objects decimal_float ledger retired held world ->
  gateway_steps backend (Clight.globalenv prog)
    (gateway_live (Callstate (Internal f_host_bootstrap) [] Kstop before) world) events
    (gateway_live (Returnstate (Vint Int.zero) Kstop after) next) ->
  gateway_bootstrap_named_paths native base module_filename canonicalizes entry root engine results after next /\
  gateway_module_descriptor_regions (Clight.globalenv prog) after /\
  gateway_reference_history_scope python objects decimal_float ledger retired held next /\
  gateway_protected_memory native protected immutable before after next.
Proof.
  intros ENTRY ROOT ENGINE RESULTS SUFFIX EXECUTABLE RESULTS_LITERAL DESCRIPTORS INCLUDED STATE SAFE CONSTANTS [SIDE BUFFERS] HISTORY RUN.
  set (extended := fun mode memory current => base mode memory current /\
    gateway_reference_history_scope python objects decimal_float ledger retired held current).
  assert (THREADS : gateway_thread_runtime backend io native stable extended thread_errno).
  { apply gateway_thread_with_reference_history with (heap_allocation := heap_allocation);
      [exact reference_threads |exact threads]. }
  assert (RUNTIME : gateway_bootstrap_runtime backend io native stable extended module_filename canonicalizes).
  { apply gateway_bootstrap_with_reference_history; assumption. }
  pose proof (gateway_bootstrap_protected_buffers native stable extended protected immutable
    (bootstrap_loaded_capacities root engine results suffix executable results_literal)
    (bootstrap_loaded_literals suffix executable results_literal) before world
    (conj (conj SIDE HISTORY) BUFFERS) STATE SAFE CONSTANTS) as INPUT.
  pose proof (actual_bootstrap_call_return backend io (gateway_protected_native native protected immutable) stable
    (gateway_protected_discipline extended native protected immutable before) thread_errno module_filename canonicalizes
    (gateway_protected_threads backend io native stable extended thread_errno THREADS protected immutable before)
    (gateway_protected_bootstrap backend io native stable extended module_filename canonicalizes RUNTIME protected immutable before)
    entry root engine results suffix executable results_literal ENTRY ROOT ENGINE RESULTS SUFFIX EXECUTABLE RESULTS_LITERAL
    before world events after next INPUT RUN) as RESULT.
  destruct (gateway_bootstrap_named_unprotect native extended protected immutable before module_filename canonicalizes
    entry root engine results after next RESULT) as [PATHS FINAL].
  destruct (gateway_bootstrap_named_discipline native extended base module_filename canonicalizes
    entry root engine results after next ltac:(intros mode memory current [BASE INVARIANT]; exact BASE) PATHS)
    as [[FINAL_BASE FINAL_HISTORY] FINAL_PATHS].
  split; [exact FINAL_PATHS |]. split.
  - eapply gateway_module_regions_retained; [exact DESCRIPTORS |].
    intros identifier variable object SELECTED [DEFINITION [NONVOLATILE [SYMBOL REGION]]].
    eapply Mem.unchanged_on_implies; [exact (gateway_protected_snapshot _ _ _ _ _ _ FINAL) |].
    intros candidate position SAME LIVE; subst candidate; apply INCLUDED.
    exists identifier, variable; split; [exact DEFINITION |]. split; [exact NONVOLATILE |].
    split; [exact (proj1 (gateway_loaded_region_bound _ _ _ _ REGION)) |]. split; assumption.
  - split; assumption.
Qed.
