(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: One real bootstrap preserves its actual prior reference history and descriptors. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers Values Memory Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayLoaderRegions GatewayModuleRegions
  GatewayBootstrapRegions GatewayBootstrapRuntime GatewayBootstrapDescriptors GatewayBootstrapLoaderSetup
  GatewayBootstrapLoadedSetup GatewayBootstrapRealpathSetup GatewayBootstrapCanonicalSetup GatewayBootstrapReturn
  GatewayInitializerProtection GatewayThreadRuntime GatewayThreadInvariant GatewayReferenceThreads
  GatewayReferenceHistoryThreads GatewayBootstrapReferenceScope GatewayBootstrapReference.

Theorem gateway_bootstrap_named_discipline {World} native
    (before_side after_side : option Values.val -> mem -> World -> Prop)
    module_filename canonicalizes entry root engine results memory world :
  (forall mode memory world, before_side mode memory world -> after_side mode memory world) ->
  @gateway_bootstrap_named_paths World native before_side module_filename canonicalizes
    entry root engine results memory world ->
  before_side None memory world /\
  gateway_bootstrap_named_paths native after_side module_filename canonicalizes entry root engine results memory world.
Proof.
  intros INCLUDED [original [located [LOADER [ORIGINAL_SIZE [ORIGINAL_SLASH [ORIGINAL_SUFFIX
    [canonical [before [resolved [CANONICAL [CANONICAL_SIZE [CANONICAL_SLASH [CANONICAL_SUFFIX
      [SIDE [STORAGE STRINGS]]]]]]]]]]]]]]].
  split; [exact SIDE |].
  exists original, located; split; [exact LOADER |]. split; [exact ORIGINAL_SIZE |].
  split; [exact ORIGINAL_SLASH |]. split; [exact ORIGINAL_SUFFIX |].
  exists canonical, before, resolved; split; [exact CANONICAL |]. split; [exact CANONICAL_SIZE |].
  split; [exact CANONICAL_SLASH |]. split; [exact CANONICAL_SUFFIX |].
  split; [apply INCLUDED; exact SIDE |]. split; assumption.
Qed.

Theorem actual_loaded_bootstrap_reference_history {World Event} (backend : gateway_backend World Event)
    io native stable base thread_errno heap_allocation module_filename canonicalizes
    python objects decimal_float ledger retired held
    (threads : gateway_thread_runtime backend io native stable base thread_errno)
    (runtime : gateway_bootstrap_runtime backend io native stable base module_filename canonicalizes)
    (profile : gateway_bootstrap_python_profile native base python objects)
    (reference_threads : gateway_reference_thread_contract backend native stable base heap_allocation python objects)
    (references : gateway_bootstrap_reference_runtime backend python objects)
    before world events after next :
  gateway_native_loader_boundary (Clight.globalenv prog) before ->
  gateway_native_readonly_mapping (Clight.globalenv prog) before ->
  gateway_native_storage_boundary native (Clight.globalenv prog) before world ->
  base None before world ->
  gateway_reference_history_scope python objects decimal_float ledger retired held world ->
  gateway_steps backend (Clight.globalenv prog)
    (gateway_live (Callstate (Internal f_host_bootstrap) nil Kstop before) world) events
    (gateway_live (Returnstate (Vint Int.zero) Kstop after) next) ->
  exists entry root engine results,
    Genv.find_symbol (Clight.globalenv prog) _PyInit__host = Some entry /\
    Genv.find_symbol (Clight.globalenv prog) _host_root = Some root /\
    Genv.find_symbol (Clight.globalenv prog) _host_engine = Some engine /\
    Genv.find_symbol (Clight.globalenv prog) _host_default_results = Some results /\
    gateway_bootstrap_named_paths native base module_filename canonicalizes entry root engine results after next /\
    gateway_module_descriptor_regions (Clight.globalenv prog) after /\
    gateway_reference_history_scope python objects decimal_float ledger retired held next /\
    Mem.unchanged_on (fun object _ => gateway_descriptor_object (Clight.globalenv prog) object) before after.
Proof.
  intros LOADER READONLY STORAGE SIDE HISTORY RUN.
  set (extended := gateway_thread_invariant_discipline base
    (gateway_reference_history_scope python objects decimal_float ledger retired held)).
  assert (THREADS : gateway_thread_runtime backend io native stable extended thread_errno).
  { apply gateway_thread_with_reference_history with (heap_allocation := heap_allocation);
      [exact reference_threads |exact threads]. }
  assert (RUNTIME : gateway_bootstrap_runtime backend io native stable extended module_filename canonicalizes).
  { apply gateway_bootstrap_with_reference_history; assumption. }
  destruct (actual_loaded_bootstrap_descriptors backend io native stable extended thread_errno module_filename canonicalizes
    THREADS RUNTIME before world events after next LOADER READONLY STORAGE (conj SIDE HISTORY) RUN)
    as (entry & root & engine & results & ENTRY & ROOT & ENGINE & RESULTS & PATHS & DESCRIPTORS & FRAME).
  destruct (gateway_bootstrap_named_discipline native extended base module_filename canonicalizes
    entry root engine results after next ltac:(intros mode memory current [BASE INVARIANT]; exact BASE) PATHS)
    as [[FINAL_BASE FINAL_HISTORY] FINAL_PATHS].
  exists entry, root, engine, results.
  split; [exact ENTRY |]. split; [exact ROOT |]. split; [exact ENGINE |]. split; [exact RESULTS |].
  split; [exact FINAL_PATHS |]. split; [exact DESCRIPTORS |]. split; assumption.
Qed.
