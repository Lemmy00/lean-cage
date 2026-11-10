(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Bootstrap retains the actual active/completed flag cells for publication. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayInitializationRegions GatewayInitializationFlags GatewayInitializationStores
  GatewayBootstrapProtectedHistory GatewayBootstrapRegions GatewayBootstrapBuffers GatewayBootstrapCapacities GatewayBootstrapRuntime
  GatewayBootstrapLoaderSetup GatewayBootstrapHistory GatewayBootstrapReferenceScope GatewayBootstrapReference
  GatewayReferenceHistoryThreads GatewayReferenceThreads GatewayThreadRuntime GatewayProtectedMemory GatewayModuleRegions.
Import ListNotations.

Record gateway_initialization_flag_state {World} native (base : option Values.val -> mem -> World -> Prop)
    symbols active complete memory (world : World) : Prop := {
  initialization_flags_side : base None memory world;
  initialization_flags_active_capacity : gateway_bootstrap_capacity native memory world (initialization_active symbols) Ptrofs.zero 4 Writable;
  initialization_flags_complete_capacity : gateway_bootstrap_capacity native memory world (initialization_complete symbols) Ptrofs.zero 4 Writable;
  initialization_flags_active_value : Mem.load Mint32 memory (initialization_active symbols) 0 = Some (Vint active);
  initialization_flags_complete_value : Mem.load Mint32 memory (initialization_complete symbols) 0 = Some (Vint complete)
}.

Lemma gateway_initialization_flag_capacity_retained {World} native symbols before (world : World) after next completed :
  gateway_bootstrap_capacity native before world (initialization_flag_object symbols completed) Ptrofs.zero 4 Writable ->
  gateway_protected_memory native (gateway_initialization_guarded_object symbols) gateway_initialization_immutable_object before after next ->
  gateway_bootstrap_capacity native after next (initialization_flag_object symbols completed) Ptrofs.zero 4 Writable.
Proof.
  intros [PRIVATE [POSITIVE [COUNT [WIDTH [LIVE RANGE]]]]] FINAL.
  assert (GUARDED : gateway_initialization_guarded_object symbols (initialization_flag_object symbols completed)).
  { right; destruct completed; [right |left]; reflexivity. }
  split; [exact (gateway_protected_owned _ _ _ _ _ _ FINAL _ GUARDED) |].
  split; [exact POSITIVE |]. split; [exact COUNT |]. split; [exact WIDTH |].
  split; [exact (gateway_protected_live _ _ _ _ _ _ FINAL _ GUARDED) |].
  intros position INSIDE; eapply Mem.perm_unchanged_on;
    [exact (gateway_protected_snapshot _ _ _ _ _ _ FINAL) |exact GUARDED |apply RANGE; exact INSIDE].
Qed.

Theorem gateway_actual_bootstrap_flagged {World Event} (backend : gateway_backend World Event)
    io native stable base thread_errno heap_allocation module_filename canonicalizes
    python objects decimal_float ledger retired held
    (threads : gateway_thread_runtime backend io native stable base thread_errno)
    (runtime : gateway_bootstrap_runtime backend io native stable base module_filename canonicalizes)
    (profile : gateway_bootstrap_python_profile native base python objects)
    (reference_threads : gateway_reference_thread_contract backend native stable base heap_allocation python objects)
    (references : gateway_bootstrap_reference_runtime backend python objects)
    symbols snapshot active complete entry before world events after next :
  Genv.find_symbol (Clight.globalenv prog) _PyInit__host = Some entry ->
  gateway_initialization_regions native stable base symbols snapshot active complete before world ->
  gateway_reference_history_scope python objects decimal_float ledger retired held world ->
  gateway_steps backend (Clight.globalenv prog)
    (gateway_live (Callstate (Internal f_host_bootstrap) [] Kstop before) world) events
    (gateway_live (Returnstate (Vint Int.zero) Kstop after) next) ->
  gateway_bootstrap_named_paths native base module_filename canonicalizes entry
    (initialization_root symbols) (initialization_engine symbols) (initialization_results symbols) after next /\
  gateway_module_descriptor_regions (Clight.globalenv prog) after /\
  gateway_reference_history_scope python objects decimal_float ledger retired held next /\
  gateway_initialization_flag_state native base symbols active complete after next.
Proof.
  intros ENTRY REGIONS HISTORY RUN.
  destruct (gateway_initialization_flag_protection native stable base symbols snapshot active complete before world REGIONS)
    as [STATE [SAFE CONSTANTS]].
  pose proof REGIONS as [BUFFERS DESCRIPTORS PROTECTED ACTIVE_CAPACITY COMPLETE_CAPACITY ACTIVE_VALUE COMPLETE_VALUE].
  destruct (gateway_actual_protected_bootstrap_history backend io native stable base thread_errno heap_allocation module_filename canonicalizes
    python objects decimal_float ledger retired held (gateway_initialization_guarded_object symbols) gateway_initialization_immutable_object
    threads runtime profile reference_threads references entry
    (initialization_root symbols) (initialization_engine symbols) (initialization_results symbols)
    (initialization_suffix symbols) (initialization_executable symbols) (initialization_results_literal symbols)
    before world events after next ENTRY (initialization_root_symbol symbols) (initialization_engine_symbol symbols)
    (initialization_results_symbol symbols) (initialization_suffix_symbol symbols) (initialization_executable_symbol symbols)
    (initialization_results_literal_symbol symbols) DESCRIPTORS ltac:(intros; left; assumption) STATE SAFE CONSTANTS BUFFERS HISTORY RUN)
    as [PATHS [FINAL_DESCRIPTORS [FINAL_HISTORY FINAL]]].
  split; [exact PATHS |]. split; [exact FINAL_DESCRIPTORS |]. split; [exact FINAL_HISTORY |].
  constructor.
  - exact (proj1 (gateway_bootstrap_named_discipline native base base module_filename canonicalizes entry
      (initialization_root symbols) (initialization_engine symbols) (initialization_results symbols) after next
      ltac:(intros; assumption) PATHS)).
  - exact (gateway_initialization_flag_capacity_retained native symbols before world after next false ACTIVE_CAPACITY FINAL).
  - exact (gateway_initialization_flag_capacity_retained native symbols before world after next true COMPLETE_CAPACITY FINAL).
  - erewrite Mem.load_unchanged_on_1;
      [exact ACTIVE_VALUE |exact (gateway_protected_snapshot _ _ _ _ _ _ FINAL) |
       exact (proj1 (proj2 (proj2 (proj2 (proj2 ACTIVE_CAPACITY))))) |].
    intros; right; left; reflexivity.
  - erewrite Mem.load_unchanged_on_1;
      [exact COMPLETE_VALUE |exact (gateway_protected_snapshot _ _ _ _ _ _ FINAL) |
       exact (proj1 (proj2 (proj2 (proj2 (proj2 COMPLETE_CAPACITY))))) |].
    intros; right; right; reflexivity.
Qed.
