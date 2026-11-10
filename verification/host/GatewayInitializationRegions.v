(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Native load supplies the concrete flags and bootstrap regions once. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayRegistry GatewayMachine GatewayLoaderRegions GatewayModuleRegions
  GatewayBootstrapRegions GatewayBootstrapBuffers GatewayBootstrapCapacities GatewayBootstrapRetention GatewayBootstrapEffects
  GatewayInitializerProtection GatewayProtectedMemory GatewayThreadRuntime GatewayBootstrapRuntime.
Import ListNotations.
Open Scope Z_scope.

Record gateway_initialization_symbols := {
  initialization_root : block;
  initialization_engine : block;
  initialization_results : block;
  initialization_suffix : block;
  initialization_executable : block;
  initialization_results_literal : block;
  initialization_active : block;
  initialization_complete : block;
  initialization_root_symbol : Genv.find_symbol (Clight.globalenv prog) _host_root = Some initialization_root;
  initialization_engine_symbol : Genv.find_symbol (Clight.globalenv prog) _host_engine = Some initialization_engine;
  initialization_results_symbol : Genv.find_symbol (Clight.globalenv prog) _host_default_results = Some initialization_results;
  initialization_suffix_symbol : Genv.find_symbol (Clight.globalenv prog) _suffix = Some initialization_suffix;
  initialization_executable_symbol : Genv.find_symbol (Clight.globalenv prog) _executable = Some initialization_executable;
  initialization_results_literal_symbol : Genv.find_symbol (Clight.globalenv prog) _results = Some initialization_results_literal;
  initialization_active_symbol : Genv.find_symbol (Clight.globalenv prog) _host_initializing = Some initialization_active;
  initialization_complete_symbol : Genv.find_symbol (Clight.globalenv prog) _host_initialized = Some initialization_complete
}.

Definition gateway_initialization_capacities symbols := bootstrap_loaded_capacities
  (initialization_root symbols) (initialization_engine symbols) (initialization_results symbols)
  (initialization_suffix symbols) (initialization_executable symbols) (initialization_results_literal symbols).
Definition gateway_initialization_literals symbols := bootstrap_loaded_literals
  (initialization_suffix symbols) (initialization_executable symbols) (initialization_results_literal symbols).

Record gateway_initialization_regions {World} native stable base symbols snapshot active complete memory (world : World) : Prop := {
  initialization_region_buffers : gateway_bootstrap_buffers native stable base
    (gateway_initialization_capacities symbols) (gateway_initialization_literals symbols) memory world;
  initialization_region_descriptors : gateway_module_descriptor_regions (Clight.globalenv prog) memory;
  initialization_region_protected : gateway_protected_memory native (gateway_descriptor_object (Clight.globalenv prog))
    (gateway_immutable_object (Clight.globalenv prog)) snapshot memory world;
  initialization_region_active_capacity : gateway_bootstrap_capacity native memory world (initialization_active symbols) Ptrofs.zero 4 Writable;
  initialization_region_complete_capacity : gateway_bootstrap_capacity native memory world (initialization_complete symbols) Ptrofs.zero 4 Writable;
  initialization_region_active_value : Mem.load Mint32 memory (initialization_active symbols) 0 = Some (Vint active);
  initialization_region_complete_value : Mem.load Mint32 memory (initialization_complete symbols) 0 = Some (Vint complete)
}.

Definition gateway_initialization_flag_identifier (complete : bool) := if complete then _host_initialized else _host_initializing.
Definition gateway_initialization_flag_variable (complete : bool) := if complete then v_host_initialized else v_host_initializing.

Theorem gateway_loaded_initialization_flag {World} native memory (world : World) complete :
  gateway_native_loader_boundary (Clight.globalenv prog) memory ->
  gateway_native_storage_boundary native (Clight.globalenv prog) memory world ->
  exists object,
    Genv.find_symbol (Clight.globalenv prog) (gateway_initialization_flag_identifier complete) = Some object /\
    gateway_bootstrap_capacity native memory world object Ptrofs.zero 4 Writable /\
    Mem.load Mint32 memory object 0 = Some (Vint Int.zero).
Proof.
  intros LOADER STORAGE.
  assert (DEFINITION : gateway_program_definition (gateway_initialization_flag_identifier complete) global_definitions =
    Some (Gvar (gateway_initialization_flag_variable complete))) by (destruct complete; reflexivity).
  assert (NONVOLATILE : gvar_volatile (gateway_initialization_flag_variable complete) = false) by (destruct complete; reflexivity).
  assert (SIZE : init_data_list_size (gvar_init (gateway_initialization_flag_variable complete)) = 4) by (destruct complete; reflexivity).
  destruct (gateway_native_initialized _ _ LOADER _ _ DEFINITION NONVOLATILE ltac:(rewrite SIZE; lia)) as [object VIEW].
  exists object; split; [exact (proj1 (proj2 (proj2 VIEW))) |]. split.
  - rewrite <- SIZE; eapply gateway_writable_loaded_capacity; [exact STORAGE |exact VIEW | |destruct complete; reflexivity].
    right; destruct complete; unfold gateway_module_mutable_globals; cbn; auto 20.
  - destruct VIEW as [_ [_ [_ [_ _ _ VALUES]]]].
    destruct complete; cbn [gateway_initialization_flag_variable Genv.load_store_init_data] in VALUES;
      exact (proj1 VALUES).
Qed.

Theorem gateway_initialization_regions_loaded {World} native stable base before (world : World) :
  gateway_native_loader_boundary (Clight.globalenv prog) before ->
  gateway_native_readonly_mapping (Clight.globalenv prog) before ->
  gateway_native_storage_boundary native (Clight.globalenv prog) before world -> base None before world ->
  exists symbols, gateway_initialization_regions native stable base symbols before Int.zero Int.zero before world.
Proof.
  intros LOADER READONLY STORAGE SIDE.
  destruct (actual_bootstrap_loaded_buffers native stable base before world LOADER STORAGE SIDE)
    as (root & engine & results & suffix & executable & results_literal & ROOT & ENGINE & RESULTS & SUFFIX & EXECUTABLE & RESULTS_LITERAL & BUFFERS).
  destruct (gateway_loaded_initialization_flag native before world false LOADER STORAGE) as (active & ACTIVE_SYMBOL & ACTIVE_CAPACITY & ACTIVE_VALUE).
  destruct (gateway_loaded_initialization_flag native before world true LOADER STORAGE) as (complete & COMPLETE_SYMBOL & COMPLETE_CAPACITY & COMPLETE_VALUE).
  exists {| initialization_root := root; initialization_engine := engine; initialization_results := results;
    initialization_suffix := suffix; initialization_executable := executable; initialization_results_literal := results_literal;
    initialization_active := active; initialization_complete := complete;
    initialization_root_symbol := ROOT; initialization_engine_symbol := ENGINE; initialization_results_symbol := RESULTS;
    initialization_suffix_symbol := SUFFIX; initialization_executable_symbol := EXECUTABLE;
    initialization_results_literal_symbol := RESULTS_LITERAL; initialization_active_symbol := ACTIVE_SYMBOL;
    initialization_complete_symbol := COMPLETE_SYMBOL |}.
  constructor; cbn; try assumption.
  - apply gateway_module_regions_loaded; exact LOADER.
  - apply gateway_descriptors_initial; assumption.
Qed.

Theorem gateway_initialization_regions_quiet {World} native stable base symbols snapshot active complete before world after next :
  @gateway_initialization_regions World native stable base symbols snapshot active complete before world ->
  base None after next -> gateway_access_retained native stable before world next ->
  gateway_native_frame native stable gateway_native_no_output world before after ->
  gateway_initialization_regions native stable base symbols snapshot active complete after next.
Proof.
  intros [BUFFERS DESCRIPTORS PROTECTED ACTIVE_CAPACITY COMPLETE_CAPACITY ACTIVE_VALUE COMPLETE_VALUE] SIDE ACCESS FRAME.
  constructor.
  - eapply gateway_bootstrap_buffers_quiet; eassumption.
  - eapply gateway_module_regions_native_frame; [exact DESCRIPTORS | |exact FRAME].
    intros identifier variable object SELECTED [DEFINITION [NONVOLATILE [SYMBOL REGION]]]; split.
    + eapply gateway_protected_owned; [exact PROTECTED |].
      exists identifier, variable; split; [exact DEFINITION |]. split; [exact NONVOLATILE |].
      split; [exact (proj1 (gateway_loaded_region_bound _ _ _ _ REGION)) |]. split; assumption.
    + intros; cbn; tauto.
  - eapply gateway_protected_effect; [exact PROTECTED |exact ACCESS |exact FRAME |intros; cbn; tauto].
  - eapply gateway_bootstrap_capacity_quiet; eassumption.
  - eapply gateway_bootstrap_capacity_quiet; eassumption.
  - erewrite Mem.load_unchanged_on_1; [exact ACTIVE_VALUE |exact FRAME |exact (proj1 (proj2 (proj2 (proj2 (proj2 ACTIVE_CAPACITY))))) |].
    intros; split; [left; exact (proj1 ACTIVE_CAPACITY) |cbn; tauto].
  - erewrite Mem.load_unchanged_on_1; [exact COMPLETE_VALUE |exact FRAME |exact (proj1 (proj2 (proj2 (proj2 (proj2 COMPLETE_CAPACITY))))) |].
    intros; split; [left; exact (proj1 COMPLETE_CAPACITY) |cbn; tauto].
Qed.
