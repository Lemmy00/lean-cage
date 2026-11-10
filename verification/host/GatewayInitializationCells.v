(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Flag-cell ownership is independent of a clear Python exception state. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayInitializationRegions GatewayInitializationStores GatewayBootstrapCapacities
  GatewayBootstrapEffects GatewayThreadRuntime.
Open Scope Z_scope.
Local Opaque Clight.globalenv Genv.find_symbol.

Record gateway_initialization_cells {World} native symbols active complete memory (world : World) : Prop := {
  initialization_cells_active_capacity : gateway_bootstrap_capacity native memory world (initialization_active symbols) Ptrofs.zero 4 Writable;
  initialization_cells_complete_capacity : gateway_bootstrap_capacity native memory world (initialization_complete symbols) Ptrofs.zero 4 Writable;
  initialization_cells_active_value : Mem.load Mint32 memory (initialization_active symbols) 0 = Some (Vint active);
  initialization_cells_complete_value : Mem.load Mint32 memory (initialization_complete symbols) 0 = Some (Vint complete)
}.

Theorem gateway_initialization_region_cells {World} native stable base symbols snapshot active complete memory world :
  @gateway_initialization_regions World native stable base symbols snapshot active complete memory world ->
  gateway_initialization_cells native symbols active complete memory world.
Proof.
  intro REGIONS; constructor; [exact (initialization_region_active_capacity _ _ _ _ _ _ _ _ _ REGIONS) |
    exact (initialization_region_complete_capacity _ _ _ _ _ _ _ _ _ REGIONS) |
    exact (initialization_region_active_value _ _ _ _ _ _ _ _ _ REGIONS) |
    exact (initialization_region_complete_value _ _ _ _ _ _ _ _ _ REGIONS)].
Qed.

Theorem gateway_initialization_cells_quiet {World} native stable symbols active complete before world after next :
  @gateway_initialization_cells World native symbols active complete before world ->
  gateway_access_retained native stable before world next ->
  gateway_native_frame native stable gateway_native_no_output world before after ->
  gateway_initialization_cells native symbols active complete after next.
Proof.
  intros [ACTIVE_CAPACITY COMPLETE_CAPACITY ACTIVE COMPLETE] ACCESS FRAME; constructor.
  - eapply gateway_bootstrap_capacity_quiet; eassumption.
  - eapply gateway_bootstrap_capacity_quiet; eassumption.
  - erewrite Mem.load_unchanged_on_1; [exact ACTIVE |exact FRAME |exact (proj1 (proj2 (proj2 (proj2 (proj2 ACTIVE_CAPACITY))))) |].
    intros; split; [left; exact (proj1 ACTIVE_CAPACITY) |cbn; tauto].
  - erewrite Mem.load_unchanged_on_1; [exact COMPLETE |exact FRAME |exact (proj1 (proj2 (proj2 (proj2 (proj2 COMPLETE_CAPACITY))))) |].
    intros; split; [left; exact (proj1 COMPLETE_CAPACITY) |cbn; tauto].
Qed.

Theorem gateway_initialization_cells_store {World} native symbols active complete before (world : World) completed word after :
  gateway_initialization_cells native symbols active complete before world ->
  Mem.store Mint32 before (initialization_flag_object symbols completed) 0 (Vint word) = Some after ->
  gateway_initialization_cells native symbols (if completed then active else word) (if completed then word else complete) after world.
Proof.
  intros [ACTIVE_CAPACITY COMPLETE_CAPACITY ACTIVE COMPLETE] STORE.
  assert (IDENTIFIERS : _host_initializing <> _host_initialized) by discriminate.
  assert (DIFFERENT : initialization_active symbols <> initialization_complete symbols).
  { exact (Genv.global_addresses_distinct (Clight.globalenv prog) IDENTIFIERS
      (initialization_active_symbol symbols) (initialization_complete_symbol symbols)). }
  constructor.
  - eapply gateway_bootstrap_capacity_store; eassumption.
  - eapply gateway_bootstrap_capacity_store; eassumption.
  - destruct completed; cbn [initialization_flag_object] in STORE |- *.
    + erewrite Mem.load_store_other; [exact ACTIVE |exact STORE |left; exact DIFFERENT].
    + erewrite (Mem.load_store_same _ _ _ _ _ _ STORE); reflexivity.
  - destruct completed; cbn [initialization_flag_object] in STORE |- *.
    + erewrite (Mem.load_store_same _ _ _ _ _ _ STORE); reflexivity.
    + erewrite Mem.load_store_other; [exact COMPLETE |exact STORE |left; congruence].
Qed.
