(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Actual flag stores retain the concrete bootstrap inputs and descriptors. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayInitializationRegions GatewayBootstrapRegions GatewayBootstrapBuffers
  GatewayBootstrapCapacities GatewayBootstrapEffects GatewayBootstrapRuntime GatewayThreadRuntime GatewayModuleRegions
  GatewayProtectedMemory GatewayInitializerProtection.
Import ListNotations.
Open Scope Z_scope.

Definition initialization_flag_object symbols (complete : bool) :=
  if complete then initialization_complete symbols else initialization_active symbols.

Theorem gateway_initialization_regions_store {World Event} (backend : GatewayMachine.gateway_backend World Event)
    io native stable base thread_errno (threads : gateway_thread_runtime backend io native stable base thread_errno)
    symbols snapshot active complete (completed : bool) word before world after :
  gateway_initialization_regions native stable base symbols snapshot active complete before world ->
  Mem.store Mint32 before (initialization_flag_object symbols completed) 0 (Vint word) = Some after ->
  gateway_initialization_regions native stable base symbols snapshot
    (if completed then active else word) (if completed then word else complete) after world.
Proof.
  intros [BUFFERS DESCRIPTORS PROTECTED ACTIVE_CAPACITY COMPLETE_CAPACITY ACTIVE_VALUE COMPLETE_VALUE] STORE.
  set (target := initialization_flag_object symbols completed).
  set (written := gateway_initialization_flag_identifier completed).
  assert (SYMBOL : Genv.find_symbol (Clight.globalenv prog) written = Some target).
  { destruct completed; [exact (initialization_complete_symbol symbols) |exact (initialization_active_symbol symbols)]. }
  assert (MUTABLE : In written gateway_module_mutable_globals).
  { destruct completed; unfold written, gateway_initialization_flag_identifier, gateway_module_mutable_globals; cbn; auto 20. }
  assert (PRIVATE : native world target).
  { destruct completed; [exact (proj1 COMPLETE_CAPACITY) |exact (proj1 ACTIVE_CAPACITY)]. }
  assert (SIDE : base None after world).
  { eapply gateway_thread_native_store; [exact threads |exact (proj1 BUFFERS) |exact PRIVATE |exact STORE]. }
  assert (FRAME : gateway_native_frame native stable (fun object _ => object = target) world before after).
  { unfold gateway_native_frame; eapply Mem.store_unchanged_on; [exact STORE |].
    intros position INSIDE [OWNED OUTSIDE]; apply OUTSIDE; reflexivity. }
  assert (ACCESS : gateway_access_retained native stable before world world) by (split; intros; assumption).
  assert (LITERALS : forall object bytes, In (object, bytes) (gateway_initialization_literals symbols) -> object <> target).
  { intros object bytes MEMBER.
    unfold gateway_initialization_literals, bootstrap_loaded_literals in MEMBER; cbn [In] in MEMBER.
    repeat destruct MEMBER as [SAME |MEMBER]; try contradiction; inversion SAME; subst object bytes.
    - eapply Genv.global_addresses_distinct with (id1 := _suffix) (id2 := written);
        [destruct completed; discriminate |exact (initialization_suffix_symbol symbols) |exact SYMBOL].
    - eapply Genv.global_addresses_distinct with (id1 := _executable) (id2 := written);
        [destruct completed; discriminate |exact (initialization_executable_symbol symbols) |exact SYMBOL].
    - eapply Genv.global_addresses_distinct with (id1 := _results) (id2 := written);
        [destruct completed; discriminate |exact (initialization_results_literal_symbol symbols) |exact SYMBOL]. }
  assert (DIFFERENT : initialization_active symbols <> initialization_complete symbols).
  { eapply Genv.global_addresses_distinct with (id1 := _host_initializing) (id2 := _host_initialized);
      [discriminate |exact (initialization_active_symbol symbols) |exact (initialization_complete_symbol symbols)]. }
  constructor.
  - destruct BUFFERS as [_ [CAPACITIES BYTES]]; split; [exact SIDE |]. split.
    + intros object amount access MEMBER; eapply gateway_bootstrap_capacity_store; [apply CAPACITIES; exact MEMBER |exact STORE].
    + intros object bytes MEMBER; eapply gateway_bootstrap_protected_effect;
        [apply BYTES; exact MEMBER |exact ACCESS |exact FRAME |].
      intros position RANGE SAME; exact (LITERALS object bytes MEMBER SAME).
  - eapply gateway_module_regions_global_store; [exact DESCRIPTORS |exact MUTABLE |exact SYMBOL |exact STORE].
  - eapply gateway_protected_store; [exact PROTECTED | |exact STORE].
    split; [exact PRIVATE |]. intros BAD; exfalso.
    exact (gateway_descriptor_mutable_separate _ written target MUTABLE SYMBOL BAD).
  - eapply gateway_bootstrap_capacity_store; eassumption.
  - eapply gateway_bootstrap_capacity_store; eassumption.
  - destruct completed; cbn [initialization_flag_object] in STORE |- *.
    + erewrite Mem.load_store_other; [exact ACTIVE_VALUE |exact STORE |left; exact DIFFERENT].
    + erewrite (Mem.load_store_same _ _ _ _ _ _ STORE); reflexivity.
  - destruct completed; cbn [initialization_flag_object] in STORE |- *.
    + erewrite (Mem.load_store_same _ _ _ _ _ _ STORE); reflexivity.
    + erewrite Mem.load_store_other; [exact COMPLETE_VALUE |exact STORE |left; congruence].
Qed.
