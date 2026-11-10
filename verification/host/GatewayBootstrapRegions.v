(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Identified writable ELF globals coexist with the linked SDK heap. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayRegistry GatewayLoaderRegions
  GatewayBootstrapCapacities GatewayThreadRuntime GatewayBootstrapRuntime GatewayBootstrapEffects
  GatewayBootstrapConstants GatewayGlobals GatewayModuleRegions GatewayBootstrapBuffers.
Import ListNotations.
Open Scope Z_scope.

(* Individual ELF segment mapping and C-private storage authority, at load only.
   This supplies no initialized application path or later callback frame. *)
Definition gateway_native_storage_selected identifier variable : Prop :=
  gateway_module_descriptor identifier variable \/ In identifier gateway_module_mutable_globals.

Record gateway_native_storage_boundary {World} (native : World -> block -> Prop)
    (ge : Clight.genv) (memory : mem) (world : World) : Prop := {
  gateway_loaded_native : forall identifier variable object,
    gateway_native_storage_selected identifier variable ->
    gateway_native_initializer_view ge identifier variable object memory -> native world object;
  gateway_loaded_writable : forall identifier variable object,
    gateway_native_initializer_view ge identifier variable object memory ->
    gvar_readonly variable = false ->
    Mem.range_perm memory object 0
      (init_data_list_size (gvar_init variable)) Cur Writable
}.

Definition gateway_bootstrap_storage {World} (native : World -> block -> Prop)
    memory world root engine results : Prop :=
  gateway_bootstrap_capacity native memory world root Ptrofs.zero 4096 Writable /\
  gateway_bootstrap_capacity native memory world engine Ptrofs.zero 4096 Writable /\
  gateway_bootstrap_capacity native memory world results Ptrofs.zero 4096 Writable.

Theorem gateway_writable_loaded_capacity {World} native ge memory world identifier variable object :
  @gateway_native_storage_boundary World native ge memory world ->
  gateway_native_initializer_view ge identifier variable object memory ->
  gateway_native_storage_selected identifier variable -> gvar_readonly variable = false ->
  gateway_bootstrap_capacity native memory world object Ptrofs.zero
    (init_data_list_size (gvar_init variable)) Writable.
Proof.
  intros LOADER VIEW SELECTED MUTABLE.
  pose proof (gateway_loaded_native native ge memory world LOADER identifier variable object SELECTED VIEW) as PRIVATE.
  pose proof (gateway_loaded_writable native ge memory world LOADER identifier variable object VIEW MUTABLE) as RANGE.
  destruct VIEW as [_ [_ [_ [BOUND READABLE BYTES VALUES]]]].
  split; [exact PRIVATE |]. split; [lia |]. split; [lia |].
  split; [change (0 + init_data_list_size (gvar_init variable) <= Ptrofs.modulus); lia |]. split.
  - eapply Mem.perm_valid_block; apply (RANGE 0); lia.
  - intros position INSIDE; apply RANGE; exact INSIDE.
Qed.

Theorem gateway_readable_loaded_capacity {World} native ge memory world identifier variable object :
  @gateway_native_storage_boundary World native ge memory world ->
  gateway_native_initializer_view ge identifier variable object memory ->
  gateway_native_storage_selected identifier variable ->
  gateway_bootstrap_capacity native memory world object Ptrofs.zero
    (init_data_list_size (gvar_init variable)) Readable.
Proof.
  intros LOADER VIEW SELECTED.
  pose proof (gateway_loaded_native native ge memory world LOADER identifier variable object SELECTED VIEW) as PRIVATE.
  destruct VIEW as [_ [_ [_ [BOUND READABLE BYTES VALUES]]]].
  split; [exact PRIVATE |]. split; [lia |]. split; [lia |].
  split; [change (0 + init_data_list_size (gvar_init variable) <= Ptrofs.modulus); lia |]. split.
  - eapply Mem.perm_valid_block; apply (READABLE 0); lia.
  - exact READABLE.
Qed.

Theorem actual_bootstrap_buffer_registration :
  gateway_program_definition _host_root global_definitions = Some (Gvar v_host_root) /\
  gateway_program_definition _host_engine global_definitions = Some (Gvar v_host_engine) /\
  gateway_program_definition _host_default_results global_definitions = Some (Gvar v_host_default_results) /\
  init_data_list_size (gvar_init v_host_root) = 4096 /\
  init_data_list_size (gvar_init v_host_engine) = 4096 /\
  init_data_list_size (gvar_init v_host_default_results) = 4096.
Proof. repeat split; vm_compute; reflexivity. Qed.

Theorem actual_bootstrap_loaded_storage {World} native memory world :
  gateway_native_loader_boundary (Clight.globalenv prog) memory ->
  @gateway_native_storage_boundary World native (Clight.globalenv prog) memory world ->
  exists root engine results,
    Genv.find_symbol (Clight.globalenv prog) _host_root = Some root /\
    Genv.find_symbol (Clight.globalenv prog) _host_engine = Some engine /\
    Genv.find_symbol (Clight.globalenv prog) _host_default_results = Some results /\
    root <> engine /\ root <> results /\ engine <> results /\
    gateway_bootstrap_storage native memory world root engine results.
Proof.
  intros LOADER WRITABLE.
  destruct actual_bootstrap_buffer_registration as [ROOT [ENGINE [RESULTS [RS [ES DS]]]]].
  destruct (gateway_native_initialized _ _ LOADER _ _ ROOT eq_refl ltac:(rewrite RS; lia)) as [root ROOT_VIEW].
  destruct (gateway_native_initialized _ _ LOADER _ _ ENGINE eq_refl ltac:(rewrite ES; lia)) as [engine ENGINE_VIEW].
  destruct (gateway_native_initialized _ _ LOADER _ _ RESULTS eq_refl ltac:(rewrite DS; lia)) as [results RESULTS_VIEW].
  assert (ROOT_SYMBOL : Genv.find_symbol (Clight.globalenv prog) _host_root = Some root)
    by exact (proj1 (proj2 (proj2 ROOT_VIEW))).
  assert (ENGINE_SYMBOL : Genv.find_symbol (Clight.globalenv prog) _host_engine = Some engine)
    by exact (proj1 (proj2 (proj2 ENGINE_VIEW))).
  assert (RESULTS_SYMBOL : Genv.find_symbol (Clight.globalenv prog) _host_default_results = Some results)
    by exact (proj1 (proj2 (proj2 RESULTS_VIEW))).
  exists root, engine, results; split; [exact ROOT_SYMBOL |]. split; [exact ENGINE_SYMBOL |].
  split; [exact RESULTS_SYMBOL |]. split.
  - eapply Genv.global_addresses_distinct with (id1 := _host_root) (id2 := _host_engine);
      [discriminate |exact ROOT_SYMBOL |exact ENGINE_SYMBOL].
  - split.
    + eapply Genv.global_addresses_distinct with (id1 := _host_root) (id2 := _host_default_results);
        [discriminate |exact ROOT_SYMBOL |exact RESULTS_SYMBOL].
    + split.
      * eapply Genv.global_addresses_distinct with (id1 := _host_engine) (id2 := _host_default_results);
          [discriminate |exact ENGINE_SYMBOL |exact RESULTS_SYMBOL].
      * unfold gateway_bootstrap_storage; split; [|split].
        -- rewrite <- RS; eapply gateway_writable_loaded_capacity; [exact WRITABLE |exact ROOT_VIEW |right; unfold gateway_module_mutable_globals; simpl; auto 20 |reflexivity].
        -- rewrite <- ES; eapply gateway_writable_loaded_capacity; [exact WRITABLE |exact ENGINE_VIEW |right; unfold gateway_module_mutable_globals; simpl; auto 20 |reflexivity].
        -- rewrite <- DS; eapply gateway_writable_loaded_capacity; [exact WRITABLE |exact RESULTS_VIEW |right; unfold gateway_module_mutable_globals; simpl; auto 20 |reflexivity].
Qed.

Theorem gateway_loaded_literal_protected {World} native stable memory world identifier variable object bytes :
  @gateway_native_storage_boundary World native (Clight.globalenv prog) memory world ->
  gateway_native_initializer_view (Clight.globalenv prog) identifier variable object memory ->
  gateway_static_cstring identifier variable bytes -> gvar_readonly variable = true ->
  gateway_bootstrap_protected native stable memory world (Vptr object Ptrofs.zero) (bytes ++ [Byte.zero]).
Proof.
  intros STORAGE VIEW STRING READONLY.
  eapply gateway_bootstrap_owned_cstring.
  - eapply gateway_loaded_native; [exact STORAGE |left; left; exact READONLY |exact VIEW].
  - eapply gateway_loaded_region_cstring; eassumption.
Qed.

Theorem actual_bootstrap_loaded_literals {World} native stable memory world :
  gateway_native_loader_boundary (Clight.globalenv prog) memory ->
  @gateway_native_storage_boundary World native (Clight.globalenv prog) memory world ->
  exists suffix executable results,
    Genv.find_symbol (Clight.globalenv prog) _suffix = Some suffix /\
    Genv.find_symbol (Clight.globalenv prog) _executable = Some executable /\
    Genv.find_symbol (Clight.globalenv prog) _results = Some results /\
    gateway_bootstrap_protected native stable memory world (Vptr suffix Ptrofs.zero)
      (bootstrap_suffix_bytes ++ [Byte.zero]) /\
    gateway_bootstrap_protected native stable memory world (Vptr executable Ptrofs.zero)
      (bootstrap_executable_bytes ++ [Byte.zero]) /\
    gateway_bootstrap_protected native stable memory world (Vptr results Ptrofs.zero)
      (bootstrap_results_bytes ++ [Byte.zero]).
Proof.
  intros LOADER STORAGE.
  destruct actual_bootstrap_source_literals as [SUFFIX [EXECUTABLE RESULTS]].
  destruct (gateway_native_initialized _ _ LOADER _suffix v_suffix ltac:(vm_compute; reflexivity) (proj1 (proj2 SUFFIX))
    ltac:(vm_compute; reflexivity)) as [suffix SUFFIX_VIEW].
  destruct (gateway_native_initialized _ _ LOADER _executable v_executable ltac:(vm_compute; reflexivity) (proj1 (proj2 EXECUTABLE))
    ltac:(vm_compute; reflexivity)) as [executable EXECUTABLE_VIEW].
  destruct (gateway_native_initialized _ _ LOADER _results v_results ltac:(vm_compute; reflexivity) (proj1 (proj2 RESULTS))
    ltac:(vm_compute; reflexivity)) as [results RESULTS_VIEW].
  exists suffix, executable, results.
  split; [exact (proj1 (proj2 (proj2 SUFFIX_VIEW))) |].
  split; [exact (proj1 (proj2 (proj2 EXECUTABLE_VIEW))) |].
  split; [exact (proj1 (proj2 (proj2 RESULTS_VIEW))) |].
  split; [|split]; eapply gateway_loaded_literal_protected; try eassumption; reflexivity.
Qed.

Theorem actual_module_definition_not_private_storage :
  ~ gateway_native_storage_selected _host_module v_host_module.
Proof.
  unfold gateway_native_storage_selected, gateway_module_descriptor, gateway_module_mutable_globals.
  cbn; intuition discriminate.
Qed.

Definition bootstrap_loaded_literals suffix executable results : list (block * list Byte.int) :=
  [(suffix, bootstrap_suffix_bytes ++ [Byte.zero]);
   (executable, bootstrap_executable_bytes ++ [Byte.zero]);
   (results, bootstrap_results_bytes ++ [Byte.zero])].

Definition bootstrap_loaded_capacities root engine results suffix executable results_literal
    : list (block * Z * permission) :=
  [(root, 4096, Writable); (engine, 4096, Writable); (results, 4096, Writable);
   (suffix, 31, Readable); (executable, 19, Readable); (results_literal, 21, Readable)].

Theorem gateway_actual_loaded_literal_capacity {World} native memory world identifier variable object :
  gateway_native_loader_boundary (Clight.globalenv prog) memory ->
  @gateway_native_storage_boundary World native (Clight.globalenv prog) memory world ->
  gateway_program_definition identifier global_definitions = Some (Gvar variable) ->
  gvar_volatile variable = false -> gvar_readonly variable = true ->
  0 < init_data_list_size (gvar_init variable) ->
  Genv.find_symbol (Clight.globalenv prog) identifier = Some object ->
  gateway_bootstrap_capacity native memory world object Ptrofs.zero
    (init_data_list_size (gvar_init variable)) Readable.
Proof.
  intros LOADER STORAGE DEFINITION VOLATILE READONLY SIZE SYMBOL.
  destruct (gateway_native_initialized _ _ LOADER identifier variable DEFINITION VOLATILE SIZE)
    as [actual VIEW].
  assert (SAME : actual = object) by (pose proof (proj1 (proj2 (proj2 VIEW))); congruence).
  subst actual; eapply gateway_readable_loaded_capacity;
    [exact STORAGE |exact VIEW |left; left; exact READONLY].
Qed.

Theorem actual_bootstrap_loaded_buffers {World} native stable discipline memory world :
  gateway_native_loader_boundary (Clight.globalenv prog) memory ->
  @gateway_native_storage_boundary World native (Clight.globalenv prog) memory world ->
  discipline None memory world ->
  exists root engine results suffix executable results_literal,
    Genv.find_symbol (Clight.globalenv prog) _host_root = Some root /\
    Genv.find_symbol (Clight.globalenv prog) _host_engine = Some engine /\
    Genv.find_symbol (Clight.globalenv prog) _host_default_results = Some results /\
    Genv.find_symbol (Clight.globalenv prog) _suffix = Some suffix /\
    Genv.find_symbol (Clight.globalenv prog) _executable = Some executable /\
    Genv.find_symbol (Clight.globalenv prog) _results = Some results_literal /\
    gateway_bootstrap_buffers native stable discipline
      (bootstrap_loaded_capacities root engine results suffix executable results_literal)
      (bootstrap_loaded_literals suffix executable results_literal) memory world.
Proof.
  intros LOADER STORAGE SIDE.
  destruct (actual_bootstrap_loaded_storage native memory world LOADER STORAGE)
    as [root [engine [results [ROOT [ENGINE [RESULTS [RE [RR [ER [ROOT_CAP [ENGINE_CAP RESULTS_CAP]]]]]]]]]]].
  destruct (actual_bootstrap_loaded_literals native stable memory world LOADER STORAGE)
    as [suffix [executable [results_literal [SUFFIX [EXECUTABLE [RESULTS_LITERAL [SUFFIX_BYTES [EXECUTABLE_BYTES RESULTS_BYTES]]]]]]]].
  assert (SUFFIX_CAP : gateway_bootstrap_capacity native memory world suffix Ptrofs.zero 31 Readable).
  { change 31 with (init_data_list_size (gvar_init v_suffix)).
    eapply gateway_actual_loaded_literal_capacity; try eassumption; vm_compute; reflexivity. }
  assert (EXECUTABLE_CAP : gateway_bootstrap_capacity native memory world executable Ptrofs.zero 19 Readable).
  { change 19 with (init_data_list_size (gvar_init v_executable)).
    eapply gateway_actual_loaded_literal_capacity; try eassumption; vm_compute; reflexivity. }
  assert (RESULTS_LITERAL_CAP : gateway_bootstrap_capacity native memory world results_literal Ptrofs.zero 21 Readable).
  { change 21 with (init_data_list_size (gvar_init v_results)).
    eapply gateway_actual_loaded_literal_capacity; try eassumption; vm_compute; reflexivity. }
  exists root, engine, results, suffix, executable, results_literal.
  split; [exact ROOT |]. split; [exact ENGINE |]. split; [exact RESULTS |].
  split; [exact SUFFIX |]. split; [exact EXECUTABLE |]. split; [exact RESULTS_LITERAL |].
  split; [exact SIDE |]. split.
  - intros object amount access MEMBER; unfold bootstrap_loaded_capacities in MEMBER; cbn [In] in MEMBER.
    repeat destruct MEMBER as [SAME |MEMBER]; try contradiction;
      inversion SAME; subst object amount access; assumption.
  - intros object bytes MEMBER; unfold bootstrap_loaded_literals in MEMBER; cbn [In] in MEMBER.
    repeat destruct MEMBER as [SAME |MEMBER]; try contradiction;
      inversion SAME; subst object bytes; assumption.
Qed.
