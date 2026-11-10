(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Genuine flag symbols are outside every actual bootstrap output buffer. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayRegistry GatewayInitializationRegions GatewayInitializationStores
  GatewayBootstrapRegions GatewayBootstrapBuffers GatewayBootstrapCapacities GatewayInitializerProtection GatewayProtectedMemory
  GatewayModuleRegions GatewayLoaderRegions.
Import ListNotations.
Open Scope Z_scope.
Local Opaque Clight.globalenv Genv.find_symbol.

Definition gateway_initialization_guarded_object symbols object : Prop :=
  gateway_descriptor_object (Clight.globalenv prog) object \/
    object = initialization_active symbols \/ object = initialization_complete symbols.
Definition gateway_initialization_immutable_object object : Prop :=
  gateway_descriptor_object (Clight.globalenv prog) object /\ gateway_immutable_object (Clight.globalenv prog) object.

Theorem gateway_initialization_capacity_not_flag symbols object amount access completed :
  In (object, amount, access) (gateway_initialization_capacities symbols) ->
  object <> initialization_flag_object symbols completed.
Proof.
  intro MEMBER.
  assert (SYMBOL : Genv.find_symbol (Clight.globalenv prog) (gateway_initialization_flag_identifier completed) =
    Some (initialization_flag_object symbols completed)).
  { destruct completed; [exact (initialization_complete_symbol symbols) |exact (initialization_active_symbol symbols)]. }
  assert (SEPARATE : forall identifier candidate,
    In identifier [_host_root; _host_engine; _host_default_results; _suffix; _executable; _results] ->
    Genv.find_symbol (Clight.globalenv prog) identifier = Some candidate -> candidate <> initialization_flag_object symbols completed).
  { intros identifier candidate SOURCE BOUND.
    assert (DIFFERENT : identifier <> gateway_initialization_flag_identifier completed).
    { intro SAME; subst identifier; destruct completed;
        cbn [gateway_initialization_flag_identifier In] in SOURCE;
        repeat destruct SOURCE as [SAME |SOURCE]; try contradiction; discriminate SAME. }
    exact (Genv.global_addresses_distinct (Clight.globalenv prog) DIFFERENT BOUND SYMBOL). }
  unfold gateway_initialization_capacities, bootstrap_loaded_capacities in MEMBER; cbn [In] in MEMBER.
  repeat destruct MEMBER as [SAME |MEMBER]; try contradiction; inversion SAME; subst object amount access.
  - apply SEPARATE with (identifier := _host_root); [cbn; auto 12 |exact (initialization_root_symbol symbols)].
  - apply SEPARATE with (identifier := _host_engine); [cbn; auto 12 |exact (initialization_engine_symbol symbols)].
  - apply SEPARATE with (identifier := _host_default_results); [cbn; auto 12 |exact (initialization_results_symbol symbols)].
  - apply SEPARATE with (identifier := _suffix); [cbn; auto 12 |exact (initialization_suffix_symbol symbols)].
  - apply SEPARATE with (identifier := _executable); [cbn; auto 12 |exact (initialization_executable_symbol symbols)].
  - apply SEPARATE with (identifier := _results); [cbn; auto 12 |exact (initialization_results_literal_symbol symbols)].
Qed.

Theorem gateway_initialization_literal_immutable symbols object bytes :
  In (object, bytes) (gateway_initialization_literals symbols) -> gateway_initialization_immutable_object object.
Proof.
  intro MEMBER; unfold gateway_initialization_literals, bootstrap_loaded_literals in MEMBER; cbn [In] in MEMBER.
  repeat destruct MEMBER as [SAME |MEMBER]; try contradiction; inversion SAME; subst object bytes.
  - split.
    + exists _suffix, v_suffix; split; [reflexivity |]. split; [reflexivity |].
      split; [vm_compute; reflexivity |]. split; [left; reflexivity |exact (initialization_suffix_symbol symbols)].
    + exists _suffix, v_suffix; split; [reflexivity |]. split; [reflexivity |exact (initialization_suffix_symbol symbols)].
  - split.
    + exists _executable, v_executable; split; [reflexivity |]. split; [reflexivity |].
      split; [vm_compute; reflexivity |]. split; [left; reflexivity |exact (initialization_executable_symbol symbols)].
    + exists _executable, v_executable; split; [reflexivity |]. split; [reflexivity |exact (initialization_executable_symbol symbols)].
  - split.
    + exists _results, v_results; split; [reflexivity |]. split; [reflexivity |].
      split; [vm_compute; reflexivity |]. split; [left; reflexivity |exact (initialization_results_literal_symbol symbols)].
    + exists _results, v_results; split; [reflexivity |]. split; [reflexivity |exact (initialization_results_literal_symbol symbols)].
Qed.

Theorem gateway_initialization_flag_protection {World} native stable base symbols snapshot active complete before (world : World) :
  gateway_initialization_regions native stable base symbols snapshot active complete before world ->
  gateway_protected_memory native (gateway_initialization_guarded_object symbols) gateway_initialization_immutable_object
    before before world /\
  (forall object amount access, In (object, amount, access) (gateway_initialization_capacities symbols) ->
    gateway_initialization_guarded_object symbols object -> gateway_initialization_immutable_object object) /\
  (forall object bytes, In (object, bytes) (gateway_initialization_literals symbols) -> gateway_initialization_immutable_object object).
Proof.
  intros [BUFFERS DESCRIPTORS PROTECTED ACTIVE_CAPACITY COMPLETE_CAPACITY ACTIVE_VALUE COMPLETE_VALUE].
  assert (REBASED : gateway_protected_memory native (gateway_descriptor_object (Clight.globalenv prog))
    (gateway_immutable_object (Clight.globalenv prog)) before before world).
  { destruct PROTECTED as [LIVE OWNED READONLY SNAPSHOT]; constructor; try assumption; apply Mem.unchanged_on_refl. }
  pose proof (gateway_bootstrap_protected_inputs native stable base (initialization_root symbols) (initialization_engine symbols)
    (initialization_results symbols) (initialization_suffix symbols) (initialization_executable symbols) (initialization_results_literal symbols)
    before world (initialization_root_symbol symbols) (initialization_engine_symbol symbols) (initialization_results_symbol symbols)
    (initialization_suffix_symbol symbols) (initialization_executable_symbol symbols) (initialization_results_literal_symbol symbols)
    REBASED BUFFERS) as [_ [CAPACITIES LITERALS]].
  split.
  - constructor.
    + intros object [DESCRIPTOR |[SAME |SAME]].
      * exact (gateway_protected_live _ _ _ _ _ _ PROTECTED object DESCRIPTOR).
      * subst object; exact (proj1 (proj2 (proj2 (proj2 (proj2 ACTIVE_CAPACITY))))).
      * subst object; exact (proj1 (proj2 (proj2 (proj2 (proj2 COMPLETE_CAPACITY))))).
    + intros object [DESCRIPTOR |[SAME |SAME]].
      * exact (gateway_protected_owned _ _ _ _ _ _ PROTECTED object DESCRIPTOR).
      * subst object; exact (proj1 ACTIVE_CAPACITY).
      * subst object; exact (proj1 COMPLETE_CAPACITY).
    + intros object GUARDED [DESCRIPTOR IMMUTABLE]; exact (gateway_protected_readonly _ _ _ _ _ _ PROTECTED object DESCRIPTOR IMMUTABLE).
    + apply Mem.unchanged_on_refl.
  - split.
    + intros object amount access MEMBER [DESCRIPTOR |[ACTIVE |COMPLETE]].
      * split; [exact DESCRIPTOR |]. exact (proj2 (proj1 (CAPACITIES object amount access MEMBER)) DESCRIPTOR).
      * exfalso; exact (gateway_initialization_capacity_not_flag symbols object amount access false MEMBER ACTIVE).
      * exfalso; exact (gateway_initialization_capacity_not_flag symbols object amount access true MEMBER COMPLETE).
    + apply gateway_initialization_literal_immutable.
Qed.
