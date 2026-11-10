(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Source descriptors retain actual relocated tables and strings. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayRegistry GatewayLoaderRegions GatewayInitializerRetention
  GatewayGlobals GatewayErrorRuntime GatewayThreadRuntime GatewayOutcome GatewayOutcomeGetsets GatewayGetsets.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_module_descriptor identifier (variable : globvar type) : Prop :=
  gvar_readonly variable = true \/ In identifier
    [_host_workspace_spec; _host_workspace_slots; _host_workspace_methods;
     _host_cancellation_spec; _host_cancellation_slots; _host_cancellation_methods;
     _host_outcome_spec; _host_outcome_slots; _host_outcome_methods;
     _host_outcome_properties; _host_outcome_fields; _host_module_methods].

Definition gateway_module_descriptor_regions (ge : Clight.genv) memory : Prop :=
  forall identifier variable,
    gateway_program_definition identifier global_definitions = Some (Gvar variable) ->
    gvar_volatile variable = false -> 0 < init_data_list_size (gvar_init variable) ->
    gateway_module_descriptor identifier variable ->
    exists object, gateway_native_initializer_view ge identifier variable object memory.

Theorem gateway_module_regions_loaded ge memory :
  gateway_native_loader_boundary ge memory -> gateway_module_descriptor_regions ge memory.
Proof. intros LOADER identifier variable DEFINITION NONVOLATILE POSITIVE SELECTED.
  eapply gateway_native_initialized; eassumption.
Qed.

Theorem gateway_module_regions_retained ge before after :
  gateway_module_descriptor_regions ge before ->
  (forall identifier variable object,
    gateway_module_descriptor identifier variable ->
    gateway_native_initializer_view ge identifier variable object before ->
    Mem.unchanged_on (fun candidate _ => candidate = object) before after) ->
  gateway_module_descriptor_regions ge after.
Proof.
  intros REGIONS FRAME identifier variable DEFINITION NONVOLATILE POSITIVE SELECTED.
  destruct (REGIONS identifier variable DEFINITION NONVOLATILE POSITIVE SELECTED) as [object VIEW].
  exists object; eapply gateway_initializer_view_retained;
    [exact VIEW |eapply FRAME; eassumption].
Qed.

Theorem gateway_module_regions_native_frame {World} ge before after
    (native : World -> block -> Prop) stable output world :
  gateway_module_descriptor_regions ge before ->
  (forall identifier variable object,
    gateway_module_descriptor identifier variable ->
    gateway_native_initializer_view ge identifier variable object before ->
    native world object /\ forall position, ~ output object position) ->
  gateway_native_frame native stable output world before after ->
  gateway_module_descriptor_regions ge after.
Proof.
  intros REGIONS PRIVATE FRAME.
  eapply gateway_module_regions_retained; [exact REGIONS |].
  intros identifier variable object SELECTED VIEW.
  destruct (PRIVATE identifier variable object SELECTED VIEW) as [OWNED UNWRITTEN].
  eapply Mem.unchanged_on_implies; [exact FRAME |].
  intros candidate position SAME; subst candidate; split; [left; exact OWNED |apply UNWRITTEN].
Qed.

Theorem actual_outcome_property_literal source :
  In source gateway_outcome_property_sources -> exists variable,
    gateway_program_definition (gateway_getset_name_symbol source) global_definitions = Some (Gvar variable) /\
    gvar_readonly variable = true /\
    gateway_static_cstring (gateway_getset_name_symbol source) variable (gateway_getset_source_name source).
Proof.
  cbn [gateway_outcome_property_sources gateway_outcome_name_symbols gateway_outcome_names
    gateway_observation_name combine seq map app In].
  intro MEMBER; repeat destruct MEMBER as [SAME |MEMBER]; try contradiction; subst source.
  all: eexists; split; [reflexivity |split; [reflexivity |]].
  all: (eapply gateway_static_string_from_registration;
    [vm_compute; reflexivity |reflexivity |reflexivity |vm_compute; intuition discriminate |
     change Ptrofs.modulus with 18446744073709551616; cbn; lia]).
Qed.

Theorem gateway_module_regions_outcome_names memory :
  gateway_module_descriptor_regions (Clight.globalenv prog) memory -> gateway_outcome_property_names memory.
Proof.
  intros REGIONS source name MEMBER SYMBOL.
  destruct (actual_outcome_property_literal source MEMBER) as [variable [DEFINITION [READONLY STATIC]]].
  assert (POSITIVE : 0 < init_data_list_size (gvar_init variable)).
  { destruct STATIC as [_ [_ [_ [_ [SIZE BYTES]]]]]; rewrite SIZE; lia. }
  assert (NONVOLATILE : gvar_volatile variable = false) by (exact (proj1 (proj2 STATIC))).
  destruct (REGIONS _ _ DEFINITION NONVOLATILE POSITIVE (or_introl READONLY)) as [object VIEW].
  assert (SAME : object = name) by (destruct VIEW as [_ [_ [ACTUAL REGION]]]; congruence).
  subst name; eapply gateway_loaded_region_cstring; eassumption.
Qed.

Definition gateway_module_mutable_globals : list ident :=
  [_host_root; _host_engine; _host_default_results;
   _host_path_class; _host_cancellation_class; _host_outcome_class;
   _host_initializing; _host_initialized].

Theorem actual_module_mutable_not_descriptor identifier variable :
  In identifier gateway_module_mutable_globals ->
  gateway_program_definition identifier global_definitions = Some (Gvar variable) ->
  ~ gateway_module_descriptor identifier variable.
Proof.
  cbn [gateway_module_mutable_globals In]; intros MEMBER DEFINITION.
  repeat destruct MEMBER as [SAME |MEMBER]; try contradiction; subst identifier;
    cbn [gateway_program_definition] in DEFINITION; inversion DEFINITION; subst variable;
    unfold gateway_module_descriptor; cbn; intuition discriminate.
Qed.

Theorem gateway_module_descriptor_separate (ge : Clight.genv) memory identifier variable object
    written symbol :
  gateway_module_descriptor identifier variable ->
  gateway_native_initializer_view ge identifier variable object memory ->
  In written gateway_module_mutable_globals ->
  Genv.find_symbol ge written = Some symbol -> object <> symbol.
Proof.
  intros SELECTED [DEFINITION [NONVOLATILE [SYMBOL REGION]]] MUTABLE WRITTEN.
  assert (DISTINCT : identifier <> written).
  { intro SAME; subst written.
    exact (actual_module_mutable_not_descriptor identifier variable MUTABLE DEFINITION SELECTED). }
  eapply Genv.global_addresses_distinct; eassumption.
Qed.

Theorem gateway_module_regions_global_store ge before after written symbol chunk offset value :
  gateway_module_descriptor_regions ge before -> In written gateway_module_mutable_globals ->
  Genv.find_symbol ge written = Some symbol -> Mem.store chunk before symbol offset value = Some after ->
  gateway_module_descriptor_regions ge after.
Proof.
  intros REGIONS MUTABLE SYMBOL STORE.
  eapply gateway_module_regions_retained; [exact REGIONS |].
  intros identifier variable object SELECTED VIEW.
  pose proof (gateway_module_descriptor_separate ge before identifier variable object written symbol
    SELECTED VIEW MUTABLE SYMBOL) as DISTINCT.
  eapply Mem.store_unchanged_on; [exact STORE |].
  intros position RANGE SAME; apply DISTINCT; symmetry; exact SAME.
Qed.
