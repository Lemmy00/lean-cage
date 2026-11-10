(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual immutable type creation binds the maintained public getters. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayPython GatewayObjects GatewayMachine GatewayTypeRuntime
  GatewayTypeDescriptors GatewayGetsets GatewayOutcomeType GatewayOutcomeGetsets GatewayErrorRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_outcome_json_name:=map Byte.repr[106;115;111;110].
Definition gateway_outcome_json_method function:gateway_type_method:={|
  gateway_type_method_name:=gateway_outcome_json_name;gateway_type_method_function:=Vptr function Ptrofs.zero;
  gateway_type_method_flags:=Int.repr 4|}.

Lemma actual_outcome_default_attribute_slots new initialize destroy traverse clear methods properties:
  gateway_default_attribute_slots(gateway_outcome_description new initialize destroy traverse clear methods properties).
Proof.
  intros code function MEMBER;cbn in MEMBER.
  repeat destruct MEMBER as[MEMBER|MEMBER];try contradiction;inversion MEMBER;repeat split;discriminate.
Qed.

Theorem actual_outcome_methods_from_regions memory table name_symbol:
  Genv.find_symbol(Clight.globalenv prog)___stringlit_51=Some name_symbol ->
  gateway_error_cstring memory(Vptr name_symbol Ptrofs.zero)gateway_outcome_json_name ->
  Genv.load_store_init_data(Clight.genv_genv(Clight.globalenv prog))memory table 0(gvar_init v_host_outcome_methods) ->
  exists function,Genv.find_symbol(Clight.globalenv prog)_host_outcome_json=Some function /\
    gateway_methods_memory memory table 0[gateway_outcome_json_method function].
Proof.
  intros NAME_SYMBOL NAME_BYTES INITIAL.
  cbn[Genv.load_store_init_data gvar_init size_chunk]in INITIAL.
  destruct INITIAL as[[name[NAME NAME_LOAD]][[function[FUNCTION FUNCTION_LOAD]][FLAGS[PADDING[DOCUMENTATION[ZERO REST]]]]]].
  assert(SAME:name=name_symbol)by congruence;subst name.
  exists function;split;[exact FUNCTION|]. exists(Vptr name_symbol Ptrofs.zero);cbn.
  split;[exact NAME_LOAD|]. split;[exact NAME_BYTES|]. split;[exact FUNCTION_LOAD|]. split;[exact FLAGS|exact ZERO].
Qed.

Lemma actual_outcome_property_names_plain:
  Forall(fun source=>~In(gateway_getset_source_name source)gateway_special_attribute_names)gateway_outcome_property_sources.
Proof.
  vm_compute;repeat(apply Forall_cons;[cbn;intuition discriminate|]);apply Forall_nil.
Qed.

Lemma gateway_outcome_attribute_tables_plain entries function:
  Forall2(gateway_getset_resolves(Clight.globalenv prog))gateway_outcome_property_sources entries ->
  gateway_plain_attribute_tables entries[gateway_outcome_json_method function].
Proof.
  intro RESOLVES;split.
  - intros entry MEMBER BAD.
    assert(NAME:In(gateway_getset_name entry)(map gateway_getset_source_name gateway_outcome_property_sources)).
    { rewrite<-(gateway_resolved_getset_names _ _ _ RESOLVES);apply in_map;exact MEMBER. }
    apply in_map_iff in NAME;destruct NAME as[source[SAME SOURCE]].
    pose proof actual_outcome_property_names_plain as PLAIN;apply Forall_forall with(x:=source)in PLAIN;[apply PLAIN;rewrite SAME;exact BAD|exact SOURCE].
  - intros method[MEMBER|MEMBER];[subst method|contradiction].
    vm_compute;intuition discriminate.
Qed.

Theorem gateway_actual_outcome_immutable_binding {World Event}(backend:gateway_backend World Event)
    python objects types default_allocator instances immutable_binding attribute_target
    (runtime:gateway_descriptor_runtime backend python objects types default_allocator instances immutable_binding attribute_target)
    before world pointer new initialize destroy traverse clear methods properties name_symbol result after next observed:
  gateway_objects_ready(python world)(objects world)before ->
  gateway_type_spec_memory before pointer(gateway_outcome_description new initialize destroy traverse clear methods properties) ->
  gateway_outcome_property_names before ->
  Genv.load_store_init_data(Clight.genv_genv(Clight.globalenv prog))before properties 0(gvar_init v_host_outcome_properties) ->
  Genv.find_symbol(Clight.globalenv prog)___stringlit_51=Some name_symbol ->
  gateway_error_cstring before(Vptr name_symbol Ptrofs.zero)gateway_outcome_json_name ->
  Genv.load_store_init_data(Clight.genv_genv(Clight.globalenv prog))before methods 0(gvar_init v_host_outcome_methods) ->
  gateway_type_operation backend gateway_type_from_spec[pointer]before world result after next observed ->result<>Vnullptr ->
  exists entries observation getter,
    immutable_binding result(gateway_outcome_description new initialize destroy traverse clear methods properties)entries /\
    Forall2(gateway_getset_resolves(Clight.globalenv prog))gateway_outcome_property_sources entries /\
    nth_error entries 14=Some observation /\gateway_getset_name observation=gateway_observation_name /\
    Genv.find_symbol(Clight.globalenv prog)_host_outcome_observation=Some getter /\
    gateway_getset_getter observation=Vptr getter Ptrofs.zero /\gateway_getset_setter observation=Vnullptr /\
    gateway_getset_closure observation=Vnullptr.
Proof.
  intros NORMAL SPECIFICATION NAMES PROPERTIES NAME_SYMBOL NAME_BYTES METHODS OPERATION NONNULL.
  destruct(actual_outcome_properties_from_regions before properties NAMES PROPERTIES)
    as(entries &RESOLVES &GETSET_MEMORY &UNIQUE &observation &getter &POSITION &NAME &GETTER &TARGET &SETTER &CLOSURE).
  destruct(actual_outcome_methods_from_regions before methods name_symbol NAME_SYMBOL NAME_BYTES METHODS)
    as(function &FUNCTION &METHOD_MEMORY).
  assert(LENGTH:length entries=15%nat).
  { pose proof(Forall2_length RESOLVES)as SAME;change(15=length entries)%nat in SAME;lia. }
  assert(BINDING:immutable_binding result(gateway_outcome_description new initialize destroy traverse clear methods properties)entries).
  { eapply(@gateway_from_spec_descriptor_binding World Event backend python objects types default_allocator instances immutable_binding attribute_target runtime
      before world pointer(gateway_outcome_description new initialize destroy traverse clear methods properties)
      entries[gateway_outcome_json_method function]properties Ptrofs.zero methods Ptrofs.zero result after next observed).
    - exact NORMAL.
    - exact SPECIFICATION.
    - reflexivity.
    - reflexivity.
    - apply actual_outcome_default_attribute_slots.
    - cbn;auto 10.
    - cbn;auto 10.
    - rewrite LENGTH;change(608<=18446744073709551616);lia.
    - change(40<=18446744073709551616);lia.
    - exact GETSET_MEMORY.
    - exact METHOD_MEMORY.
    - exact UNIQUE.
    - apply gateway_outcome_attribute_tables_plain;exact RESOLVES.
    - exact OPERATION.
    - exact NONNULL. }
  exists entries,observation,getter;split;[exact BINDING|]. split;[exact RESOLVES|].
  exact(conj POSITION(conj NAME(conj GETTER(conj TARGET(conj SETTER CLOSURE))))).
Qed.

Theorem gateway_current_outcome_class {World Event}(backend:gateway_backend World Event)
    python objects types default_allocator instances immutable_binding attribute_target
    (runtime:gateway_descriptor_runtime backend python objects types default_allocator instances immutable_binding attribute_target)
    memory world class new initialize destroy traverse clear methods properties entries:
  gateway_objects_ready(python world)(objects world)memory ->gateway_rooted(python world)(objects world)class ->
  immutable_binding class(gateway_outcome_description new initialize destroy traverse clear methods properties)entries ->
  types world class=Some(gateway_outcome_description new initialize destroy traverse clear methods properties) /\
    default_allocator world class.
Proof.
  intros NORMAL ROOT BINDING.
  destruct(@gateway_immutable_type_description World Event backend python objects types default_allocator instances immutable_binding attribute_target
    runtime memory world class _ entries NORMAL ROOT BINDING)as[TYPE ALLOCATOR].
  split;[exact TYPE|apply ALLOCATOR;apply gateway_outcome_allocator_is_default].
Qed.
