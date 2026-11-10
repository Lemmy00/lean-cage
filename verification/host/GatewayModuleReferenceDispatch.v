(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Source-owned class creation binds the immutable received-result getter. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayRuntime GatewayPython GatewayObjects
  GatewayTypeRuntime GatewayTypeDescriptors GatewayGetsets GatewayOutcomeType GatewayOutcomeGetsets
  GatewayOutcomeDispatch GatewayModuleSource GatewayModuleClass GatewayModuleRegions GatewayLoaderRegions
  GatewayModuleDispatch GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting
  GatewayReferenceRuntime GatewayModuleReference.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_actual_module_reference_dispatch {World Event}(backend:gateway_backend World Event)
    python objects types allocator instances leases normal attached io native stable
    immutable_binding attribute_target
    (runtime:gateway_type_runtime backend python objects types allocator instances leases normal attached io native stable)
    (references:gateway_type_reference_runtime backend python objects types allocator normal)
    (descriptors:gateway_descriptor_runtime backend python objects types allocator instances immutable_binding attribute_target)
    ledger before world specification temporaries continuation result after next observed:
  gateway_reference_ledger_well_formed ledger->gateway_reference_counts_fit ledger(python world)->
  gateway_reference_take(gateway_reference_result(gateway_reference_depth(module_outcome_cont temporaries continuation)))
    (gateway_reference_entries ledger)=None->normal before world->
  gateway_module_descriptor_regions(Clight.globalenv prog)before->
  Genv.find_symbol(Clight.globalenv prog)_host_outcome_spec=Some specification->
  gateway_step backend(Clight.globalenv prog)
    (gateway_live(Callstate(External(EF_external "PyType_FromSpec"(mksignature[Xptr]Xptr cc_default))
      [tptr(Tstruct __5268 noattr)](tptr(Tstruct __object noattr))cc_default)
      [Vptr specification Ptrofs.zero](module_outcome_cont temporaries continuation)before)world)
    (gateway_primitive observed)
    (gateway_live(Returnstate result(module_outcome_cont temporaries continuation)after)next)->result<>Vnullptr->
  exists final object offset new initialize destroy traverse clear methods properties entries observation getter,
    result=Vptr object offset /\normal after next /\
    types next result=Some(gateway_outcome_description new initialize destroy traverse clear methods properties) /\
    allocator next result /\gateway_rooted(python next)(objects next)result /\
    gateway_reference_ledger_well_formed final /\gateway_reference_counts_fit final(python next) /\
    gateway_reference_owns final
      (gateway_reference_result(gateway_reference_depth(module_outcome_cont temporaries continuation)))
      (gateway_reference_next ledger)result /\
    gateway_reference_apply(gateway_reference_mint
      (gateway_reference_result(gateway_reference_depth(module_outcome_cont temporaries continuation)))result)
      (gateway_reference_valid ledger)=gateway_reference_valid final /\
    immutable_binding result(gateway_outcome_description new initialize destroy traverse clear methods properties)entries /\
    Forall2(gateway_getset_resolves(Clight.globalenv prog))gateway_outcome_property_sources entries /\
    nth_error entries 14=Some observation /\gateway_getset_name observation=gateway_observation_name /\
    Genv.find_symbol(Clight.globalenv prog)_host_outcome_observation=Some getter /\
    gateway_getset_getter observation=Vptr getter Ptrofs.zero /\gateway_getset_setter observation=Vnullptr /\
    gateway_getset_closure observation=Vnullptr.
Proof.
  intros FORMED FIT VACANT NORMAL REGIONS SPECIFICATION_SYMBOL STEP NONNULL.
  destruct(gateway_module_outcome_specification before REGIONS)
    as(actual_specification&new&initialize&destroy&traverse&clear&methods&properties&ACTUAL_SPECIFICATION&NEW&INITIALIZE&
      DESTROY&TRAVERSE&CLEAR&METHODS_SYMBOL&PROPERTIES_SYMBOL&SPECIFICATION).
  assert(SAME:actual_specification=specification)by congruence;subst actual_specification.
  destruct(REGIONS _host_outcome_properties v_host_outcome_properties eq_refl eq_refl
    ltac:(change(0<640);lia)ltac:(right;cbn;tauto))as[property_table PROPERTY_VIEW].
  destruct PROPERTY_VIEW as[PROPERTY_DEF[PROPERTY_VOLATILE[PROPERTY_SYMBOL PROPERTY_REGION]]].
  assert(SAME_PROPERTY:property_table=properties)by congruence;subst property_table.
  destruct(REGIONS _host_outcome_methods v_host_outcome_methods eq_refl eq_refl
    ltac:(change(0<64);lia)ltac:(right;cbn;tauto))as[method_table METHOD_VIEW].
  destruct METHOD_VIEW as[METHOD_DEF[METHOD_VOLATILE[METHOD_SYMBOL METHOD_REGION]]].
  assert(SAME_METHOD:method_table=methods)by congruence;subst method_table.
  destruct(REGIONS ___stringlit_51 v___stringlit_51 eq_refl eq_refl
    ltac:(change(0<5);lia)ltac:(left;reflexivity))as[name_symbol NAME_VIEW].
  pose proof(gateway_loaded_region_cstring _ _ _ _ _ gateway_module_json_name_literal NAME_VIEW)as NAME_BYTES.
  pose proof NAME_VIEW as[_[_[NAME_SYMBOL NAME_REGION]]].
  destruct(@gateway_type_normal World Event backend python objects types allocator instances leases normal attached io native stable
    runtime before world NORMAL)as[GIL[CLEAR_ERROR VALID]].
  assert(READY:gateway_objects_ready(python world)(objects world)before)by(exact(conj VALID(conj GIL CLEAR_ERROR))).
  assert(OPERATION:gateway_type_operation backend gateway_type_from_spec[Vptr specification Ptrofs.zero]
    before world result after next observed).
  { eexists;split;[reflexivity|]. inversion STEP;subst;cbn[gateway_runtime_operation];eassumption. }
  destruct(gateway_actual_outcome_immutable_binding backend python objects types allocator instances immutable_binding attribute_target descriptors
    before world(Vptr specification Ptrofs.zero)new initialize destroy traverse clear methods properties name_symbol result after next observed
    READY SPECIFICATION(gateway_module_regions_outcome_names before REGIONS)
    (gateway_loaded_region_values _ _ _ _ PROPERTY_REGION)NAME_SYMBOL NAME_BYTES
    (gateway_loaded_region_values _ _ _ _ METHOD_REGION)OPERATION NONNULL)
    as(entries&observation&getter&BINDING&RESOLVES&POSITION&NAME&GETTER&TARGET&SETTER&CLOSURE).
  assert(SPEC_ROLE:gateway_source_outcome_spec(Vptr specification Ptrofs.zero)).
  { exists specification;split;[exact SPECIFICATION_SYMBOL|reflexivity]. }
  assert(TYPE_ROLE:gateway_source_outcome_type
    (gateway_outcome_description new initialize destroy traverse clear methods properties)).
  { exists new,initialize,destroy,traverse,clear,methods,properties.
    exact(conj eq_refl(conj NEW(conj INITIALIZE(conj DESTROY(conj TRAVERSE(conj CLEAR
      (conj METHODS_SYMBOL PROPERTIES_SYMBOL))))))). }
  destruct(gateway_actual_module_type_reference backend python objects types allocator instances leases normal attached io native stable
    runtime references ledger before world specification new initialize destroy traverse clear methods properties
    temporaries continuation result after next observed FORMED FIT VACANT NORMAL SPEC_ROLE TYPE_ROLE SPECIFICATION STEP NONNULL)
    as(final&object&offset&RESULT&AFTER_NORMAL&TYPE&ALLOCATOR&ROOT&APPLY&WELL&COUNTS&OWNED&BOUND&RETAINED).
  exists final,object,offset,new,initialize,destroy,traverse,clear,methods,properties,entries,observation,getter.
  exact(conj RESULT(conj AFTER_NORMAL(conj TYPE(conj ALLOCATOR(conj ROOT(conj WELL(conj COUNTS(conj OWNED
    (conj APPLY(conj BINDING(conj RESOLVES(conj POSITION(conj NAME(conj GETTER(conj TARGET(conj SETTER CLOSURE)))))))))))))))).
Qed.
