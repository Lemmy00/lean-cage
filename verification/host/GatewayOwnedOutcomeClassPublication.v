(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: One FromSpec operation owns the same source-stored
  immutable class. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayOutcomeType
  GatewayTypeRuntime GatewayTypeDescriptors GatewayOutcomeDispatch GatewayGetsets GatewayOutcomeGetsets
  GatewayThreadRuntime GatewayBootstrapReferenceScope GatewayModuleSource GatewayModuleClass GatewayModuleRegions
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceHistory GatewayReferenceAbandon
  GatewayReferenceRuntime GatewayReferenceStackBound GatewayReferenceThreads GatewayReferenceGlobalStore GatewayOwnedOutcomeClass GatewayOwnedOutcomeClassStore.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_actual_initializer_owns_outcome_class {World Event}(backend:gateway_backend World Event)
    python objects types allocator instances leases base attached io native stable thread_errno heap_allocation
    immutable_binding attribute_target
    (runtime:gateway_type_runtime backend python objects types allocator instances leases(base None)attached io native stable)
    (references:gateway_type_reference_runtime backend python objects types allocator(base None))
    (descriptors:gateway_descriptor_runtime backend python objects types allocator instances immutable_binding attribute_target)
    (threads:gateway_thread_runtime backend io native stable base thread_errno)
    (reference_threads:gateway_reference_thread_contract backend native stable base heap_allocation python objects)
    (profile:gateway_bootstrap_python_profile native base python objects)
    before world specification parameters continuation result after next observed position ledger retired symbol old events returned final_memory final_world:
  base None before world ->gateway_module_descriptor_regions(Clight.globalenv prog)before ->
  Genv.find_symbol(Clight.globalenv prog)_host_outcome_spec=Some specification ->
  Genv.find_symbol(Clight.globalenv prog)_host_outcome_class=Some symbol ->native world symbol ->
  Mem.load Mptr before symbol 0=Some old ->
  gateway_history_well_formed position ledger retired ->gateway_history_counts_fit ledger retired(python world) ->
  gateway_reference_take(gateway_reference_result(S(gateway_reference_depth continuation)))
    (gateway_reference_entries ledger)=None ->
  gateway_reference_take(gateway_reference_temporary(gateway_reference_depth continuation)_t'11)
    (gateway_reference_entries ledger)=None ->
  gateway_step backend(Clight.globalenv prog)
    (gateway_live(Callstate(External(EF_external "PyType_FromSpec"(mksignature[Xptr]Xptr cc_default))
      [tptr(Tstruct __5268 noattr)](tptr(Tstruct __object noattr))cc_default)
      [Vptr specification Ptrofs.zero](module_outcome_cont parameters continuation)before)world)
    (gateway_primitive observed)
    (gateway_live(Returnstate result(module_outcome_cont parameters continuation)after)next) ->result<>Vnullptr ->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate result(module_outcome_cont parameters continuation)after)next)events
    (gateway_live(Returnstate returned Kstop final_memory)final_world) ->
  exists minted final archived prefix suffix stored current changed object offset
      new initialize destroy traverse clear methods properties entries observation getter,
    result=Vptr object offset /\events=prefix++suffix /\
    gateway_history_apply position(gateway_history_current(gateway_reference_mint
      (gateway_reference_result(S(gateway_reference_depth continuation)))result))
      {|gateway_history_active:=gateway_reference_valid ledger;gateway_history_abandoned:=retired|}=
      {|gateway_history_active:=gateway_reference_valid minted;gateway_history_abandoned:=retired|} /\
    gateway_history_execution backend(Clight.globalenv prog)gateway_history_global_store_select(S position)
      (gateway_live(Returnstate result(module_outcome_cont parameters continuation)after)next)
      {|gateway_history_active:=gateway_reference_valid minted;gateway_history_abandoned:=retired|}prefix
      (gateway_live(State f_host_initialize Sskip(Kseq module_outcome_rest continuation)empty_env
        (PTree.set _t'11 result parameters)changed)current)
      {|gateway_history_active:=gateway_reference_valid final;gateway_history_abandoned:=archived|} /\
    gateway_history_well_formed(S position+length prefix)final archived /\
    gateway_history_counts_fit final archived(python current) /\
    gateway_reference_owns final(gateway_reference_global _host_outcome_class)(gateway_reference_next ledger)result /\
    Mem.store Mptr stored symbol 0 result=Some changed /\Mem.load Mptr changed symbol 0=Some result /\
    gateway_reference_place_value(Clight.globalenv prog)
      (State f_host_initialize Sskip(Kseq module_outcome_rest continuation)empty_env(PTree.set _t'11 result parameters)changed)
      (gateway_reference_global _host_outcome_class)result /\
    gateway_objects_ready(python current)(objects current)changed /\gateway_rooted(python current)(objects current)result /\
    types current result=Some(gateway_outcome_description new initialize destroy traverse clear methods properties) /\allocator current result /\
    gateway_source_outcome_type(gateway_outcome_description new initialize destroy traverse clear methods properties) /\
    immutable_binding result(gateway_outcome_description new initialize destroy traverse clear methods properties)entries /\
    Forall2(gateway_getset_resolves(Clight.globalenv prog))gateway_outcome_property_sources entries /\
    nth_error entries 14=Some observation /\gateway_getset_name observation=gateway_observation_name /\
    Genv.find_symbol(Clight.globalenv prog)_host_outcome_observation=Some getter /\
    gateway_getset_getter observation=Vptr getter Ptrofs.zero /\gateway_getset_setter observation=Vnullptr /\
    gateway_getset_closure observation=Vnullptr /\
    (forall pointer,gateway_history_total_count final archived pointer=gateway_history_total_count minted retired pointer) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_initialize Sskip(Kseq module_outcome_rest continuation)empty_env
        (PTree.set _t'11 result parameters)changed)current)suffix
      (gateway_live(Returnstate returned Kstop final_memory)final_world).
Proof.
  intros NORMAL REGIONS SPEC_SYMBOL CLASS_SYMBOL PRIVATE LOAD WELL FIT RESULT_FREE TEMP_FREE STEP NONNULL RUN.
  destruct(gateway_actual_owned_outcome_class backend python objects types allocator instances leases(base None)attached io native stable
    immutable_binding attribute_target runtime references descriptors before world specification parameters continuation result after next observed position ledger retired
    NORMAL REGIONS SPEC_SYMBOL WELL FIT RESULT_FREE STEP NONNULL)
    as(minted &object &offset &new &initialize &destroy &traverse &clear &methods &properties &entries &observation &getter
      &RESULT &AFTER_NORMAL &MINT &MINTED_WELL &MINTED_FIT &MINTED_OWNER &RESULT_BOUND &AFTER_READY &TYPE &ALLOCATOR &ROOT
      &SOURCE_TYPE &BINDING &RESOLVES &POSITION &NAME &GETTER &TARGET &SETTER &CLOSURE).
  assert(OPERATION:gateway_type_operation backend gateway_type_from_spec[Vptr specification Ptrofs.zero]
    before world result after next observed).
  { eexists;split;[reflexivity|]. inversion STEP;subst;cbn[GatewayRuntime.gateway_runtime_operation];eassumption. }
  destruct(gateway_module_outcome_specification before REGIONS)
    as(actual_spec &actual_new &actual_initialize &actual_destroy &actual_traverse &actual_clear &actual_methods &actual_properties
      &ACTUAL_SPEC &ANY_NEW &ANY_INIT &ANY_DESTROY &ANY_TRAVERSE &ANY_CLEAR &ANY_METHODS &ANY_PROPERTIES &SPECIFICATION).
  assert(SPEC_SAME:actual_spec=specification)by congruence;subst actual_spec.
  destruct(@gateway_type_from_spec_effect World Event backend python objects types allocator instances leases(base None)attached io native stable
    runtime before world(Vptr specification Ptrofs.zero)
    (gateway_outcome_description actual_new actual_initialize actual_destroy actual_traverse actual_clear actual_methods actual_properties)
    result after next observed NORMAL SPECIFICATION ltac:(cbn;lia)eq_refl OPERATION)
    as[ATTACHED[ACCESS[FRAME OTHER]]].
  assert(VALID:Mem.valid_block before symbol).
  { eapply Mem.valid_access_valid_block,Mem.valid_access_implies;[eapply Mem.load_valid_access;exact LOAD|constructor]. }
  assert(AFTER_NATIVE:native next symbol)by(exact(proj1 ACCESS symbol VALID PRIVATE)).
  assert(AFTER_LOAD:Mem.load Mptr after symbol 0=Some old).
  { eapply Mem.load_unchanged_on;[exact FRAME| |exact LOAD]. intros;split;[left;exact PRIVATE|cbn;tauto]. }
  assert(TEMP_VACANT:gateway_reference_take(gateway_reference_temporary(gateway_reference_depth continuation)_t'11)
    (gateway_reference_entries minted)=None).
  { pose proof(f_equal gateway_history_active MINT)as MINT_APPLY.
    change(gateway_reference_apply(gateway_reference_mint
      (gateway_reference_result(S(gateway_reference_depth continuation)))result)(gateway_reference_valid ledger)=gateway_reference_valid minted)
      in MINT_APPLY.
    eapply(GatewayReferenceStackBound.gateway_reference_mint_keeps_vacant ledger minted
      (gateway_reference_result(S(gateway_reference_depth continuation)))result
      (gateway_reference_temporary(gateway_reference_depth continuation)_t'11));[exact TEMP_FREE|discriminate|exact MINT_APPLY]. }
  set(property:=fun memory current=>base None memory current /\native current symbol /\
    Mem.load Mptr memory symbol 0=Some old /\gateway_history_counts_fit minted retired(python current)).
  assert(CLOSED:GatewayFramedRuntime.gateway_ambient_closed backend property).
  { intros memory owner changed following[SIDE[NATIVE[CURRENT COUNTED]]]INTERFERENCE.
    destruct(gateway_thread_ambient _ _ _ _ _ _ threads None memory owner changed following SIDE INTERFERENCE)
      as[NEXT_SIDE[NEXT_ACCESS NEXT_FRAME]].
    assert(CURRENT_VALID:Mem.valid_block memory symbol).
    { eapply Mem.valid_access_valid_block,Mem.valid_access_implies;[eapply Mem.load_valid_access;exact CURRENT|constructor]. }
    assert(NEXT_NATIVE:native following symbol)by(exact(proj1 NEXT_ACCESS symbol CURRENT_VALID NATIVE)).
    split;[exact NEXT_SIDE|]. split;[exact NEXT_NATIVE|]. split.
    - eapply Mem.load_unchanged_on;[exact NEXT_FRAME| |exact CURRENT]. intros;split;[left;exact NATIVE|cbn;tauto].
    - intro pointer;specialize(COUNTED pointer).
      pose proof(@gateway_reference_thread_ambient World Event backend native stable base heap_allocation python objects reference_threads None memory owner changed following SIDE INTERFERENCE)as EFFECT.
      pose proof(gateway_reference_thread_counts _ _ _ _ EFFECT pointer);lia. }
  assert(INITIAL:property after next)by(exact(conj AFTER_NORMAL(conj AFTER_NATIVE(conj AFTER_LOAD MINTED_FIT)))).
  assert(PROPERTY:forall memory current,property memory current->gateway_objects_ready(python current)(objects current)memory /\
    gateway_native_private(python current)symbol /\gateway_history_counts_fit minted retired(python current)).
  { intros memory current[SIDE[NATIVE[CURRENT COUNTED]]];split.
    - exact(gateway_bootstrap_profile_ready native base python objects profile memory current SIDE).
    - split;[exact(gateway_bootstrap_profile_native native base python objects profile memory current symbol SIDE NATIVE)|exact COUNTED]. }
  rewrite RESULT in RUN,MINTED_OWNER.
  destruct(gateway_actual_owned_outcome_class_store backend(Clight.globalenv prog)python objects property after next parameters continuation object offset symbol
    events returned final_memory final_world(S position)minted retired(gateway_reference_next ledger)CLOSED INITIAL PROPERTY
    CLASS_SYMBOL MINTED_WELL MINTED_OWNER TEMP_VACANT RUN)
    as(prefix &suffix &stored &current &changed &final &archived &EVENTS &HISTORY &FINAL_WELL &FINAL_FIT &FINAL_OWNER &STORE &CURRENT_LOAD
      &CURRENT_READY &CURRENT_BOUND &COUNTS &SUFFIX).
  assert(FINAL_ACTIVE:gateway_reference_counts_fit final(python current)).
  { intro pointer;specialize(FINAL_FIT pointer);unfold gateway_history_total_count in FINAL_FIT;lia. }
  assert(CURRENT_ROOT:gateway_rooted(python current)(objects current)(Vptr object offset)).
  { eapply gateway_reference_owned_rooted;[exact FINAL_ACTIVE|exact FINAL_OWNER]. }
  destruct(gateway_current_outcome_class backend python objects types allocator instances immutable_binding attribute_target descriptors
    changed current result new initialize destroy traverse clear methods properties entries CURRENT_READY
    ltac:(rewrite RESULT;exact CURRENT_ROOT)BINDING)as[CURRENT_TYPE CURRENT_ALLOCATOR].
  exists minted,final,archived,prefix,suffix,stored,current,changed,object,offset,new,initialize,destroy,traverse,clear,methods,properties,entries,observation,getter.
  rewrite RESULT in *.
  split;[reflexivity|].
  split;[exact EVENTS|].
  split;[exact MINT|].
  split;[exact HISTORY|].
  split;[exact FINAL_WELL|].
  split;[exact FINAL_FIT|].
  split;[exact FINAL_OWNER|].
  split;[exact STORE|].
  split;[exact CURRENT_LOAD|].
  split;[exact CURRENT_BOUND|].
  split;[exact CURRENT_READY|].
  split;[exact CURRENT_ROOT|].
  split;[exact CURRENT_TYPE|].
  split;[exact CURRENT_ALLOCATOR|].
  split;[exact SOURCE_TYPE|].
  split;[exact BINDING|].
  split;[exact RESOLVES|].
  split;[exact POSITION|].
  split;[exact NAME|].
  split;[exact GETTER|].
  split;[exact TARGET|].
  split;[exact SETTER|].
  split;[exact CLOSURE|].
  split;[exact COUNTS|].
  exact SUFFIX.
Qed.
