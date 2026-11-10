(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The same allocation call, field assignment and return preserve the repaired
   source-reference ledger and the original private metadata graph. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayOperations GatewayReadonly GatewayFramedRuntime
  GatewayObjects GatewayPython GatewayObjectDiscipline GatewayObjectThreads GatewayTypeRuntime
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceRuntime GatewayReferenceBalance GatewayReferenceThreads GatewayReferenceRetained GatewayPermissionSurvival GatewayPermissionRuntime
  GatewayOutcome GatewayOutcomeAllocation GatewayOutcomeConstruction GatewayOwnedOutcomeReturn GatewayOwnedOutcomeResult GatewayOutcomeViewReturn
  GatewayOutcomeFailure GatewayLocalRuntime GatewayObjectEvents GatewayObjectRuns GatewayThreadRuntime GatewayStreamInterface GatewayPathEvents.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Section OwnedOutcomeFactory.
Context {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
  (python:World->python_world)(objects:World->gateway_object_heap)
  (types:World->Values.val->option gateway_type_description)(default_allocator:World->Values.val->Prop)
  (instances:World->Values.val->option Values.val)(leases:World->nat->Values.val->Prop)(owned:World->Values.val->Prop)
  (decimal_float:list Z->Floats.float->Prop)(detached:Values.val->Memory.mem->World->Prop)
  (io:Event->option gateway_native_io)(stable:World->block->Z->Prop)(thread_errno:World->int)
  (heap_allocation:block->Z->Prop)(normal:mem->World->Prop).
Let native:=fun world object=>gateway_native_private(python world)object.
Let discipline:=gateway_python_discipline python objects detached.
Context(runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
  (lifetimes:gateway_allocation_lifetime_runtime backend)
  (allocations:gateway_outcome_allocation_runtime backend python objects types default_allocator instances leases owned io native stable)
  (type_references:gateway_type_reference_runtime backend python objects types default_allocator normal)
  (reference_threads:gateway_reference_thread_contract backend native stable discipline heap_allocation python objects).

Definition gateway_owned_outcome_class_context environment class description ledger held memory world:Prop:=
  gateway_objects_ready(python world)(objects world)memory /\types world class=Some description /\default_allocator world class /\
  gateway_rooted(python world)(objects world)class /\gateway_reference_scope python objects decimal_float ledger held world /\
  gateway_native_environment native world memory environment.

Lemma gateway_owned_outcome_class_context_ambient environment class description ledger held:
  Int.and(gateway_type_flags description)(Int.repr 256)=Int.repr 256 ->
  gateway_ambient_closed backend(gateway_owned_outcome_class_context environment class description ledger held).
Proof.
  intros IMMUTABLE before world after next[NORMAL[TYPE[ALLOCATOR[LEASE[HELD ENVIRONMENT]]]]]INTERFERENCE.
  destruct(gateway_thread_ambient _ _ _ _ _ _ runtime None before world after next NORMAL INTERFERENCE)
    as[READY[[NATIVE STABLE]FRAME]].
  pose proof LEASE as ROOT.
  destruct(@gateway_outcome_class_ambient World Event backend python objects types default_allocator instances leases owned io
    native stable allocations before world after next class description NORMAL ROOT TYPE ALLOCATOR IMMUTABLE INTERFERENCE)
    as[NEXT_ROOT[NEXT_TYPE NEXT_ALLOCATOR]].
  pose proof(@gateway_reference_thread_ambient World Event backend native stable discipline heap_allocation python objects
    reference_threads None before world after next NORMAL INTERFERENCE)as EFFECT.
  split;[exact READY|]. split;[exact NEXT_TYPE|]. split;[exact NEXT_ALLOCATOR|]. split;[exact NEXT_ROOT|].
  split;[eapply gateway_reference_scope_thread_effect;[exact HELD|exact EFFECT]|].
  intros identifier object ty LOOK;destruct(ENVIRONMENT identifier object ty LOOK)as[LIVE PRIVATE];split;
    [eapply Mem.valid_block_unchanged_on;[exact FRAME|exact LIVE]|apply NATIVE;assumption].
Qed.

Theorem gateway_actual_outcome_allocation_keeps_view
    (view:World->Prop)(view_frame:forall before next,view before->gateway_reference_thread_effect python objects before next->view next)
    context environment parameters class description ledger held data_block data_offset
    before world events value after next descriptor:
  gateway_direct_io_projection backend io->gateway_outcome_member_layout ge->parameters!_copy=Some(Vptr data_block data_offset)->
  gateway_reference_ledger_well_formed ledger->
  gateway_reference_take(gateway_reference_result(S(gateway_reference_depth context)))(gateway_reference_entries ledger)=None->
  gateway_source_outcome_type description->gateway_type_basicsize description=24->gateway_type_itemsize description=0->
  Int.and(gateway_type_flags description)(Int.repr 256)=Int.repr 256->
  gateway_owned_outcome_class_context environment class description ledger held before world->view world->
  gateway_steps backend ge
    (gateway_live(Callstate(External(EF_external "PyType_GenericAlloc"(mksignature[Xptr;Xlong]Xptr cc_default))
      [tptr(Tstruct __typeobject noattr);tlong](tptr(Tstruct __object noattr))cc_default)
      [class;Vlong Int64.zero](gateway_outcome_allocation_cont environment parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  exists object final,
    value=Vptr object Ptrofs.zero /\~Mem.valid_block before object /\gateway_reference_ledger_well_formed final /\
    gateway_reference_apply(gateway_reference_mint(gateway_reference_result(S(gateway_reference_depth context)))value)
      (gateway_reference_valid ledger)=gateway_reference_valid final /\
    gateway_owned_outcome_return_context python objects instances owned decimal_float object(Vptr data_block data_offset)class final
      (gateway_reference_result(S(gateway_reference_depth context)))(gateway_reference_next ledger)held after next /\
    gateway_received_bytes io descriptor events=[] /\view next /\gateway_reference_balance(python world)(python next)ledger final.
Proof.
  intros PROJECTION LAYOUT COPY FORMED VACANT ROLE SIZE ITEMS IMMUTABLE INPUT VIEW RUN NONNULL.
  set(definition:=(External(EF_external "PyType_GenericAlloc"(mksignature[Xptr;Xlong]Xptr cc_default))
    [tptr(Tstruct __typeobject noattr);tlong](tptr(Tstruct __object noattr))cc_default:Ctypes.fundef Clight.function)).
  destruct(gateway_return_cut backend ge definition[class;Vlong Int64.zero](gateway_outcome_allocation_cont environment parameters)
    before world events(Returnstate value Kstop after)next ltac:(cbn;exact I)ltac:(cbn;lia)RUN)
    as(allocating &rest &allocated &allocator_after &allocator_next &EVENTS &ALLOCATION_RUN &REST).
  assert(ALLOCATED_NONNULL:allocated<>Vnullptr).
  { intro NULL;subst allocated;apply NONNULL;eapply gateway_actual_outcome_allocation_failure;exact REST. }
  destruct(gateway_external_operation_of_run backend ge _ _ _ _ _ _ _ _ _ _ _ ALLOCATION_RUN)
    as(pending &returned &called &called_world &changed &changed_world &observed &ALLOC_EVENTS &PENDING &PREFIX &OPERATION &SUFFIX).
  set(input:=fun memory current=>gateway_owned_outcome_class_context environment class description ledger held memory current /\view current /\
    forall pointer,(python_native_strong(python world)pointer<=python_native_strong(python current)pointer)%nat).
  assert(CLOSED:gateway_ambient_closed backend input).
  { intros memory current changed_memory following[BASE[CURRENT COUNTS_BEFORE]]INTERFERENCE;split.
    - eapply gateway_owned_outcome_class_context_ambient;
        [exact IMMUTABLE|exact BASE|exact INTERFERENCE].
    - pose proof(@gateway_reference_thread_ambient World Event backend native stable discipline heap_allocation python objects reference_threads
        None memory current changed_memory following(proj1 BASE)INTERFERENCE)as EFFECT.
      split;[eapply view_frame;eassumption|]. intro pointer;specialize(COUNTS_BEFORE pointer).
      pose proof(gateway_reference_thread_counts _ _ _ _ EFFECT pointer);lia. }
  pose proof(gateway_pending_run_ready backend ge _ CLOSED(Callstate definition[class;Vlong Int64.zero]Kstop before)
    before world pending called called_world(conj INPUT(conj VIEW ltac:(intro pointer;apply Nat.le_refl)))PENDING PREFIX)as[CALLED[CALLED_VIEW BEFORE_MONO]].
  destruct CALLED as[NORMAL[TYPE[ALLOCATOR[ROOT[HELD ENVIRONMENT]]]]].
  assert(API:gateway_object_operation backend gateway_api_generic_alloc[class;Vlong Int64.zero]
    called called_world allocated changed changed_world observed).
  { eexists;split;[exact actual_gateway_generic_alloc_abi|exact OPERATION]. }
  destruct(@gateway_outcome_generic_alloc World Event backend python objects types default_allocator instances leases owned io native stable
    allocations called called_world class description allocated changed changed_world observed NORMAL ROOT TYPE ALLOCATOR SIZE ITEMS IMMUTABLE API)
    as[ACCESS[FRAME[NONIO[NULL|NEW]]]];[contradiction|].
  destruct NEW as(object &old_ticket &ALLOCATED &FRESH &READY &CLASS &AFTER_TYPE &AFTER_ALLOCATOR &VALUE &PRIVATE &CREATED &CELL &ZERO
    &VALUES &PRIVACY);subst allocated.
  pose proof(@gateway_type_reference_generic_alloc World Event backend python objects types default_allocator normal type_references
    called called_world class description(Vptr object Ptrofs.zero)changed changed_world observed NORMAL ROLE ROOT TYPE ALLOCATOR SIZE ITEMS IMMUTABLE API
    ltac:(discriminate))as CREDIT.
  destruct(gateway_reference_credit_mints ledger(gateway_reference_result(S(gateway_reference_depth context)))(Vptr object Ptrofs.zero)
    (python called_world)(python changed_world)FORMED(proj1 HELD)VACANT CREDIT)
    as(final &MINT &WELL &COUNTS &OWNED &RETAINED).
  assert(VIEW_EFFECT:gateway_reference_thread_effect python objects called_world changed_world).
  { constructor;[|exact VALUES|exact PRIVACY]. intro pointer.
    destruct(Val.eq pointer(Vptr object Ptrofs.zero))as[SAME|DIFFERENT].
    - subst pointer;rewrite(gateway_reference_credit_target _ _ _ CREDIT);lia.
    - rewrite(gateway_reference_credit_other _ _ _ CREDIT pointer DIFFERENT);lia. }
  assert(AFTER_VIEW:view changed_world)by(eapply view_frame;eassumption).
  assert(AFTER_HELD:gateway_reference_scope python objects decimal_float final held changed_world).
  { split;[exact COUNTS|]. eapply gateway_reference_held_frame;
      [exact(proj2 HELD)|exact(proj1 HELD)|exact COUNTS| |exact VALUES|exact PRIVACY].
    intros captured MEMBER;pose proof(proj1(Forall_forall _ _)(proj2 HELD)captured MEMBER)as[[place OLD]OTHERS].
    exists place;apply RETAINED;exact OLD. }
  assert(AFTER_ENVIRONMENT:gateway_native_environment native changed_world changed environment).
  { intros identifier candidate ty LOOK;destruct(ENVIRONMENT identifier candidate ty LOOK)as[LIVE NATIVE].
    split;[eapply Mem.valid_block_unchanged_on;[exact FRAME|exact LIVE]|apply(proj1 ACCESS);assumption]. }
  set(post_view:=fun current=>view current /\forall pointer,
    (python_native_strong(python changed_world)pointer<=python_native_strong(python current)pointer)%nat).
  assert(POST_FRAME:forall before next,post_view before->gateway_reference_thread_effect python objects before next->post_view next).
  { intros first last[CURRENT MONO]EFFECT;split;[eapply view_frame;eassumption|].
    intro pointer;specialize(MONO pointer);pose proof(gateway_reference_thread_counts _ _ _ _ EFFECT pointer);lia. }
  set(construction:=fun memory current=>gateway_owned_outcome_construction_context python objects instances owned decimal_float
    environment object Vnullptr class final(gateway_reference_result(S(gateway_reference_depth context)))(gateway_reference_next ledger)held memory current /\post_view current).
  assert(AFTER_CONTEXT:construction changed changed_world).
  { split;[split|exact(conj AFTER_VIEW ltac:(intro pointer;apply Nat.le_refl))].
    - exact(conj READY(conj CELL(conj ZERO(conj CLASS(conj OWNED AFTER_HELD))))).
    - exact AFTER_ENVIRONMENT. }
  assert(CONTEXT_CLOSED:gateway_ambient_closed backend construction).
  { intros memory current changed_memory following[BASE CURRENT]INTERFERENCE;split.
    - eapply gateway_owned_outcome_construction_ambient;[exact runtime|exact allocations|exact reference_threads|exact BASE|exact INTERFERENCE].
    - eapply POST_FRAME;[exact CURRENT|].
      eapply gateway_reference_thread_ambient with(mode:=None);[exact reference_threads|exact(proj1(proj1 BASE))|exact INTERFERENCE]. }
  pose proof(gateway_readonly_run_side backend ge construction CONTEXT_CLOSED(Returnstate(Vptr object Ptrofs.zero)Kstop changed)
    changed_world returned(Vptr object Ptrofs.zero)allocator_after allocator_next I AFTER_CONTEXT SUFFIX)as CALLER_READY.
  destruct(gateway_actual_constructed_outcome_keeps_view backend ge python objects types default_allocator instances leases owned decimal_float detached
    io stable thread_errno heap_allocation runtime allocations reference_threads post_view POST_FRAME environment parameters object data_block data_offset class final
    (gateway_reference_result(S(gateway_reference_depth context)))(gateway_reference_next ledger)held
    allocator_after allocator_next rest value after next LAYOUT COPY(proj1 CALLER_READY)(proj2 CALLER_READY)REST)as[SAME[FINAL[FINAL_VIEW AFTER_MONO]]].
  pose proof(gateway_actual_owned_constructed_outcome backend ge python objects types default_allocator instances leases owned decimal_float detached
    io stable thread_errno heap_allocation runtime allocations reference_threads environment parameters object data_block data_offset class final
    (gateway_reference_result(S(gateway_reference_depth context)))(gateway_reference_next ledger)held allocator_after allocator_next rest value after next
    LAYOUT COPY(proj1 CALLER_READY)REST)as[_[_ QUIET]].
  assert(FRESH_BEFORE:~Mem.valid_block before object).
  { intro LIVE;apply FRESH;eapply gateway_survival_live;
      [exact(gateway_actual_run_permissions backend ge lifetimes _ _ _ PREFIX)|exact LIVE]. }
  exists object,final;split;[exact SAME|]. split;[exact FRESH_BEFORE|]. split;[exact WELL|]. split;[rewrite SAME;exact MINT|]. split;[exact FINAL|].
  split;[|split;[exact FINAL_VIEW|]].
  2:{ pose proof(gateway_reference_balance_mint(python called_world)(python changed_world)ledger final
        (gateway_reference_result(S(gateway_reference_depth context)))(Vptr object Ptrofs.zero)CREDIT MINT)as MINT_BALANCE.
      intro pointer;specialize(BEFORE_MONO pointer);specialize(AFTER_MONO pointer);specialize(MINT_BALANCE pointer);lia. }
  rewrite EVENTS,gateway_received_append.
  rewrite(gateway_object_run_no_direct_receive backend ge io gateway_api_generic_alloc definition[class;Vlong Int64.zero]
    before world allocating(Vptr object Ptrofs.zero)allocator_after allocator_next descriptor PROJECTION actual_gateway_generic_alloc_abi ALLOCATION_RUN).
  rewrite(gateway_quiet_received io descriptor rest QUIET);reflexivity.
Qed.

Theorem gateway_actual_owned_outcome_allocation context environment parameters class description ledger held data_block data_offset
    before world events value after next descriptor:
  gateway_direct_io_projection backend io->gateway_outcome_member_layout ge->parameters!_copy=Some(Vptr data_block data_offset)->
  gateway_reference_ledger_well_formed ledger->
  gateway_reference_take(gateway_reference_result(S(gateway_reference_depth context)))(gateway_reference_entries ledger)=None->
  gateway_source_outcome_type description->gateway_type_basicsize description=24->gateway_type_itemsize description=0->
  Int.and(gateway_type_flags description)(Int.repr 256)=Int.repr 256->
  gateway_owned_outcome_class_context environment class description ledger held before world->
  gateway_steps backend ge
    (gateway_live(Callstate(External(EF_external "PyType_GenericAlloc"(mksignature[Xptr;Xlong]Xptr cc_default))
      [tptr(Tstruct __typeobject noattr);tlong](tptr(Tstruct __object noattr))cc_default)
      [class;Vlong Int64.zero](gateway_outcome_allocation_cont environment parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  exists object final,
    value=Vptr object Ptrofs.zero /\~Mem.valid_block before object /\gateway_reference_ledger_well_formed final /\
    gateway_reference_apply(gateway_reference_mint(gateway_reference_result(S(gateway_reference_depth context)))value)
      (gateway_reference_valid ledger)=gateway_reference_valid final /\
    gateway_owned_outcome_return_context python objects instances owned decimal_float object(Vptr data_block data_offset)class final
      (gateway_reference_result(S(gateway_reference_depth context)))(gateway_reference_next ledger)held after next /\
    gateway_received_bytes io descriptor events=[].
Proof.
  intros PROJECTION LAYOUT COPY FORMED VACANT ROLE SIZE ITEMS IMMUTABLE INPUT RUN NONNULL.
  destruct(gateway_actual_outcome_allocation_keeps_view(fun _=>True)ltac:(intros;exact I)
    context environment parameters class description ledger held data_block data_offset before world events value after next descriptor
    PROJECTION LAYOUT COPY FORMED VACANT ROLE SIZE ITEMS IMMUTABLE INPUT I RUN NONNULL)
    as(object &final &POINTER &FRESH &WELL &MINT &CONTEXT &EMPTY &VIEW &BALANCE).
  exists object,final;exact(conj POINTER(conj FRESH(conj WELL(conj MINT(conj CONTEXT EMPTY))))).
Qed.
End OwnedOutcomeFactory.
