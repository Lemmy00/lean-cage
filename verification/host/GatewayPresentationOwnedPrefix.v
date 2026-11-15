(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The callback tuple is built from actual source-owned SDK credits. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine CallContexts.
From HostGateway Require Import GatewaySource GatewayMachine GatewayRuntime GatewayPython GatewayObjects GatewayReferences
  GatewayValue GatewayObjectDiscipline GatewayObjectThreads GatewayThreadRuntime GatewayStreamInterface GatewayFramedRuntime
  GatewayContexts GatewaySourcePaths GatewaySourceSDKReceipt GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting
  GatewayReferenceStackBound GatewayReferenceFrames GatewayReferenceNormalForm GatewayReferenceHeld GatewayReferenceThreads
  GatewayReferenceCapture GatewayOutcomeCopyCapture GatewayPresentationRuntime GatewayPresentationSource GatewayPresentationTrace
  GatewayPresentationCapturedSource GatewayPresentationCredits GatewayPresentationContext GatewayPresentationCapture.
Import ListNotations.
Local Close Scope lean_scope.

Lemma gateway_presentation_sdk_step {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    external types result_type convention arguments context before world result after next observed:
  gateway_runtime_operation backend(External external types result_type convention)arguments before world result after next observed ->
  gateway_step backend ge(gateway_live(Callstate(External external types result_type convention)arguments context before)world)
    (gateway_primitive observed)(gateway_live(Returnstate result context after)next).
Proof. intros OPERATION;apply gateway_external_returned;exact OPERATION. Qed.

Theorem gateway_actual_owned_presentation_prefix {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects tuples decimal_float detached io stable thread_errno heap_allocation
    (thread:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (threads:gateway_reference_thread_contract backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (references:gateway_reference_runtime backend python objects)
    (metadata:gateway_presentation_reference_runtime backend python objects tuples)
    (presentation:gateway_presentation_runtime backend python objects tuples(fun current object=>gateway_native_private(python current)object))
    context older held reserved captured protected source parameters array displacement child child_offset callable callable_offset
    before world events value after next:
  gateway_presentation_bindings ge ->is_call_cont context ->gateway_reference_stack_bound context older ->
  gateway_reference_ledger_well_formed older ->In captured held ->
  parameters!_count=Some(Vint Int.one) ->parameters!_values=Some(Vptr array displacement) ->
  parameters!_callable=Some(Vptr callable callable_offset) ->
  (Ptrofs.unsigned displacement+8<=Ptrofs.modulus)%Z ->
  (forall position,(Ptrofs.unsigned displacement<=position<Ptrofs.unsigned displacement+8)%Z->protected array position) ->
  gateway_presentation_context python objects decimal_float older held reserved captured protected source array displacement
    (Vptr child child_offset)before world ->
  gateway_steps backend ge(gateway_live(State f_host_call_objects(fn_body f_host_call_objects)Kstop empty_env parameters before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->
  exists tuple tuple_offset ledger selected prefix suffix memory current,
    events=prefix++suffix /\gateway_reference_ledger_well_formed ledger /\
    gateway_reference_entries ledger=gateway_reference_entry(gateway_reference_next older)
      (gateway_reference_temporary(gateway_reference_depth context)_arguments)(Vptr tuple tuple_offset)::gateway_reference_entries older /\
    gateway_reference_next ledger=S(S(gateway_reference_next older)) /\
    selected!_arguments=Some(Vptr tuple tuple_offset) /\selected!_callable=Some(Vptr callable callable_offset) /\
    gateway_presentation_tuple_context python objects tuples decimal_float ledger held reserved captured protected source array displacement
      (Vptr child child_offset)(Vptr tuple tuple_offset)[Some(Vptr child child_offset)]true memory current /\
    gateway_steps backend ge(gateway_live(State f_host_call_objects(fn_body f_host_call_objects)Kstop empty_env parameters before)world)prefix
      (gateway_live(Callstate gateway_presentation_call_definition[Vptr callable callable_offset;Vptr tuple tuple_offset]
        (gateway_presentation_call_cont selected)memory)current) /\
    gateway_steps backend ge(gateway_live(Callstate gateway_presentation_call_definition[Vptr callable callable_offset;Vptr tuple tuple_offset]
      (gateway_presentation_call_cont selected)memory)current)suffix(gateway_live(Returnstate value Kstop after)next).
Proof.
  intros[NEW_BIND[INC_BIND[SET_BIND[CALL_BIND RELEASE_BIND]]]]CALL STACK WELL CAPTURED COUNT ARRAY CALLABLE NOWRAP PROTECTED INITIAL RUN NONNULL.
  destruct NEW_BIND as[new_symbol[NEW_SYMBOL NEW_FUNCTION]].
  destruct INC_BIND as[inc_symbol[INC_SYMBOL INC_FUNCTION]].
  destruct SET_BIND as[set_symbol[SET_SYMBOL SET_FUNCTION]].
  destruct CALL_BIND as[call_symbol[CALL_SYMBOL CALL_FUNCTION]].
  set(base:=fun ledger=>gateway_presentation_context python objects decimal_float ledger held reserved captured protected source
    array displacement(Vptr child child_offset)).
  assert(BASE_CLOSED:forall ledger,gateway_ambient_closed backend(base ledger)).
  { intro ledger;apply(gateway_presentation_context_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation
      thread threads ledger held reserved captured protected source array displacement(Vptr child child_offset)CAPTURED PROTECTED). }
  set(tuple_side:=fun ledger tuple contents unique=>gateway_presentation_tuple_context python objects tuples decimal_float ledger held reserved
    captured protected source array displacement(Vptr child child_offset)tuple contents unique).
  assert(TUPLE_CLOSED:forall ledger tuple contents unique,gateway_ambient_closed backend(tuple_side ledger tuple contents unique)).
  { intros;apply(gateway_presentation_tuple_context_ambient backend python objects tuples decimal_float detached io stable thread_errno heap_allocation
      thread threads presentation ledger held reserved captured protected source array displacement(Vptr child child_offset)tuple contents unique CAPTURED PROTECTED). }
  pose proof(gateway_presentation_new_source backend ge(base older)parameters before new_symbol gateway_presentation_new_definition
    (BASE_CLOSED older)COUNT NEW_SYMBOL NEW_FUNCTION eq_refl)as NEW_SOURCE.
  destruct(gateway_source_sdk_receipt backend ge _ _ _ _ [Vlong Int64.one](gateway_presentation_new_cont parameters)(base older)
    (State f_host_call_objects(fn_body f_host_call_objects)Kstop empty_env parameters before)before world events value after next
    ltac:(exact I)ltac:(cbn;lia)(BASE_CLOSED older)NEW_SOURCE INITIAL RUN)
    as(p0 &r0 &m0 &w0 &tuple_value &m1 &w1 &e0 &EVENTS0 &READY0 &PREFIX0 &OP0 &REST0).
  assert(NEW_NONNULL:tuple_value<>Vnullptr).
  { intro NULL;subst tuple_value;apply NONNULL;eapply gateway_presentation_new_failed;exact REST0. }
  assert(RESULT_FREE:gateway_reference_take(gateway_reference_result(S(gateway_reference_depth context)))(gateway_reference_entries older)=None).
  { apply gateway_reference_take_none;intros entry MEMBER OWNER;destruct(STACK entry MEMBER)as[invocation[name[PLACE SAVED]]];congruence. }
  destruct(gateway_actual_presentation_tuple_credit backend ge python objects tuples
    (fun current object=>gateway_native_private(python current)object)decimal_float presentation older held reserved protected
    (plug_cont(gateway_presentation_new_cont parameters)context)m0 w0 tuple_value m1 w1 e0 WELL
    (gateway_presentation_context_budget _ _ _ _ _ _ _ _ _ _ _ _ _ _ READY0)RESULT_FREE
    (proj2(gateway_presentation_context_scope _ _ _ _ _ _ _ _ _ _ _ _ _ _ READY0))
    (gateway_presentation_context_ready _ _ _ _ _ _ _ _ _ _ _ _ _ _ READY0)
    (gateway_presentation_context_owned _ _ _ _ _ _ _ _ _ _ _ _ _ _ READY0)
    (gateway_presentation_sdk_step backend ge _ _ _ _ _ _ _ _ _ _ _ _ OP0)NEW_NONNULL)
    as(minted &tuple &tuple_offset &TUPLE &MINT &MINT_WELL &MINT_OWNER &MINT_BOUND &MINT_SCOPE &MINT_BUDGET &MINT_READY &CONTENTS &ZERO &ONE &FRAME &BALANCE).
  subst tuple_value.
  assert(MINT_ENTRIES:gateway_reference_entries minted=gateway_reference_entry(gateway_reference_next older)
    (gateway_reference_result(S(gateway_reference_depth context)))(Vptr tuple tuple_offset)::gateway_reference_entries older).
  { exact(proj1(gateway_reference_mint_entries _ _ _ _ MINT)). }
  assert(MINT_NEXT:gateway_reference_next minted=S(gateway_reference_next older))
    by(exact(proj2(gateway_reference_mint_entries _ _ _ _ MINT))).
  assert(MINT_BASE:base minted m1 w1).
  { eapply gateway_presentation_context_from_frame;[exact READY0|exact CAPTURED|exact PROTECTED|exact MINT_READY|
      exact MINT_SCOPE|exact MINT_BUDGET|exact FRAME]. }
  assert(TUPLE_POSITIVE:(0<python_native_strong(python w1)(Vptr tuple tuple_offset))%nat).
  { pose proof(gateway_reference_owned_count_positive _ _ _ _ MINT_OWNER);specialize(MINT_BUDGET(Vptr tuple tuple_offset));lia. }
  assert(MINT_SIDE:tuple_side minted(Vptr tuple tuple_offset)[None]true m1 w1)
    by(exact(conj MINT_BASE(conj CONTENTS(conj TUPLE_POSITIVE(fun _=>ONE))))).
  assert(DIFFERENT:Vptr tuple tuple_offset<>Vptr child child_offset).
  { intro SAME;rewrite SAME in ZERO.
    pose proof(gateway_presentation_context_child_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ READY0 CAPTURED)as[LIVE REST];lia. }
  assert(MINT_TEMP_FREE:forall identifier,gateway_reference_take(gateway_reference_temporary(gateway_reference_depth context)identifier)
      (gateway_reference_entries minted)=None).
  { intro identifier;rewrite MINT_ENTRIES;cbn[gateway_reference_take gateway_reference_entry gateway_reference_owner].
    destruct(gateway_reference_place_eq(gateway_reference_temporary(gateway_reference_depth context)identifier)
      (gateway_reference_result(S(gateway_reference_depth context))));[discriminate|].
    rewrite(gateway_reference_stack_current_vacant context older identifier STACK);reflexivity. }
  destruct(gateway_presentation_actual_capture backend ge python objects decimal_float(tuple_side minted(Vptr tuple tuple_offset)[None]true)
    context parameters _t'1 _arguments(Kseq gateway_presentation_after_new Kstop)(Vptr tuple tuple_offset)m1 w1 r0 value after next
    minted(gateway_reference_next older)(gateway_reference_entries older)held reserved CALL eq_refl(TUPLE_CLOSED _ _ _ _)MINT_SIDE
    ltac:(discriminate)ltac:(intros memory current[GOOD REST];exact(conj(gateway_presentation_context_scope _ _ _ _ _ _ _ _ _ _ _ _ _ _ GOOD)
      (gateway_presentation_context_budget _ _ _ _ _ _ _ _ _ _ _ _ _ _ GOOD)))MINT_WELL MINT_ENTRIES
    (MINT_TEMP_FREE _t'1)(MINT_TEMP_FREE _arguments)REST0)
    as(stored &pc &rc &mc &wc &EVENTSC &CAPTURE_READY &STORED_WELL &STORED_ENTRIES &STORED_NEXT &STORED_SCOPE &STORED_BUDGET &STORED_COUNTS &CAPTURE_PREFIX &CAPTURE_REST).
  assert(STORED_SIDE:tuple_side stored(Vptr tuple tuple_offset)[None]true mc wc)
    by(eapply gateway_presentation_tuple_context_counts;eassumption).
  set(captured_parameters:=gateway_reference_capture_parameters parameters _t'1 _arguments(Vptr tuple tuple_offset)).
  assert(CAPTURE_ARRAY:captured_parameters!_values=Some(Vptr array displacement)).
  { unfold captured_parameters,gateway_reference_capture_parameters;repeat rewrite PTree.gso by discriminate;exact ARRAY. }
  assert(CAPTURE_COUNT:captured_parameters!_count=Some(Vint Int.one)).
  { unfold captured_parameters,gateway_reference_capture_parameters;repeat rewrite PTree.gso by discriminate;exact COUNT. }
  assert(CAPTURE_TUPLE:captured_parameters!_arguments=Some(Vptr tuple tuple_offset))
    by(apply PTree.gss).
  destruct(gateway_presentation_captured_incref_source backend ge(tuple_side stored(Vptr tuple tuple_offset)[None]true)
    captured_parameters array displacement tuple tuple_offset child child_offset mc inc_symbol python_incref_definition
    (TUPLE_CLOSED _ _ _ _)CAPTURE_COUNT CAPTURE_ARRAY CAPTURE_TUPLE NOWRAP
    ltac:(intros memory current[GOOD[CONTENTS_NOW[POSITIVE UNIQUE]]];eapply gateway_presentation_positive_pointer;
      [exact(gateway_presentation_context_ready _ _ _ _ _ _ _ _ _ _ _ _ _ _ GOOD)|exact POSITIVE])
    ltac:(intros memory current[GOOD REST];exact(gateway_presentation_context_array _ _ _ _ _ _ _ _ _ _ _ _ _ _ GOOD))
    INC_SYMBOL INC_FUNCTION eq_refl)
    as(inc_parameters &INC_SOURCE &INC_TUPLE &INC_ARRAY &INC_COUNT &INC_INDEX &INC_CALLABLE).
  destruct(gateway_source_sdk_receipt backend ge _ _ _ _ [Vptr child child_offset](gateway_presentation_incref_cont inc_parameters)
    (tuple_side stored(Vptr tuple tuple_offset)[None]true)
    (State f_host_call_objects Sskip(Kseq gateway_presentation_after_new Kstop)empty_env captured_parameters mc)
    mc wc rc value after next ltac:(exact I)ltac:(cbn;lia)(TUPLE_CLOSED _ _ _ _)INC_SOURCE STORED_SIDE CAPTURE_REST)
    as(p1 &r1 &m2 &w2 &ignored &m3 &w3 &e1 &EVENTS1 &READY2 &PREFIX1 &OP1 &REST1).
  assert(CELL_FREE:gateway_reference_take(gateway_reference_cell array(Ptrofs.unsigned displacement))(gateway_reference_entries stored)=None).
  { apply gateway_reference_take_none;intros entry MEMBER OWNER;rewrite STORED_ENTRIES in MEMBER;destruct MEMBER as[HEAD|OLD].
    - subst entry;discriminate.
    - destruct(STACK entry OLD)as[invocation[name[PLACE SAVED]]];congruence. }
  assert(STORED_OWNER:gateway_reference_owns stored(gateway_reference_temporary(gateway_reference_depth context)_arguments)
    (gateway_reference_next older)(Vptr tuple tuple_offset))by(unfold gateway_reference_owns;rewrite STORED_ENTRIES;left;reflexivity).
  assert(NATIVE2:gateway_native_private(python w2)array).
  { destruct READY2 as[GOOD REST].
    apply(proj1(gateway_presentation_context_owned _ _ _ _ _ _ _ _ _ _ _ _ _ _ GOOD array(Ptrofs.unsigned displacement)
      (PROTECTED(Ptrofs.unsigned displacement)ltac:(lia)))). }
  destruct(gateway_actual_presentation_argument_credit backend ge python objects tuples decimal_float references metadata
    stored held reserved context inc_parameters(gateway_reference_next older)(Vptr tuple tuple_offset)[None]array displacement
    child child_offset m2 w2 ignored m3 w3 e1 STORED_WELL
    (gateway_presentation_context_budget _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 READY2))CELL_FREE
    (proj2(gateway_presentation_context_scope _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 READY2)))
    (gateway_presentation_context_ready _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 READY2))NATIVE2
    ltac:(split;[rewrite INC_ARRAY;exact CAPTURE_ARRAY|];split;[exact INC_INDEX|];split;
      [exact(gateway_presentation_context_array _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 READY2))|exact NOWRAP])INC_TUPLE STORED_OWNER
    (proj1(proj2 READY2))DIFFERENT(gateway_presentation_context_child_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 READY2)CAPTURED)
    (gateway_presentation_context_immutable _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 READY2))
    (gateway_presentation_sdk_step backend ge _ _ _ _ _ _ _ _ _ _ _ _ OP1))
    as(incremented &INC_MINT &INC_WELL &INC_OWNER &INC_BOUND &INC_SCOPE &INC_BUDGET &INC_READY &INC_CONTENTS &INC_STRONG &INC_IMMUTABLE &INC_FRAME &INC_NATIVE &INC_BALANCE).
  assert(INC_ENTRIES:gateway_reference_entries incremented=gateway_reference_entry(gateway_reference_next stored)
    (gateway_reference_cell array(Ptrofs.unsigned displacement))(Vptr child child_offset)::gateway_reference_entries stored)
    by(exact(proj1(gateway_reference_mint_entries _ _ _ _ INC_MINT))).
  assert(INC_NEXT:gateway_reference_next incremented=S(gateway_reference_next stored))
    by(exact(proj2(gateway_reference_mint_entries _ _ _ _ INC_MINT))).
  assert(INC_OPERATION:gateway_object_operation backend gateway_api_incref[Vptr child child_offset]m2 w2 ignored m3 w3 e1).
  { eapply gateway_object_operation_actual;[reflexivity|].
    exact(gateway_presentation_sdk_step backend ge _ _ _ _ _ (gateway_presentation_incref_cont inc_parameters) _ _ _ _ _ _ OP1). }
  assert(INC_BASE:base incremented m3 w3).
  { eapply gateway_presentation_context_effect;[exact(proj1 READY2)|exact CAPTURED|exact PROTECTED|exact INC_READY|exact INC_SCOPE|
      exact INC_BUDGET| | | |].
    - pose proof(gateway_runtime_incref_objects _ _ _ references m2 w2(Vptr child child_offset)ignored m3 w3 e1
        (gateway_presentation_context_ready _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 READY2))
        (gateway_presentation_context_child_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 READY2)CAPTURED)INC_OPERATION)as[RET[RD[VALUES REST]]];exact VALUES.
    - pose proof(gateway_runtime_incref_objects _ _ _ references m2 w2(Vptr child child_offset)ignored m3 w3 e1
        (gateway_presentation_context_ready _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 READY2))
        (gateway_presentation_context_child_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 READY2)CAPTURED)INC_OPERATION)as[RET[RD[VALUES[PRIVACY REST]]]];exact PRIVACY.
    - eapply Mem.unchanged_on_implies;[exact INC_FRAME|].
      intros object position MEMBER LIVE;exact(proj1(gateway_presentation_context_owned _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 READY2)object position MEMBER)).
    - intros object position MEMBER;apply INC_NATIVE.
      exact(proj1(gateway_presentation_context_owned _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 READY2)object position MEMBER)). }
  assert(INC_POSITIVE:(0<python_native_strong(python w3)(Vptr tuple tuple_offset))%nat).
  { pose proof(gateway_reference_owned_count_positive _ _ _ _ STORED_OWNER)as POSITIVE.
    assert(OWNED:gateway_reference_owns incremented(gateway_reference_temporary(gateway_reference_depth context)_arguments)
      (gateway_reference_next older)(Vptr tuple tuple_offset))by(unfold gateway_reference_owns;rewrite INC_ENTRIES;right;exact STORED_OWNER).
    pose proof(gateway_reference_owned_count_positive _ _ _ _ OWNED);specialize(INC_BUDGET(Vptr tuple tuple_offset));lia. }
  assert(INC_SIDE:tuple_side incremented(Vptr tuple tuple_offset)[None]true m3 w3).
  { split;[exact INC_BASE|]. split;[exact INC_CONTENTS|]. split;[exact INC_POSITIVE|].
    intro SAME;rewrite INC_STRONG;apply(proj2(proj2(proj2 READY2)));reflexivity. }
  destruct(gateway_presentation_set_source backend ge(tuple_side incremented(Vptr tuple tuple_offset)[None]true)inc_parameters
    array displacement tuple tuple_offset child child_offset ignored m3 set_symbol gateway_presentation_set_definition
    (TUPLE_CLOSED _ _ _ _)INC_INDEX ltac:(rewrite INC_ARRAY;exact CAPTURE_ARRAY)INC_TUPLE NOWRAP
    ltac:(intros memory current[GOOD REST];exact(gateway_presentation_context_array _ _ _ _ _ _ _ _ _ _ _ _ _ _ GOOD))
    SET_SYMBOL SET_FUNCTION eq_refl)
    as(set_parameters &SET_SOURCE &SET_TUPLE &SET_ARRAY &SET_COUNT &SET_INDEX &SET_CALLABLE).
  destruct(gateway_source_sdk_receipt backend ge _ _ _ _ [Vptr tuple tuple_offset;Vlong Int64.zero;Vptr child child_offset]
    (gateway_presentation_set_cont set_parameters)(tuple_side incremented(Vptr tuple tuple_offset)[None]true)
    (Returnstate ignored(gateway_presentation_incref_cont inc_parameters)m3)m3 w3 r1 value after next
    ltac:(exact I)ltac:(cbn;lia)(TUPLE_CLOSED _ _ _ _)SET_SOURCE INC_SIDE REST1)
    as(p2 &r2 &m4 &w4 &status &m5 &w5 &e2 &EVENTS2 &READY4 &PREFIX2 &OP2 &REST2).
  assert(HELD_DIFFERENT:forall current,In current held->gateway_held_ticket current<>gateway_reference_next stored).
  { intros current MEMBER SAME.
    destruct(proj1(Forall_forall _ _)(proj2(gateway_presentation_context_scope _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 READY2)))current MEMBER)as[[place TICKET]REST].
    destruct STORED_WELL as[NODUP[PLACES LIMIT]].
    apply Forall_forall with(x:=gateway_reference_entry(gateway_held_ticket current)place(gateway_held_object current))in LIMIT;[cbn in LIMIT;lia|exact TICKET]. }
  assert(TUPLE_OWNER:gateway_reference_owns incremented(gateway_reference_temporary(gateway_reference_depth context)_arguments)
    (gateway_reference_next older)(Vptr tuple tuple_offset))by(unfold gateway_reference_owns;rewrite INC_ENTRIES;right;exact STORED_OWNER).
  destruct(gateway_actual_presentation_argument_steal backend ge python objects tuples
    (fun current object=>gateway_native_private(python current)object)decimal_float presentation incremented held reserved protected context
    set_parameters(gateway_reference_next older)(Vptr tuple tuple_offset)array displacement child child_offset
    (gateway_reference_next stored)captured m4 w4 status m5 w5 e2 INC_WELL
    (gateway_presentation_context_budget _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 READY4))INC_OWNER
    (gateway_presentation_context_scope _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 READY4))HELD_DIFFERENT CAPTURED
    (gateway_presentation_context_reached _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 READY4))
    (gateway_presentation_context_ready _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 READY4))
    (gateway_presentation_context_owned _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 READY4))
    ltac:(split;[rewrite SET_ARRAY,INC_ARRAY;exact CAPTURE_ARRAY|];split;[rewrite SET_INDEX;exact INC_INDEX|];split;
      [exact(gateway_presentation_context_array _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 READY4))|exact NOWRAP])
    ltac:(rewrite SET_TUPLE;exact INC_TUPLE)TUPLE_OWNER(proj1(proj2 READY4))
    (gateway_presentation_positive_live _ _ _ _(gateway_presentation_context_ready _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 READY4))(proj1(proj2(proj2 READY4))))
    (proj2(proj2(proj2 READY4))eq_refl)(gateway_presentation_context_child_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 READY4)CAPTURED)
    (gateway_presentation_context_immutable _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 READY4))
    (gateway_presentation_sdk_step backend ge _ _ _ _ _ _ _ _ _ _ _ _ OP2))
    as(installed &STATUS &RELEASE &INSTALLED_WELL &INSTALLED_SCOPE &INSTALLED_BUDGET &INSTALLED_READY &INSTALLED_CONTENTS &INSTALLED_STRONG &IMMUTABLE5 &REACHED5 &FRAME5 &BALANCE5 &RETAINED5).
  assert(INSTALLED_ENTRIES:gateway_reference_entries installed=gateway_reference_entries stored).
  { exact(proj1(gateway_reference_head_release incremented installed(gateway_reference_entries stored)(gateway_reference_next stored)
      (gateway_reference_cell array(Ptrofs.unsigned displacement))(Vptr child child_offset)INC_ENTRIES RELEASE)). }
  assert(INSTALLED_NEXT:gateway_reference_next installed=S(S(gateway_reference_next older))).
  { pose proof(proj2(gateway_reference_head_release incremented installed(gateway_reference_entries stored)(gateway_reference_next stored)
      (gateway_reference_cell array(Ptrofs.unsigned displacement))(Vptr child child_offset)INC_ENTRIES RELEASE));congruence. }
  assert(INSTALLED_BASE:base installed m5 w5)
    by(eapply gateway_presentation_context_from_frame;[exact(proj1 READY4)|exact CAPTURED|exact PROTECTED|exact INSTALLED_READY|
      exact INSTALLED_SCOPE|exact INSTALLED_BUDGET|exact FRAME5]).
  assert(INSTALLED_POSITIVE:(0<python_native_strong(python w5)(Vptr tuple tuple_offset))%nat).
  { assert(OWNED:gateway_reference_owns installed(gateway_reference_temporary(gateway_reference_depth context)_arguments)
      (gateway_reference_next older)(Vptr tuple tuple_offset))by(unfold gateway_reference_owns;rewrite INSTALLED_ENTRIES;exact STORED_OWNER).
    pose proof(gateway_reference_owned_count_positive _ _ _ _ OWNED);specialize(INSTALLED_BUDGET(Vptr tuple tuple_offset));lia. }
  assert(INSTALLED_SIDE:tuple_side installed(Vptr tuple tuple_offset)[Some(Vptr child child_offset)]true m5 w5)
    by(exact(conj INSTALLED_BASE(conj INSTALLED_CONTENTS(conj INSTALLED_POSITIVE(fun _=>INSTALLED_STRONG))))).
  subst status.
  destruct(gateway_presentation_call_source backend ge(tuple_side installed(Vptr tuple tuple_offset)[Some(Vptr child child_offset)]true)
    set_parameters tuple tuple_offset callable callable_offset m5 call_symbol gateway_presentation_call_definition(TUPLE_CLOSED _ _ _ _)
    ltac:(rewrite SET_INDEX;exact INC_INDEX)ltac:(rewrite SET_COUNT,INC_COUNT;exact CAPTURE_COUNT)
    ltac:(rewrite SET_TUPLE;exact INC_TUPLE)
    ltac:(rewrite SET_CALLABLE,INC_CALLABLE;unfold captured_parameters,gateway_reference_capture_parameters;
      repeat rewrite PTree.gso by discriminate;exact CALLABLE)CALL_SYMBOL CALL_FUNCTION eq_refl)
    as(selected &CALL_SOURCE &CALL_TUPLE &CALL_ARRAY &CALL_COUNT &CALL_INDEX &CALL_CALLABLE).
  destruct(gateway_source_path_cut backend ge _ _ _ _ _ _ CALL_SOURCE m5 w5 r2 value after next INSTALLED_SIDE REST2)
    as(p3 &r3 &m6 &w6 &EVENTS3 &QUIET3 &PREFIX3 &READY6 &REST3).
  set(prefix:=p0++gateway_primitive e0::pc++p1++gateway_primitive e1::p2++gateway_primitive e2::p3).
  exists tuple,tuple_offset,installed,selected,prefix,r3,m6,w6.
  split.
  - unfold prefix;rewrite EVENTS0,EVENTSC,EVENTS1,EVENTS2,EVENTS3;
      repeat first[rewrite<-app_assoc|progress cbn[app]];reflexivity.
  - split;[exact INSTALLED_WELL|]. split;[congruence|]. split;[exact INSTALLED_NEXT|]. split.
    + rewrite CALL_TUPLE,SET_TUPLE;exact INC_TUPLE.
    + split;[rewrite CALL_CALLABLE,SET_CALLABLE,INC_CALLABLE;unfold captured_parameters,gateway_reference_capture_parameters;
        repeat rewrite PTree.gso by discriminate;exact CALLABLE|]. split;[exact READY6|]. split;[|exact REST3].
      unfold prefix;eapply gateway_steps_append;[exact PREFIX0|]. econstructor;[apply gateway_presentation_sdk_step;exact OP0|].
      eapply gateway_steps_append;[exact CAPTURE_PREFIX|]. eapply gateway_steps_append;[exact PREFIX1|].
      econstructor;[apply gateway_presentation_sdk_step;exact OP1|]. eapply gateway_steps_append;[exact PREFIX2|].
      econstructor;[apply gateway_presentation_sdk_step;exact OP2|exact PREFIX3].
Qed.
