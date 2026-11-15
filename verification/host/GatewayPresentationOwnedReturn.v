(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The observed callback result keeps its own reference through
   tuple cleanup. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallContexts.
From HostGateway Require Import GatewaySource GatewayMachine GatewayRuntime GatewayPython GatewayObjects GatewayReferences
  GatewayValue GatewayObjectDiscipline GatewayObjectThreads GatewayThreadRuntime GatewayStreamInterface GatewayFramedRuntime
  GatewayContexts GatewaySourcePaths GatewaySourceSDKReceipt GatewaySourceSegments GatewayReadonly GatewayPure GatewayValueReturns
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceStackBound GatewayReferenceFrames
  GatewayReferenceNormalForm GatewayReferenceHeld GatewayReferenceThreads GatewayReferenceCapture GatewayReferenceMoves
  GatewayReferenceContextReturns GatewayOutcomeCopyCapture GatewayPresentationRuntime GatewayPresentationSource GatewayPresentationTrace
  GatewayPresentationCapturedSource GatewayPresentationCredits GatewayPresentationContext GatewayPresentationCapture GatewayPresentationOwnedPrefix.
Import ListNotations.
Local Close Scope lean_scope.

Lemma gateway_presentation_release_second ledger final tail first_ticket first_owner first tuple_ticket tuple_owner tuple:
  first_owner<>tuple_owner ->
  gateway_reference_entries ledger=gateway_reference_entry first_ticket first_owner first::gateway_reference_entry tuple_ticket tuple_owner tuple::tail ->
  gateway_reference_apply(gateway_reference_release tuple_owner tuple)(gateway_reference_valid ledger)=gateway_reference_valid final ->
  gateway_reference_entries final=gateway_reference_entry first_ticket first_owner first::tail /\gateway_reference_next final=gateway_reference_next ledger.
Proof.
  intros DIFFERENT ENTRIES;unfold gateway_reference_apply;rewrite ENTRIES;
    cbn[gateway_reference_take gateway_reference_entry gateway_reference_owner gateway_reference_pointer].
  destruct(gateway_reference_place_eq tuple_owner first_owner);[congruence|].
  destruct(gateway_reference_place_eq tuple_owner tuple_owner);[|congruence].
  cbn[gateway_reference_pointer gateway_reference_entry].
  destruct(Val.eq tuple tuple);[|congruence]. intro SAME;injection SAME as SAME;subst final;split;reflexivity.
Qed.

Theorem gateway_actual_owned_presentation_return {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects tuples decimal_float detached io stable thread_errno heap_allocation
    (thread:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (threads:gateway_reference_thread_contract backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (presentation:gateway_presentation_runtime backend python objects tuples(fun current object=>gateway_native_private(python current)object))
    context older ledger held reserved captured protected source parameters array displacement child child_offset callable callable_offset
    tuple tuple_offset tuple_ticket before world events value after next:
  gateway_presentation_bindings ge ->is_call_cont context ->gateway_reference_stack_bound context older ->
  gateway_reference_ledger_well_formed ledger ->In captured held ->In(Vptr callable callable_offset)reserved ->
  (forall current,In current held->(gateway_held_ticket current<tuple_ticket)%nat) ->
  gateway_reference_entries ledger=gateway_reference_entry tuple_ticket
    (gateway_reference_temporary(gateway_reference_depth context)_arguments)(Vptr tuple tuple_offset)::gateway_reference_entries older ->
  parameters!_arguments=Some(Vptr tuple tuple_offset) ->parameters!_callable=Some(Vptr callable callable_offset) ->
  (forall position,(Ptrofs.unsigned displacement<=position<Ptrofs.unsigned displacement+8)%Z->protected array position) ->
  gateway_presentation_tuple_context python objects tuples decimal_float ledger held reserved captured protected source array displacement
    (Vptr child child_offset)(Vptr tuple tuple_offset)[Some(Vptr child child_offset)]true before world ->
  gateway_steps backend ge(gateway_live(Callstate gateway_presentation_call_definition[Vptr callable callable_offset;Vptr tuple tuple_offset]
    (gateway_presentation_call_cont parameters)before)world)events(gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->
  exists final object offset prefix suffix callback_memory callback_world returned_memory returned_world observed,
    value=Vptr object offset /\events=prefix++gateway_primitive observed::suffix /\
    gateway_presentation_operation backend gateway_presentation_call[Vptr callable callable_offset;Vptr tuple tuple_offset]
      callback_memory callback_world value returned_memory returned_world observed /\
    gateway_reference_ledger_well_formed final /\
    gateway_reference_entries final=gateway_reference_entry(gateway_reference_next ledger)
      (gateway_reference_result(gateway_reference_depth context))value::gateway_reference_entries older /\
    gateway_reference_next final=S(gateway_reference_next ledger) /\
    gateway_presentation_context python objects decimal_float final held reserved captured protected source array displacement
      (Vptr child child_offset)after next /\
    gateway_reference_source_bound ge(Returnstate value context after)final.
Proof.
  intros[NEW_BIND[INC_BIND[SET_BIND[CALL_BIND RELEASE_BIND]]]]CALL STACK WELL CAPTURED RESERVED HELD_BELOW ENTRIES ARGUMENTS CALLABLE
    PROTECTED INITIAL RUN NONNULL.
  destruct RELEASE_BIND as[release_symbol[RELEASE_SYMBOL RELEASE_FUNCTION]].
  set(base:=fun ledger=>gateway_presentation_context python objects decimal_float ledger held reserved captured protected source
    array displacement(Vptr child child_offset)).
  set(tuple_side:=fun ledger tuple contents unique=>gateway_presentation_tuple_context python objects tuples decimal_float ledger held reserved
    captured protected source array displacement(Vptr child child_offset)tuple contents unique).
  assert(BASE_CLOSED:forall current,gateway_ambient_closed backend(base current)).
  { intro current;apply(gateway_presentation_context_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation
      thread threads current held reserved captured protected source array displacement(Vptr child child_offset)CAPTURED PROTECTED). }
  assert(TUPLE_CLOSED:forall current selected contents unique,gateway_ambient_closed backend(tuple_side current selected contents unique)).
  { intros;apply(gateway_presentation_tuple_context_ambient backend python objects tuples decimal_float detached io stable thread_errno heap_allocation
      thread threads presentation current held reserved captured protected source array displacement(Vptr child child_offset)selected contents unique CAPTURED PROTECTED). }
  assert(CALL_SOURCE:gateway_source_path backend ge gateway_presentation_call_definition[Vptr callable callable_offset;Vptr tuple tuple_offset]
    (gateway_presentation_call_cont parameters)(tuple_side ledger(Vptr tuple tuple_offset)[Some(Vptr child child_offset)]true)
    (Callstate gateway_presentation_call_definition[Vptr callable callable_offset;Vptr tuple tuple_offset](gateway_presentation_call_cont parameters)before)
    (tuple_side ledger(Vptr tuple tuple_offset)[Some(Vptr child child_offset)]true))by(constructor;auto).
  destruct(gateway_source_sdk_receipt backend ge _ _ _ _ [Vptr callable callable_offset;Vptr tuple tuple_offset](gateway_presentation_call_cont parameters)
    (tuple_side ledger(Vptr tuple tuple_offset)[Some(Vptr child child_offset)]true)
    (Callstate gateway_presentation_call_definition[Vptr callable callable_offset;Vptr tuple tuple_offset](gateway_presentation_call_cont parameters)before)
    before world events value after next ltac:(exact I)ltac:(cbn;lia)(TUPLE_CLOSED _ _ _ _)CALL_SOURCE INITIAL RUN)
    as(p0 &r0 &m0 &w0 &returned &m1 &w1 &e0 &EVENTS0 &READY0 &PREFIX0 &OP0 &REST0).
  assert(RETURNED_NONNULL:returned<>Vnullptr).
  { intro NULL;subst returned;apply NONNULL.
    eapply gateway_presentation_call_failed;[exact ARGUMENTS|exact RELEASE_SYMBOL|exact RELEASE_FUNCTION|exact REST0]. }
  assert(RESULT_FREE:gateway_reference_take(gateway_reference_result(S(gateway_reference_depth context)))(gateway_reference_entries ledger)=None).
  { apply gateway_reference_take_none;intros entry MEMBER OWNER;rewrite ENTRIES in MEMBER;destruct MEMBER as[HEAD|OLD].
    - subst entry;discriminate.
    - destruct(STACK entry OLD)as[invocation[name[PLACE SAVED]]];congruence. }
  assert(CALLABLE_POSITIVE:(0<python_native_strong(python w0)(Vptr callable callable_offset))%nat).
  { pose proof(gateway_presentation_context_budget _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 READY0)(Vptr callable callable_offset)).
    assert(COUNT:(0<count_occ Val.eq reserved(Vptr callable callable_offset))%nat)by(apply count_occ_In;exact RESERVED);lia. }
  destruct(gateway_actual_presentation_callback_credit backend ge python objects tuples(fun current object=>gateway_native_private(python current)object)
    decimal_float presentation ledger held reserved protected(plug_cont(gateway_presentation_call_cont parameters)context)
    (Vptr callable callable_offset)(Vptr tuple tuple_offset)(Vptr child child_offset)captured m0 w0 returned m1 w1 e0
    WELL(gateway_presentation_context_budget _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 READY0))RESULT_FREE
    (gateway_presentation_context_scope _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 READY0))CAPTURED
    (gateway_presentation_context_reached _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 READY0))
    (gateway_presentation_context_ready _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 READY0))
    (gateway_presentation_context_owned _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 READY0))
    (gateway_presentation_positive_live _ _ _ _(gateway_presentation_context_ready _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 READY0))CALLABLE_POSITIVE)
    (gateway_presentation_positive_live _ _ _ _(gateway_presentation_context_ready _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 READY0))(proj1(proj2(proj2 READY0))))
    CALLABLE_POSITIVE(proj1(proj2(proj2 READY0)))(proj1(proj2 READY0))
    (gateway_presentation_context_immutable _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 READY0))
    (gateway_presentation_sdk_step backend ge _ _ _ _ _ _ _ _ _ _ _ _ OP0)RETURNED_NONNULL)
    as(minted &object &offset &RETURNED &MINT &MINT_WELL &MINT_OWNER &MINT_BOUND &MINT_SCOPE &MINT_BUDGET &MINT_READY &MINT_LIVE &CONTENTS &IMMUTABLE1 &REACHED1 &FRAME1 &BALANCE1).
  subst returned.
  assert(MINT_ENTRIES:gateway_reference_entries minted=gateway_reference_entry(gateway_reference_next ledger)
    (gateway_reference_result(S(gateway_reference_depth context)))(Vptr object offset)::gateway_reference_entries ledger)
    by(exact(proj1(gateway_reference_mint_entries _ _ _ _ MINT))).
  assert(MINT_NEXT:gateway_reference_next minted=S(gateway_reference_next ledger))
    by(exact(proj2(gateway_reference_mint_entries _ _ _ _ MINT))).
  assert(MINT_BASE:base minted m1 w1)
    by(eapply gateway_presentation_context_from_frame;[exact(proj1 READY0)|exact CAPTURED|exact PROTECTED|exact MINT_READY|exact MINT_SCOPE|exact MINT_BUDGET|exact FRAME1]).
  assert(TUPLE_POSITIVE:(0<python_native_strong(python w1)(Vptr tuple tuple_offset))%nat).
  { assert(OWNED:gateway_reference_owns minted(gateway_reference_temporary(gateway_reference_depth context)_arguments)tuple_ticket(Vptr tuple tuple_offset))
      by(unfold gateway_reference_owns;rewrite MINT_ENTRIES,ENTRIES;right;left;reflexivity).
    pose proof(gateway_reference_owned_count_positive _ _ _ _ OWNED);specialize(MINT_BUDGET(Vptr tuple tuple_offset));lia. }
  assert(MINT_SIDE:tuple_side minted(Vptr tuple tuple_offset)[Some(Vptr child child_offset)]false m1 w1).
  { split;[exact MINT_BASE|]. split;[exact CONTENTS|]. split;[exact TUPLE_POSITIVE|].
    intro BAD;discriminate BAD. }
  assert(MINT_TEMP_FREE:forall identifier,identifier<>_arguments ->
    gateway_reference_take(gateway_reference_temporary(gateway_reference_depth context)identifier)(gateway_reference_entries minted)=None).
  { intros identifier DIFFERENT;apply gateway_reference_take_none;intros entry MEMBER OWNER;rewrite MINT_ENTRIES,ENTRIES in MEMBER.
    destruct MEMBER as[HEAD|[TUPLE|OLD]].
    - subst entry;discriminate.
    - subst entry;cbn[gateway_reference_entry gateway_reference_owner]in OWNER;congruence.
    - apply(proj1(gateway_reference_take_none _ _)(gateway_reference_stack_current_vacant context older identifier STACK)entry OLD OWNER). }
  destruct(gateway_presentation_actual_capture backend ge python objects decimal_float
    (tuple_side minted(Vptr tuple tuple_offset)[Some(Vptr child child_offset)]false)context parameters _t'3 _result
    (Kseq gateway_presentation_after_call Kstop)(Vptr object offset)m1 w1 r0 value after next minted(gateway_reference_next ledger)
    (gateway_reference_entries ledger)held reserved CALL eq_refl(TUPLE_CLOSED _ _ _ _)MINT_SIDE ltac:(discriminate)
    ltac:(intros memory current[GOOD REST];exact(conj(gateway_presentation_context_scope _ _ _ _ _ _ _ _ _ _ _ _ _ _ GOOD)
      (gateway_presentation_context_budget _ _ _ _ _ _ _ _ _ _ _ _ _ _ GOOD)))MINT_WELL MINT_ENTRIES
    (MINT_TEMP_FREE _t'3 ltac:(discriminate))(MINT_TEMP_FREE _result ltac:(discriminate))REST0)
    as(stored &pc &rc &mc &wc &EVENTSC &CAPTURE_READY &STORED_WELL &STORED_ENTRIES &STORED_NEXT &STORED_SCOPE &STORED_BUDGET &STORED_COUNTS &CAPTURE_PREFIX &CAPTURE_REST).
  assert(STORED_SIDE:tuple_side stored(Vptr tuple tuple_offset)[Some(Vptr child child_offset)]false mc wc)
    by(eapply gateway_presentation_tuple_context_counts;eassumption).
  set(captured_parameters:=gateway_reference_capture_parameters parameters _t'3 _result(Vptr object offset)).
  assert(CAPTURE_ARGUMENTS:captured_parameters!_arguments=Some(Vptr tuple tuple_offset)).
  { unfold captured_parameters,gateway_reference_capture_parameters;repeat rewrite PTree.gso by discriminate;exact ARGUMENTS. }
  assert(CAPTURE_RESULT:captured_parameters!_result=Some(Vptr object offset))by(apply PTree.gss).
  destruct(gateway_presentation_captured_release_source backend ge(tuple_side stored(Vptr tuple tuple_offset)[Some(Vptr child child_offset)]false)
    captured_parameters tuple tuple_offset(Vptr object offset)mc release_symbol gateway_presentation_release_definition
    (TUPLE_CLOSED _ _ _ _)CAPTURE_ARGUMENTS CAPTURE_RESULT RELEASE_SYMBOL RELEASE_FUNCTION eq_refl)
    as(release_parameters &RELEASE_SOURCE &RELEASE_ARGUMENTS &RELEASE_RESULT &RELEASE_CALLABLE).
  destruct(gateway_source_sdk_receipt backend ge _ _ _ _ [Vptr tuple tuple_offset](gateway_presentation_release_cont release_parameters)
    (tuple_side stored(Vptr tuple tuple_offset)[Some(Vptr child child_offset)]false)
    (State f_host_call_objects Sskip(Kseq gateway_presentation_after_call Kstop)empty_env captured_parameters mc)
    mc wc rc value after next ltac:(exact I)ltac:(cbn;lia)(TUPLE_CLOSED _ _ _ _)RELEASE_SOURCE STORED_SIDE CAPTURE_REST)
    as(p1 &r1 &m2 &w2 &ignored &m3 &w3 &e1 &EVENTS1 &READY2 &PREFIX1 &OP1 &REST1).
  assert(TUPLE_OWNER:gateway_reference_owns stored(gateway_reference_temporary(gateway_reference_depth context)_arguments)tuple_ticket(Vptr tuple tuple_offset))
    by(unfold gateway_reference_owns;rewrite STORED_ENTRIES,ENTRIES;right;left;reflexivity).
  destruct(gateway_actual_presentation_tuple_release backend ge python objects tuples(fun current object=>gateway_native_private(python current)object)
    decimal_float presentation stored held reserved protected context release_parameters tuple_ticket(Vptr tuple tuple_offset)
    [Some(Vptr child child_offset)]m2 w2 ignored m3 w3 e1 STORED_WELL
    (gateway_presentation_context_budget _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 READY2))TUPLE_OWNER
    (proj2(gateway_presentation_context_scope _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 READY2)))
    ltac:(intros current MEMBER SAME;pose proof(HELD_BELOW current MEMBER);lia)
    (gateway_presentation_context_ready _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 READY2))
    (gateway_presentation_context_owned _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 READY2))(proj1(proj2 READY2))
    ltac:(right;exists(Vptr child child_offset);split;[reflexivity|exact(gateway_presentation_context_immutable _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 READY2))])
    ltac:(rewrite RELEASE_ARGUMENTS;exact CAPTURE_ARGUMENTS)
    (gateway_presentation_sdk_step backend ge _ _ _ _ _ _ _ _ _ _ _ _ OP1))
    as(released &RELEASE &RELEASED_WELL &RELEASED_SCOPE &RELEASED_BUDGET &RELEASED_READY &FRAME3 &BALANCE3 &RETAINED3).
  assert(RELEASED_ENTRIES:gateway_reference_entries released=gateway_reference_entry(gateway_reference_next ledger)
    (gateway_reference_temporary(gateway_reference_depth context)_result)(Vptr object offset)::gateway_reference_entries older).
  { exact(proj1(gateway_presentation_release_second stored released(gateway_reference_entries older)(gateway_reference_next ledger)
      (gateway_reference_temporary(gateway_reference_depth context)_result)(Vptr object offset)tuple_ticket
      (gateway_reference_temporary(gateway_reference_depth context)_arguments)(Vptr tuple tuple_offset)ltac:(discriminate)
      ltac:(rewrite STORED_ENTRIES,ENTRIES;reflexivity)RELEASE)). }
  assert(RELEASED_NEXT:gateway_reference_next released=S(gateway_reference_next ledger)).
  { pose proof(proj2(gateway_presentation_release_second stored released(gateway_reference_entries older)(gateway_reference_next ledger)
      (gateway_reference_temporary(gateway_reference_depth context)_result)(Vptr object offset)tuple_ticket
      (gateway_reference_temporary(gateway_reference_depth context)_arguments)(Vptr tuple tuple_offset)ltac:(discriminate)
      ltac:(rewrite STORED_ENTRIES,ENTRIES;reflexivity)RELEASE));congruence. }
  assert(RELEASED_BASE:base released m3 w3)
    by(eapply gateway_presentation_context_from_frame;[exact(proj1 READY2)|exact CAPTURED|exact PROTECTED|exact RELEASED_READY|
      exact RELEASED_SCOPE|exact RELEASED_BUDGET|exact FRAME3]).
  destruct(gateway_pure_path_ready_return backend ge(base released)(BASE_CLOSED released)
    (Returnstate ignored(gateway_presentation_release_cont release_parameters)m3)(Vptr object offset)w3 r1 value after next
    (gateway_presentation_return_pure ge release_parameters ignored(Vptr object offset)m3 RELEASE_RESULT ltac:(right;repeat eexists))RELEASED_BASE REST1)
    as[SAME[FINAL_BASE QUIET]].
  subst value.
  pose proof(gateway_presentation_released_return_source backend ge(base released)release_parameters ignored m3(BASE_CLOSED released))as RETURN_SOURCE.
  destruct(gateway_source_segment_cut backend ge _ _ _ _ RETURN_SOURCE m3 w3 r1(Vptr object offset)after next RELEASED_BASE REST1)
    as(pr &rr &mr &wr &EVENTSR &QUIETR &PREFIXR &READYR &RESTR).
  assert(RESULT_OWNER:gateway_reference_owns released(gateway_reference_temporary(gateway_reference_depth context)_result)
    (gateway_reference_next ledger)(Vptr object offset))by(unfold gateway_reference_owns;rewrite RELEASED_ENTRIES;left;reflexivity).
  assert(RETURN_FREE:gateway_reference_take(gateway_reference_result(gateway_reference_depth context))(gateway_reference_entries released)=None).
  { apply gateway_reference_take_none;intros entry MEMBER OWNER;rewrite RELEASED_ENTRIES in MEMBER;destruct MEMBER as[HEAD|OLD];
      [subst entry;discriminate|destruct(STACK entry OLD)as[invocation[name[PLACE SAVED]]];congruence]. }
  destruct(gateway_reference_context_source_return backend ge context f_host_call_objects(Etempvar _result(tptr(Tstruct __object noattr)))_result
    Kstop empty_env release_parameters(Vptr object offset)mr wr rr(Vptr object offset)after next released(gateway_reference_next ledger)
    eq_refl eq_refl ltac:(intros;apply old_expression_value,value_temp;exact RELEASE_RESULT)ltac:(intros;inversion H;reflexivity)
    RELEASED_WELL RESULT_OWNER RETURN_FREE RESTR)
    as(final &RETURN_IDENTITY &RETURN_EXECUTION &RETURN_MOVE &FINAL_WELL &FINAL_OWNER &FINAL_COUNTS).
  change(gateway_reference_apply(gateway_reference_move(gateway_reference_temporary(gateway_reference_depth context)_result)
    (gateway_reference_result(gateway_reference_depth context)))(gateway_reference_valid released)=gateway_reference_valid final)in RETURN_MOVE.
  destruct(gateway_reference_move_scope python objects decimal_float released(gateway_reference_temporary(gateway_reference_depth context)_result)
    (gateway_reference_result(gateway_reference_depth context))(gateway_reference_next ledger)(Vptr object offset)held next
    RELEASED_WELL RESULT_OWNER RETURN_FREE(gateway_presentation_context_scope _ _ _ _ _ _ _ _ _ _ _ _ _ _ FINAL_BASE))
    as(returned &MOVE &RETURNED_WELL &RETURNED_OWNER &FINAL_SCOPE &COUNTS &RETAINED).
  rewrite RETURN_MOVE in MOVE;injection MOVE as EQUAL;subst returned.
  destruct(gateway_reference_head_move released final(gateway_reference_entries older)(gateway_reference_next ledger)
    (gateway_reference_temporary(gateway_reference_depth context)_result)(gateway_reference_result(gateway_reference_depth context))
    (Vptr object offset)RELEASED_ENTRIES RETURN_MOVE)as[FINAL_ENTRIES FINAL_NEXT].
  exists final,object,offset,p0,r0,m0,w0,m1,w1,e0.
  split;[reflexivity|]. split;[exact EVENTS0|]. split.
  - exists gateway_presentation_call_definition;split;[reflexivity|exact OP0].
  - split;[exact FINAL_WELL|]. split;[exact FINAL_ENTRIES|]. split;[congruence|]. split.
    + eapply gateway_presentation_context_counts;[exact FINAL_BASE|exact FINAL_SCOPE|exact COUNTS].
    + eapply gateway_reference_result_entries_bound;[exact STACK|exact FINAL_ENTRIES].
Qed.
