(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Boolean dispatch returns its actual source-owned builtin. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps CallContexts LocalAccess.
From HostGateway Require Import GatewaySource GatewayImport GatewayMachine GatewayContexts GatewayPython GatewayObjects
  GatewayObjectDiscipline GatewayObjectThreads GatewayReferences GatewayValue GatewayValueEntry GatewayValueStack
  GatewayValueTag GatewayValueRegions GatewayValueEnvironment GatewayValueBoolean GatewayValueBooleanCut GatewayValueReturns
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceHeld GatewayReferenceThreads
  GatewayReferenceScalarRuns GatewayReferenceFrames GatewayReferenceExecution GatewayReferenceContextScope
  GatewayThreadInvariant GatewayReturnRuntime GatewayThreadRuntime GatewayStreamInterface GatewayFramedRuntime
  GatewayObjectRuns GatewayObjectEvents GatewayPathEvents.
Import ListNotations.
Local Close Scope lean_scope.

Lemma gateway_reference_mint_keeps_vacant ledger owner pointer other final:
  gateway_reference_take other(gateway_reference_entries ledger)=None->other<>owner->
  gateway_reference_apply(gateway_reference_mint owner pointer)(gateway_reference_valid ledger)=
    gateway_reference_valid final->gateway_reference_take other(gateway_reference_entries final)=None.
Proof.
  intros VACANT DIFFERENT;unfold gateway_reference_apply.
  destruct(gateway_reference_take owner(gateway_reference_entries ledger))as[[old remaining]|]eqn:FREE;
    [discriminate|].
  intro SAME;injection SAME as SAME;subst final.
  change(gateway_reference_take other
    ({|gateway_reference_ticket:=gateway_reference_next ledger;gateway_reference_owner:=owner;
       gateway_reference_pointer:=pointer|}::gateway_reference_entries ledger)=None).
  apply gateway_reference_take_none;intros entry[HEAD|MEMBER]OWNER.
  - subst entry;cbn in OWNER;congruence.
  - exact(proj1(gateway_reference_take_none _ _)VACANT entry MEMBER OWNER).
Qed.

Section Boolean.
Context {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
  (python:World->python_world)(objects:World->gateway_object_heap)
  (detached:Values.val->Memory.mem->World->Prop)(io:Event->option gateway_native_io)
  (stable:World->block->Z->Prop)(thread_errno:World->int)(heap_allocation:block->Z->Prop)
  (decimal_float:list Z->Floats.float->Prop).
Let native:=fun world object=>gateway_native_private(python world)object.
Let base:=gateway_python_discipline python objects detached.
Context(runtime:gateway_thread_runtime backend io native stable base thread_errno)
  (constructors:gateway_objects_runtime backend python objects decimal_float)
  (reference_threads:gateway_reference_thread_contract backend native stable base heap_allocation python objects)
  (projection:gateway_direct_io_projection backend io).

Theorem gateway_reference_actual_boolean_branch context ledger held flag slots arguments initial stream_block stream_offset
    final_stream readonly original before world events value after next symbol definition descriptor:
  is_call_cont context->gateway_reference_ledger_well_formed ledger->
  gateway_reference_take(gateway_reference_result(S(gateway_reference_depth context)))
    (gateway_reference_entries ledger)=None->
  gateway_reference_take(gateway_reference_temporary(gateway_reference_depth context)_t'3)
    (gateway_reference_entries ledger)=None->
  gateway_reference_take(gateway_reference_result(gateway_reference_depth context))
    (gateway_reference_entries ledger)=None->
  gateway_object_api_definition gateway_api_bool=Some definition->
  Genv.find_symbol ge _PyBool_FromLong=Some symbol->Genv.find_funct_ptr ge symbol=Some definition->
  type_of_fundef definition=Tfunction[tlong](tptr(Tstruct __object noattr))cc_default->
  gateway_value_tagged native stable
    (gateway_thread_invariant_discipline base(gateway_reference_scope python objects decimal_float ledger held))
    slots stream_block stream_offset final_stream readonly original(gateway_value_boolean_tag flag)before world->
  gateway_steps backend ge
    (gateway_live(Returnstate(Vint Int.zero)(gateway_value_tag_cont slots arguments initial)before)world)
    events(gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  exists final prefix constructing suffix called called_world constructed returned returned_world,
    events=prefix++constructing++suffix /\
    gateway_steps backend ge
      (gateway_live(Callstate definition[gateway_value_boolean_argument flag]Kstop called)called_world)constructing
      (gateway_live(Returnstate constructed Kstop returned)returned_world) /\
    value=constructed /\gateway_reference_ledger_well_formed final /\
    gateway_reference_owns final(gateway_reference_result(gateway_reference_depth context))
      (gateway_reference_next ledger)value /\
    gateway_reference_place_value ge(Returnstate value context after)
      (gateway_reference_result(gateway_reference_depth context))value /\
    gateway_reference_scope python objects decimal_float final
      (held++[{|gateway_held_ticket:=gateway_reference_next ledger;gateway_held_object:=value;
        gateway_held_view:=gateway_held_scalar_value(gateway_bool_object flag)|}])next /\
    gateway_value_heap decimal_float(objects next)value
      (LeanCage_Host_GatewayResponseCode_Value_boolean(if flag then Bool_true else Bool_false)) /\
    base None after next /\gateway_received_bytes io descriptor events=[] /\
    exists api_ledger,
      gateway_reference_apply(gateway_reference_mint(gateway_reference_result(S(gateway_reference_depth context)))constructed)
        (gateway_reference_valid ledger)=gateway_reference_valid api_ledger /\
      gateway_reference_execution backend ge gateway_reference_frame_select
        (gateway_plug(gateway_live(Returnstate constructed(gateway_value_boolean_cont flag slots arguments initial)returned)
          returned_world)context)(gateway_reference_valid api_ledger)suffix
        (gateway_live(Returnstate value context after)next)(gateway_reference_valid final).
Proof.
  intros CALL FORMED API_FREE TEMP_FREE RESULT_FREE DEFINITION SYMBOL FUNCTION TYPE INPUT RUN NONNULL.
  set(augmented:=gateway_thread_invariant_discipline base(gateway_reference_scope python objects decimal_float ledger held)).
  pose proof(gateway_thread_with_reference_scope backend io native stable base thread_errno heap_allocation
    python objects decimal_float reference_threads ledger held runtime)as SCOPED_RUNTIME.
  set(property:=gateway_value_tagged native stable augmented slots stream_block stream_offset final_stream readonly original
    (gateway_value_boolean_tag flag)).
  pose proof(gateway_value_tagged_ambient backend io native stable augmented thread_errno SCOPED_RUNTIME
    slots stream_block stream_offset final_stream readonly original(gateway_value_boolean_tag flag))as CLOSED.
  destruct(gateway_actual_boolean_call backend ge property flag slots arguments initial before world events value after next
    symbol definition CLOSED ltac:(intros;exact(proj2 H))SYMBOL FUNCTION TYPE INPUT RUN)
    as(prefix &constructing &suffix &called &called_world &constructed &returned &returned_world &
      EVENTS &QUIET &PREFIX &CALLED &API_RUN &SUFFIX).
  assert(RESULT_NONNULL:constructed<>Vnullptr).
  { intro NULL;subst constructed;apply NONNULL.
    exact(gateway_value_boolean_returned backend ge flag slots arguments initial returned returned_world suffix
      Vnullptr value after next(or_introl eq_refl)SUFFIX). }
  pose proof(gateway_value_active_environment native stable augmented slots stream_block stream_offset final_stream readonly original
    called called_world(proj1 CALLED))as[[SIDE SCOPE]ENVIRONMENT].
  destruct(gateway_reference_actual_scalar_run backend ge python objects detached io stable thread_errno heap_allocation decimal_float
    runtime constructors reference_threads ledger(gateway_reference_result(S(gateway_reference_depth context)))held
    gateway_api_bool definition[gateway_value_boolean_argument flag](gateway_bool_object flag)gateway_bool_kind
    (gateway_value_environment slots)property called called_world constructing constructed returned returned_world
    FORMED API_FREE SCOPE DEFINITION CLOSED ltac:(intros;split;[constructor|exact I])eq_refl eq_refl
    ltac:(right;left;reflexivity)CALLED(conj SIDE ENVIRONMENT)API_RUN RESULT_NONNULL)
    as(api_ledger &operation_prefix &operation_suffix &api_before &api_world &api_after &api_next &observed &
      API_EVENTS &OPERATION &MINT &API_WELL &API_OWNED &API_SCOPE &API_ENVIRONMENT &RETAINED).
  assert(TEMP_VACANT:gateway_reference_take(gateway_reference_temporary(gateway_reference_depth context)_t'3)
    (gateway_reference_entries api_ledger)=None).
  { eapply(gateway_reference_mint_keeps_vacant ledger(gateway_reference_result(S(gateway_reference_depth context)))constructed
      (gateway_reference_temporary(gateway_reference_depth context)_t'3)api_ledger);
      [exact TEMP_FREE|discriminate|exact MINT]. }
  assert(RESULT_VACANT:gateway_reference_take(gateway_reference_result(gateway_reference_depth context))
    (gateway_reference_entries api_ledger)=None).
  { eapply(gateway_reference_mint_keeps_vacant ledger(gateway_reference_result(S(gateway_reference_depth context)))constructed
      (gateway_reference_result(gateway_reference_depth context))api_ledger);
      [exact RESULT_FREE|intro SAME;injection SAME;lia|exact MINT]. }
  destruct(gateway_reference_context_caller_scope backend ge context python objects decimal_float io native stable base thread_errno
    heap_allocation runtime reference_threads f_host_value _t'3(gateway_value_environment slots)
    (gateway_value_boolean_parameters flag arguments initial)(Etempvar _t'3(tptr(Tstruct __object noattr)))
    (Kseq gateway_value_after_boolean Kstop)constructed returned returned_world suffix value after next api_ledger
    (gateway_reference_next ledger)
    (held++[{|gateway_held_ticket:=gateway_reference_next ledger;gateway_held_object:=constructed;
      gateway_held_view:=gateway_held_scalar_value(gateway_bool_object flag)|}])
    CALL eq_refl eq_refl ltac:(intro;apply old_expression_value,value_temp,PTree.gss)
    ltac:(intros memory converted CONVERSION;
      exact(GatewayReturnIdentity.gateway_pointer_cast_identity memory
        (tptr(Tstruct __object noattr))(tptr(Tstruct __object noattr))constructed converted
        (ex_intro _ (Tstruct __object noattr)eq_refl)(ex_intro _ (Tstruct __object noattr)eq_refl)CONVERSION))
    API_WELL API_OWNED TEMP_VACANT RESULT_VACANT API_SCOPE API_ENVIRONMENT SUFFIX)
    as[final[SAME[ANNOTATED[WELL[OWNED[BINDING[FINAL_SCOPE[FINAL_SIDE TAIL_QUIET]]]]]]]].
  subst value.
  assert(VALUE:gateway_object_values(objects next)constructed=Some(gateway_bool_object flag)).
  { pose proof(proj2 FINAL_SCOPE)as HELD;apply Forall_app in HELD;destruct HELD as[OLD NEW].
    destruct(Forall_inv NEW)as[OWNER[PRIVATE[SAFE[LOOKUP CHILDREN]]]];exact LOOKUP. }
  exists final,prefix,constructing,suffix,called,called_world,constructed,returned,returned_world.
  split;[exact EVENTS|]. split;[exact API_RUN|]. split;[reflexivity|]. split;[exact WELL|].
  split;[exact OWNED|]. split;[exact BINDING|]. split;[exact FINAL_SCOPE|].
  split;[apply gateway_heap_boolean;exact VALUE|]. split;[exact FINAL_SIDE|]. split.
  - rewrite EVENTS,!gateway_received_append,(gateway_quiet_received io descriptor prefix QUIET),
      (gateway_object_run_no_direct_receive backend ge io gateway_api_bool definition[gateway_value_boolean_argument flag]
        called called_world constructing constructed returned returned_world descriptor projection DEFINITION API_RUN),
      (gateway_quiet_received io descriptor suffix TAIL_QUIET);reflexivity.
  - exists api_ledger;split;[exact MINT|exact ANNOTATED].
Qed.

End Boolean.
