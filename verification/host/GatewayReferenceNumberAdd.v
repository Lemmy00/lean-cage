(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual sum and both operand releases produce the next
   integer iteration with its new source reference and the original retained inputs. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline GatewayObjectThreads
  GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceHeld GatewayReferenceThreads GatewayReferenceNormalForm GatewayReferenceNumericLedger GatewayReferenceNumericFrames
  GatewayReferenceNumericContext GatewayReferenceNumericRequests GatewayReferenceNumericRelease GatewayReferenceNumberArithmetic GatewayReferenceContainerScope
  GatewayReferenceEmptyContainer GatewayReferenceFloatTail GatewayNumberIntegerCalls GatewayNumberIntegerLoopSource GatewayNumberIntegerStructure GatewayNumberArithmeticSuccess
  GatewayContexts GatewaySourcePaths GatewaySourceSegments GatewayFramedRuntime GatewayPathEvents GatewayObjectRuns GatewayObjectEvents
  GatewayScalarConstructorCalls GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Theorem gateway_reference_actual_number_add {World Event}(backend:gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (constructors:gateway_objects_runtime backend python objects decimal_float)
    (references:gateway_reference_runtime backend python objects)
    (reference_threads:gateway_reference_thread_contract backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (projection:gateway_direct_io_projection backend io)
    ledger current_owner part_owner part_ticket part part_offset chunk scaled_owner scaled_ticket scaled scaled_offset multiple
    held parameters definition index width scalar slots stream_block stream_offset initial readonly original size object bytes before world events value after next:
  gateway_reference_ledger_well_formed ledger->gateway_reference_take current_owner(gateway_reference_entries ledger)=None->
  gateway_reference_owns ledger part_owner part_ticket(Vptr part part_offset)->
  gateway_reference_owns ledger scaled_owner scaled_ticket(Vptr scaled scaled_offset)->part_ticket<>scaled_ticket->
  (forall captured,In captured held->gateway_held_ticket captured<>part_ticket /\gateway_held_ticket captured<>scaled_ticket)->
  gateway_reference_scope python objects decimal_float ledger
    (held++[gateway_reference_scalar_capture part_ticket(Vptr part part_offset)(gateway_long_object chunk);
      gateway_reference_scalar_capture scaled_ticket(Vptr scaled scaled_offset)(gateway_long_object multiple)])world->
  gateway_object_api_definition gateway_api_number_add=Some definition->
  parameters!_scaled=Some(Vptr scaled scaled_offset)->parameters!_part=Some(Vptr part part_offset)->
  parameters!_index=Some(Vlong(Int64.repr index))->parameters!_width=Some(Vlong(Int64.repr width))->
  gateway_scalar_private_ready python objects detached stable heap_allocation scalar slots stream_block stream_offset initial readonly original
    size object bytes before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate definition[Vptr scaled scaled_offset;Vptr part part_offset](number_integer_add_cont parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  exists final result result_offset loop_parameters prefix suffix loop_memory loop_world,
    gateway_reference_ledger_well_formed final /\gateway_reference_next final=S(gateway_reference_next ledger) /\
    gateway_reference_owns final current_owner(gateway_reference_next ledger)(Vptr result result_offset) /\
    gateway_reference_take part_owner(gateway_reference_entries final)=None /\gateway_reference_take scaled_owner(gateway_reference_entries final)=None /\
    (forall owner ticket pointer,ticket<>part_ticket->ticket<>scaled_ticket->gateway_reference_owns ledger owner ticket pointer->
      gateway_reference_owns final owner ticket pointer) /\
    gateway_reference_numeric_context python objects decimal_float detached stable heap_allocation final
      (held++[gateway_reference_scalar_capture(gateway_reference_next ledger)(Vptr result result_offset)(gateway_long_object(multiple+chunk))])
      scalar slots stream_block stream_offset initial readonly original size object bytes loop_memory loop_world /\
    loop_parameters!_value__1=Some(Vptr result result_offset) /\loop_parameters!_index=Some(Vlong(Int64.repr(index+width))) /\
    loop_parameters!_width=Some(Vlong(Int64.repr 9)) /\
    (forall identifier,identifier<>_value__1->identifier<>_t'20->identifier<>_index->identifier<>_width->
      loop_parameters!identifier=parameters!identifier) /\
    events=prefix++suffix /\gateway_received_bytes io(stream_descriptor initial)prefix=[] /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate definition[Vptr scaled scaled_offset;Vptr part part_offset](number_integer_add_cont parameters)before)world)prefix
      (gateway_live(State f_host_json_number number_integer_loop number_integer_loop_cont empty_env loop_parameters loop_memory)loop_world) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_json_number number_integer_loop number_integer_loop_cont empty_env loop_parameters loop_memory)loop_world)suffix
      (gateway_live(Returnstate value Kstop after)next) /\
    exists constructed after_scaled,
      gateway_reference_apply(gateway_reference_mint current_owner(Vptr result result_offset))(gateway_reference_valid ledger)=gateway_reference_valid constructed /\
      gateway_reference_apply(gateway_reference_release scaled_owner(Vptr scaled scaled_offset))(gateway_reference_valid constructed)=gateway_reference_valid after_scaled /\
      gateway_reference_apply(gateway_reference_release part_owner(Vptr part part_offset))(gateway_reference_valid after_scaled)=gateway_reference_valid final.
Proof.
  intros FORMED CURRENT_FREE PART_OWNED SCALED_OWNED DISTINCT DIFFERENT SCOPE DEFINITION SCALED_PARAMETER PART_PARAMETER INDEX WIDTH INPUT RUN NONNULL.
  set(part_capture:=gateway_reference_scalar_capture part_ticket(Vptr part part_offset)(gateway_long_object chunk)).
  set(scaled_capture:=gateway_reference_scalar_capture scaled_ticket(Vptr scaled scaled_offset)(gateway_long_object multiple)).
  set(operands:=held++[part_capture;scaled_capture]).
  destruct gateway_actual_number_float_bindings as[_[release_definition[RELEASE_DEFINITION[RELEASE_BINDING RELEASE_TYPE]]]].
  destruct RELEASE_BINDING as[release_symbol[RELEASE_SYMBOL RELEASE_FUNCTION]].
  destruct(gateway_return_cut backend(Clight.globalenv prog)definition[Vptr scaled scaled_offset;Vptr part part_offset](number_integer_add_cont parameters)
    before world events(Returnstate value Kstop after)next ltac:(cbn;exact I)ltac:(cbn;lia)RUN)
    as(adding &from_add &summed &add_after &add_next &EVENTS &ADD_RUN &ADD_REST).
  assert(SUM_NONNULL:summed<>Vnullptr).
  { eapply gateway_number_sum_success_nonnull;[exact SCALED_PARAMETER|right;repeat eexists;reflexivity|
      exact PART_PARAMETER|right;repeat eexists;reflexivity|exact RELEASE_SYMBOL|exact RELEASE_FUNCTION|exact RELEASE_TYPE|exact ADD_REST|exact NONNULL]. }
  destruct(gateway_reference_actual_binary_storage backend(Clight.globalenv prog)python objects decimal_float detached io stable thread_errno heap_allocation
    runtime constructors reference_threads false ledger current_owner operands definition scaled_ticket(Vptr scaled scaled_offset)multiple
    part_ticket(Vptr part part_offset)chunk scalar slots stream_block stream_offset initial readonly original size object bytes before world adding summed add_after add_next
    FORMED CURRENT_FREE SCOPE ltac:(unfold operands;apply in_or_app;right;right;left;reflexivity)
    ltac:(unfold operands;apply in_or_app;right;left;reflexivity)DEFINITION INPUT ADD_RUN SUM_NONNULL)
    as(constructed &MINT &WELL &RESULT_OWNED &ADD_STORAGE &ADD_SCOPE).
  set(result_capture:=gateway_reference_scalar_capture(gateway_reference_next ledger)summed(gateway_long_object(multiple+chunk))).
  set(release_property:=gateway_reference_numeric_context python objects decimal_float detached stable heap_allocation constructed(operands++[result_capture])
    scalar slots stream_block stream_offset initial readonly original size object bytes).
  pose proof(gateway_reference_numeric_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation runtime reference_threads
    constructed(operands++[result_capture])scalar slots stream_block stream_offset initial readonly original size object bytes)as RELEASE_CLOSED.
  destruct(gateway_number_scaled_release_path backend(Clight.globalenv prog)release_property parameters(Vptr scaled scaled_offset)summed add_after release_symbol release_definition
    RELEASE_CLOSED SCALED_PARAMETER ltac:(right;repeat eexists;reflexivity)RELEASE_SYMBOL RELEASE_FUNCTION RELEASE_TYPE)
    as(release_parameters &SCALED_PATH &SUM_PARAMETER &RELEASE_PARAMETERS).
  destruct(gateway_source_path_cut backend(Clight.globalenv prog)_ _ _ _ _ _ SCALED_PATH add_after add_next from_add value after next
    (conj ADD_STORAGE ADD_SCOPE)ADD_REST)
    as(scaled_prefix &from_scaled &scaled_before &scaled_world &SCALED_EVENTS &SCALED_QUIET &TO_SCALED &SCALED_READY &FROM_SCALED).
  destruct(gateway_return_cut backend(Clight.globalenv prog)release_definition[Vptr scaled scaled_offset](number_integer_release_scaled_cont release_parameters)
    scaled_before scaled_world from_scaled(Returnstate value Kstop after)next ltac:(cbn;exact I)ltac:(cbn;lia)FROM_SCALED)
    as(releasing_scaled &from_part &scaled_ignored &scaled_after &scaled_next &SCALED_RUN_EVENTS &SCALED_RUN &SCALED_REST).
  assert(SCALED_BOUND:(scaled_ticket<gateway_reference_next ledger)%nat)
    by(exact(proj1(Forall_forall _ _)(proj2(proj2 FORMED))_ SCALED_OWNED)).
  assert(PART_BOUND:(part_ticket<gateway_reference_next ledger)%nat)
    by(exact(proj1(Forall_forall _ _)(proj2(proj2 FORMED))_ PART_OWNED)).
  assert(SCALED_STILL:gateway_reference_owns constructed scaled_owner scaled_ticket(Vptr scaled scaled_offset)).
  { eapply gateway_reference_numeric_minted_keeps;[exact MINT|exact SCALED_OWNED]. }
  assert(SCALED_SCOPE:gateway_reference_scope python objects decimal_float constructed
    ((held++[part_capture;result_capture])++[scaled_capture])scaled_world).
  { eapply gateway_reference_scope_sublist;[exact(proj2 SCALED_READY)|].
    intros captured MEMBER;unfold operands in *;repeat rewrite in_app_iff in *;cbn in *;tauto. }
  destruct(gateway_reference_actual_numeric_release backend(Clight.globalenv prog)python objects detached io stable thread_errno heap_allocation decimal_float
    runtime references reference_threads constructed scaled_owner scaled_ticket(Vptr scaled scaled_offset)(gateway_long_object multiple)
    (held++[part_capture;result_capture])release_definition scalar slots stream_block stream_offset initial readonly original size object bytes
    scaled_before scaled_world releasing_scaled scaled_ignored scaled_after scaled_next WELL SCALED_STILL
    ltac:(intros captured MEMBER;apply in_app_or in MEMBER;destruct MEMBER as[OLD|[SAME|[SAME|BAD]]];
      [exact(proj2(DIFFERENT captured OLD))|subst captured;exact DISTINCT|subst captured;cbn;lia|contradiction])
    SCALED_SCOPE RELEASE_DEFINITION(proj1 SCALED_READY)SCALED_RUN)
    as(after_scaled &SCALED_RELEASE &SCALED_WELL &AFTER_SCALED_SCOPE &AFTER_SCALED_STORAGE &SCALED_OCCURRENCE).
  assert(PART_STILL:gateway_reference_owns after_scaled part_owner part_ticket(Vptr part part_offset)).
  { eapply gateway_reference_numeric_released_keeps;[exact WELL|exact SCALED_STILL|exact DISTINCT|exact SCALED_RELEASE|].
    eapply gateway_reference_numeric_minted_keeps;[exact MINT|exact PART_OWNED]. }
  set(part_property:=gateway_reference_numeric_context python objects decimal_float detached stable heap_allocation after_scaled
    (held++[part_capture;result_capture])scalar slots stream_block stream_offset initial readonly original size object bytes).
  pose proof(gateway_reference_numeric_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation runtime reference_threads
    after_scaled(held++[part_capture;result_capture])scalar slots stream_block stream_offset initial readonly original size object bytes)as PART_CLOSED.
  pose proof(gateway_number_part_release_path backend(Clight.globalenv prog)part_property release_parameters(Vptr part part_offset)scaled_ignored scaled_after
    release_symbol release_definition PART_CLOSED ltac:(rewrite RELEASE_PARAMETERS by discriminate;exact PART_PARAMETER)
    ltac:(right;repeat eexists;reflexivity)RELEASE_SYMBOL RELEASE_FUNCTION RELEASE_TYPE)as PART_PATH.
  destruct(gateway_source_path_cut backend(Clight.globalenv prog)_ _ _ _ _ _ PART_PATH scaled_after scaled_next from_part value after next
    (conj AFTER_SCALED_STORAGE AFTER_SCALED_SCOPE)SCALED_REST)
    as(part_prefix &from_release_part &part_before &part_world &PART_EVENTS &PART_QUIET &TO_PART &PART_READY &FROM_PART).
  destruct(gateway_return_cut backend(Clight.globalenv prog)release_definition[Vptr part part_offset](number_integer_release_part_cont release_parameters)
    part_before part_world from_release_part(Returnstate value Kstop after)next ltac:(cbn;exact I)ltac:(cbn;lia)FROM_PART)
    as(releasing_part &from_advance &part_ignored &part_after &part_next &PART_RUN_EVENTS &PART_RUN &PART_REST).
  assert(PART_SCOPE:gateway_reference_scope python objects decimal_float after_scaled
    ((held++[result_capture])++[part_capture])part_world).
  { eapply gateway_reference_scope_sublist;[exact(proj2 PART_READY)|].
    intros captured MEMBER;repeat rewrite in_app_iff in *;cbn in *;tauto. }
  destruct(gateway_reference_actual_numeric_release backend(Clight.globalenv prog)python objects detached io stable thread_errno heap_allocation decimal_float
    runtime references reference_threads after_scaled part_owner part_ticket(Vptr part part_offset)(gateway_long_object chunk)
    (held++[result_capture])release_definition scalar slots stream_block stream_offset initial readonly original size object bytes
    part_before part_world releasing_part part_ignored part_after part_next SCALED_WELL PART_STILL
    ltac:(intros captured MEMBER;apply in_app_or in MEMBER;destruct MEMBER as[OLD|[SAME|BAD]];
      [exact(proj1(DIFFERENT captured OLD))|subst captured;cbn;lia|contradiction])PART_SCOPE RELEASE_DEFINITION(proj1 PART_READY)PART_RUN)
    as(final &PART_RELEASE &FINAL_WELL &FINAL_SCOPE &FINAL_STORAGE &PART_OCCURRENCE).
  assert(RESULT_AFTER_SCALED:gateway_reference_owns after_scaled current_owner(gateway_reference_next ledger)summed).
  { eapply gateway_reference_numeric_released_keeps;[exact WELL|exact SCALED_STILL|lia|exact SCALED_RELEASE|exact RESULT_OWNED]. }
  assert(FINAL_RESULT:gateway_reference_owns final current_owner(gateway_reference_next ledger)summed).
  { eapply gateway_reference_numeric_released_keeps;[exact SCALED_WELL|exact PART_STILL|lia|exact PART_RELEASE|exact RESULT_AFTER_SCALED]. }
  destruct(gateway_reference_owned_pointer python objects final current_owner(gateway_reference_next ledger)summed part_after part_next
    ltac:(eapply gateway_scalar_private_side;exact FINAL_STORAGE)(proj1 FINAL_SCOPE)FINAL_RESULT)
    as(result &result_offset &RESULT_POINTER &RESULT_VALID);subst summed.
  set(final_property:=gateway_reference_numeric_context python objects decimal_float detached stable heap_allocation final(held++[result_capture])
    scalar slots stream_block stream_offset initial readonly original size object bytes).
  pose proof(gateway_reference_numeric_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation runtime reference_threads
    final(held++[result_capture])scalar slots stream_block stream_offset initial readonly original size object bytes)as FINAL_CLOSED.
  assert(VALID:forall memory current_world,final_property memory current_world->Mem.weak_valid_pointer memory result(Ptrofs.unsigned result_offset)=true).
  { intros memory current_world[READY HOLD].
    destruct(gateway_reference_owned_pointer python objects final current_owner(gateway_reference_next ledger)(Vptr result result_offset)memory current_world
      ltac:(eapply gateway_scalar_private_side;exact READY)(proj1 HOLD)FINAL_RESULT)as(candidate &offset &SAME &OBSERVED);inversion SAME;subst;exact OBSERVED. }
  pose proof(gateway_number_integer_advance_segment backend(Clight.globalenv prog)final_property release_parameters result result_offset index width part_ignored part_after
    FINAL_CLOSED VALID SUM_PARAMETER ltac:(rewrite RELEASE_PARAMETERS by discriminate;exact INDEX)
    ltac:(rewrite RELEASE_PARAMETERS by discriminate;exact WIDTH))as ADVANCE.
  destruct(gateway_source_segment_cut backend(Clight.globalenv prog)_ _ _ _ ADVANCE part_after part_next from_advance value after next
    (conj FINAL_STORAGE FINAL_SCOPE)PART_REST)
    as(advance_prefix &suffix &loop_memory &loop_world &ADVANCE_EVENTS &ADVANCE_QUIET &TO_LOOP &LOOP_READY &LOOP_REST).
  set(loop_parameters:=PTree.set _width(Vlong(Int64.repr 9))(PTree.set _index(Vlong(Int64.repr(index+width)))release_parameters)).
  pose proof(gateway_plug_steps backend(Clight.globalenv prog)_ _ _(number_integer_add_cont parameters)ltac:(cbn;exact I)ADD_RUN)as ADD_CALLER.
  pose proof(gateway_plug_steps backend(Clight.globalenv prog)_ _ _(number_integer_release_scaled_cont release_parameters)ltac:(cbn;exact I)SCALED_RUN)as SCALED_CALLER.
  pose proof(gateway_plug_steps backend(Clight.globalenv prog)_ _ _(number_integer_release_part_cont release_parameters)ltac:(cbn;exact I)PART_RUN)as PART_CALLER.
  exists final,result,result_offset,loop_parameters,
    (adding++scaled_prefix++releasing_scaled++part_prefix++releasing_part++advance_prefix),suffix,loop_memory,loop_world.
  split;[exact FINAL_WELL|]. split.
  - rewrite(gateway_reference_numeric_release_next _ _ _ _ PART_RELEASE),
      (gateway_reference_numeric_release_next _ _ _ _ SCALED_RELEASE).
    exact(proj2(gateway_reference_mint_entries _ _ _ _ MINT)).
  - split;[exact FINAL_RESULT|]. split.
    + eapply gateway_reference_numeric_released_vacant;[exact SCALED_WELL|exact PART_RELEASE].
    + split.
      * eapply gateway_reference_numeric_release_keeps_vacant;[|exact PART_RELEASE].
        eapply gateway_reference_numeric_released_vacant;[exact WELL|exact SCALED_RELEASE].
      * split.
        -- intros owner ticket pointer NOT_PART NOT_SCALED OWNED.
           eapply gateway_reference_numeric_released_keeps;[exact SCALED_WELL|exact PART_STILL|exact NOT_PART|exact PART_RELEASE|].
           eapply gateway_reference_numeric_released_keeps;[exact WELL|exact SCALED_STILL|exact NOT_SCALED|exact SCALED_RELEASE|].
           eapply gateway_reference_numeric_minted_keeps;[exact MINT|exact OWNED].
        -- split;[exact LOOP_READY|]. split.
           ++ unfold loop_parameters;repeat rewrite PTree.gso by discriminate;exact SUM_PARAMETER.
           ++ split;[unfold loop_parameters;rewrite PTree.gso by discriminate;apply PTree.gss|].
              split;[unfold loop_parameters;apply PTree.gss|]. split.
              ** intros identifier A B C D;unfold loop_parameters;repeat rewrite PTree.gso by congruence;
                   rewrite RELEASE_PARAMETERS by assumption;reflexivity.
              ** split;[rewrite EVENTS,SCALED_EVENTS,SCALED_RUN_EVENTS,PART_EVENTS,PART_RUN_EVENTS,ADVANCE_EVENTS;repeat rewrite app_assoc;reflexivity|]. split.
                 --- rewrite!gateway_received_append,
                       (gateway_quiet_received io(stream_descriptor initial)scaled_prefix SCALED_QUIET),
                       (gateway_quiet_received io(stream_descriptor initial)part_prefix PART_QUIET),
                       (gateway_quiet_received io(stream_descriptor initial)advance_prefix ADVANCE_QUIET).
                     rewrite(gateway_object_run_no_direct_receive backend(Clight.globalenv prog)io gateway_api_number_add definition
                       [Vptr scaled scaled_offset;Vptr part part_offset]before world adding(Vptr result result_offset)add_after add_next
                       (stream_descriptor initial)projection DEFINITION ADD_RUN).
                     rewrite(gateway_object_run_no_direct_receive backend(Clight.globalenv prog)io gateway_api_decref release_definition[Vptr scaled scaled_offset]
                       scaled_before scaled_world releasing_scaled scaled_ignored scaled_after scaled_next(stream_descriptor initial)projection RELEASE_DEFINITION SCALED_RUN).
                     rewrite(gateway_object_run_no_direct_receive backend(Clight.globalenv prog)io gateway_api_decref release_definition[Vptr part part_offset]
                       part_before part_world releasing_part part_ignored part_after part_next(stream_descriptor initial)projection RELEASE_DEFINITION PART_RUN);reflexivity.
                 --- split.
                     +++ repeat eapply gateway_steps_append;
                           [exact ADD_CALLER|exact TO_SCALED|exact SCALED_CALLER|exact TO_PART|exact PART_CALLER|exact TO_LOOP].
                     +++ split;[exact LOOP_REST|]. exists constructed,after_scaled;repeat split;assumption.
Qed.
