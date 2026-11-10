(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual data-cell store and native return retain the original metadata. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayObjectDiscipline GatewayObjectThreads
  GatewayOutcome GatewayOutcomeAllocation GatewayOutcomeConstruction GatewayOwnedOutcomeReturn GatewayOwnedOutcomeResult
  GatewayReferenceThreads GatewayLocalRuntime GatewayScopedMemory GatewayFrames GatewayContexts
  GatewayFramedRuntime GatewayCallPath GatewayOperations GatewaySourceSegments GatewayThreadRuntime GatewayStreamInterface GatewayReadonly.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Section OutcomeViewReturn.
Context {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
  (python:World->python_world)(objects:World->gateway_object_heap)
  (types:World->Values.val->option GatewayTypeRuntime.gateway_type_description)
  (allocator:World->Values.val->Prop)(instances:World->Values.val->option Values.val)
  (leases:World->nat->Values.val->Prop)(owned:World->Values.val->Prop)
  (decimal_float:list Z->Floats.float->Prop)(detached:Values.val->mem->World->Prop)
  (io:Event->option gateway_native_io)(stable:World->block->Z->Prop)(thread_errno:World->int)(heap_allocation:block->Z->Prop).
Let native:=fun world object=>gateway_native_private(python world)object.
Let discipline:=gateway_python_discipline python objects detached.
Context(runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
  (allocations:gateway_outcome_allocation_runtime backend python objects types allocator instances leases owned io native stable)
  (reference_threads:gateway_reference_thread_contract backend native stable discipline heap_allocation python objects)
  (view:World->Prop)
  (view_frame:forall before next,view before->gateway_reference_thread_effect python objects before next->view next).

Definition gateway_outcome_view_state(state:gateway_state World):Prop:=
  match state with
  |gateway_live _ world=>view world
  |gateway_dead _ _=>True end.

Lemma gateway_outcome_return_view_step object data class ledger owner ticket held
    source world event target:
  gateway_owned_outcome_return_state python objects instances owned decimal_float
    object data class ledger owner ticket held(gateway_live source world)->
  gateway_outcome_view_state(gateway_live source world)->
  gateway_step backend ge(gateway_live source world)event target->
  gateway_owned_outcome_return_state python objects instances owned decimal_float object data class ledger owner ticket held target /\
  gateway_outcome_view_state target.
Proof.
  intros BASE VIEW STEP.
  pose proof(gateway_owned_outcome_return_step backend ge python objects types allocator instances leases owned decimal_float detached io stable
    thread_errno heap_allocation runtime allocations reference_threads object data class ledger owner ticket held source world event target BASE STEP)
    as[AFTER QUIET];split;[exact AFTER|].
  destruct BASE as[LOCAL[SCOPED[READY REST]]].
  assert(INTERNAL:~gateway_at_primitive source)by(eapply gateway_local_readonly_not_primitive;exact LOCAL).
  destruct(gateway_nonprimitive_step backend ge _ _ _ _ INTERNAL STEP)
    as[[trace[following[EVENT[REAL TARGET]]]]|[[changed[current[EVENT[INTERFERENCE TARGET]]]]|[EVENT TARGET]]];subst;cbn in *.
  - exact VIEW.
  - eapply view_frame;[exact VIEW|].
    eapply gateway_reference_thread_ambient with(mode:=None);[exact reference_threads|exact READY|exact INTERFERENCE].
  - exact I.
Qed.

Lemma gateway_outcome_return_view_run object data class ledger owner ticket held
    first events last:
  gateway_owned_outcome_return_state python objects instances owned decimal_float object data class ledger owner ticket held first->
  gateway_outcome_view_state first->gateway_steps backend ge first events last->
  gateway_owned_outcome_return_state python objects instances owned decimal_float object data class ledger owner ticket held last /\
  gateway_outcome_view_state last.
Proof.
  intros BASE VIEW RUN;revert BASE VIEW;induction RUN;intros BASE VIEW;[split;assumption|].
  destruct first as[source world|memory world].
  - destruct(gateway_outcome_return_view_step object data class ledger owner ticket held
      source world observed middle BASE VIEW H)as[NEXT NEXT_VIEW];apply IHRUN;assumption.
  - inversion H.
Qed.

Theorem gateway_actual_outcome_return_keeps_view environment parameters object data class ledger owner ticket held
    before world events value after next:
  gateway_native_environment native world before environment->
  gateway_owned_outcome_return_context python objects instances owned decimal_float object data class ledger owner ticket held before world->
  view world->
  gateway_steps backend ge(gateway_live(gateway_outcome_assigned_state environment parameters object before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  value=Vptr object Ptrofs.zero /\
  gateway_owned_outcome_return_context python objects instances owned decimal_float object data class ledger owner ticket held after next /\
  view next.
Proof.
  intros ENVIRONMENT CONTEXT VIEW RUN.
  assert(AVOIDS:gateway_environment_avoids(gateway_outcome_cell_region object)environment).
  { intros identifier candidate ty position LOOK[SAME RANGE];subst candidate.
    destruct(ENVIRONMENT identifier object ty LOOK)as[LIVE NATIVE].
    destruct CONTEXT as[_[[_[RUNTIME REST]]MORE]];exact(NATIVE RUNTIME). }
  assert(INITIAL:gateway_owned_outcome_return_state python objects instances owned decimal_float object data class ledger owner ticket held
    (gateway_live(gateway_outcome_assigned_state environment parameters object before)world)).
  { split;[split;[reflexivity|split;[reflexivity|exact ENVIRONMENT]]|].
    split;[split;[reflexivity|split;[reflexivity|exact AVOIDS]]|exact CONTEXT]. }
  destruct(gateway_outcome_return_view_run object data class ledger owner ticket held _ _ _ INITIAL VIEW RUN)
    as[[_[_ FINAL]]AFTER_VIEW].
  split;[eapply gateway_outcome_final_return_identity;exact RUN|]. split;assumption.
Qed.

Theorem gateway_actual_constructed_outcome_keeps_view environment parameters object data_block data_offset class ledger owner ticket held
    before world events value after next:
  gateway_outcome_member_layout ge->parameters!_copy=Some(Vptr data_block data_offset)->
  gateway_owned_outcome_construction_context python objects instances owned decimal_float
    environment object Vnullptr class ledger owner ticket held before world->
  view world->
  gateway_steps backend ge
    (gateway_live(Returnstate(Vptr object Ptrofs.zero)(gateway_outcome_allocation_cont environment parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  value=Vptr object Ptrofs.zero /\
  gateway_owned_outcome_return_context python objects instances owned decimal_float object(Vptr data_block data_offset)class ledger owner ticket held after next /\
  view next.
Proof.
  intros LAYOUT COPY CONTEXT VIEW RUN.
  set(input:=fun memory current=>gateway_owned_outcome_construction_context python objects instances owned decimal_float
    environment object Vnullptr class ledger owner ticket held memory current /\
    view current).
  set(output:=fun memory current=>gateway_owned_outcome_construction_context python objects instances owned decimal_float
    environment object(Vptr data_block data_offset)class ledger owner ticket held memory current /\
    view current).
  assert(CLOSED:gateway_ambient_closed backend input).
  { intros memory current changed following[BASE CURRENT]INTERFERENCE;split.
    - eapply gateway_owned_outcome_construction_ambient;[exact runtime|exact allocations|exact reference_threads|exact BASE|exact INTERFERENCE].
    - eapply view_frame;[exact CURRENT|].
      eapply gateway_reference_thread_ambient with(mode:=None);[exact reference_threads|exact(proj1(proj1 BASE))|exact INTERFERENCE]. }
  assert(POINTER:forall memory current,input memory current->Mem.weak_valid_pointer memory object 0=true).
  { intros memory current[[[READY[[_[_[_[ACCESS POINTER]]]]REST]]ENV]VIEW_NOW];exact POINTER. }
  assert(STORE:forall memory current,input memory current->exists changed,
    Mem.store Mptr memory object 16(Vptr data_block data_offset)=Some changed /\output changed current).
  { intros memory current[[[READY[CELL[LOAD[CLASS[OWNER HELD]]]]]ENV]VIEW_NOW].
    destruct(gateway_outcome_data_store python objects owned memory current object(Vptr data_block data_offset)READY CELL
      ltac:(eexists;eexists;reflexivity))as(changed &WRITE &AFTER_READY &AFTER_CELL &AFTER_LOAD &FRAME).
    exists changed;split;[exact WRITE|]. split;[split|exact VIEW_NOW].
    - exact(conj AFTER_READY(conj AFTER_CELL(conj AFTER_LOAD(conj CLASS(conj OWNER HELD))))).
    - intros identifier candidate ty LOOK;destruct(ENV identifier candidate ty LOOK)as[LIVE PRIVATE];split;
        [eapply Mem.store_valid_block_1;[exact WRITE|exact LIVE]|exact PRIVATE]. }
  pose proof(gateway_outcome_assignment_segment backend ge input output environment parameters object data_block data_offset before
    LAYOUT COPY CLOSED POINTER STORE)as SEGMENT.
  destruct(gateway_source_segment_cut backend ge _ _ _ _ SEGMENT before world events value after next(conj CONTEXT VIEW)RUN)
    as(prefix &suffix &assigned &current &EVENTS &QUIET &PREFIX &[[AFTER_CONTEXT AFTER_ENV]AFTER_VIEW]&REST).
  eapply gateway_actual_outcome_return_keeps_view;[exact AFTER_ENV|exact AFTER_CONTEXT|exact AFTER_VIEW|exact REST].
Qed.
End OutcomeViewReturn.
