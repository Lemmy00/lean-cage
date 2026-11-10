(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The same actual allocation continuation stores its exact copy pointer and
   retains the repaired source-reference ledger through the final return. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayObjectDiscipline
  GatewayObjectThreads GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceThreads GatewayOutcomeAllocation GatewayOutcomeConstruction GatewayOwnedOutcomeReturn
  GatewayFramedRuntime GatewaySourceSegments GatewayLocalRuntime GatewayThreadRuntime GatewayStreamInterface
  GatewayContexts GatewayPathEvents GatewayReadonly.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Section OwnedOutcomeResult.
Context {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
  (python:World->python_world)(objects:World->gateway_object_heap)
  (types:World->Values.val->option GatewayTypeRuntime.gateway_type_description)
  (default_allocator:World->Values.val->Prop)(instances:World->Values.val->option Values.val)
  (leases:World->nat->Values.val->Prop)(owned:World->Values.val->Prop)
  (decimal_float:list Z->Floats.float->Prop)(detached:Values.val->Memory.mem->World->Prop)
  (io:Event->option gateway_native_io)(stable:World->block->Z->Prop)(thread_errno:World->int)
  (heap_allocation:block->Z->Prop).
Let native:=fun world object=>gateway_native_private(python world)object.
Let discipline:=gateway_python_discipline python objects detached.
Context(runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
  (allocations:gateway_outcome_allocation_runtime backend python objects types default_allocator instances leases owned io native stable)
  (reference_threads:gateway_reference_thread_contract backend native stable discipline heap_allocation python objects).

Let returned_context:=@gateway_owned_outcome_return_context World python objects instances owned decimal_float.

Definition gateway_owned_outcome_construction_context environment object data class ledger owner ticket held memory world:Prop:=
  returned_context object data class ledger owner ticket held memory world /\gateway_native_environment native world memory environment.

Lemma gateway_owned_outcome_construction_ambient environment object data class ledger owner ticket held :
  gateway_ambient_closed backend(gateway_owned_outcome_construction_context environment object data class ledger owner ticket held).
Proof.
  intros before world after next[CONTEXT ENVIRONMENT]INTERFERENCE;split.
  - eapply gateway_owned_outcome_return_context_ambient;[exact runtime|exact allocations|exact reference_threads|exact CONTEXT|exact INTERFERENCE].
  - destruct(gateway_thread_ambient _ _ _ _ _ _ runtime None before world after next(proj1 CONTEXT)INTERFERENCE)
      as[NORMAL[[NATIVE STABLE]FRAME]].
    intros identifier candidate ty LOOK;destruct(ENVIRONMENT identifier candidate ty LOOK)as[LIVE PRIVATE];split;
      [eapply Mem.valid_block_unchanged_on;[exact FRAME|exact LIVE]|apply NATIVE;assumption].
Qed.

Theorem gateway_actual_owned_constructed_outcome environment parameters object data_block data_offset class ledger owner ticket held
    before world events value after next:
  GatewayOutcome.gateway_outcome_member_layout ge ->parameters!_copy=Some(Vptr data_block data_offset) ->
  gateway_owned_outcome_construction_context environment object Vnullptr class ledger owner ticket held before world ->
  gateway_steps backend ge
    (gateway_live(Returnstate(Vptr object Ptrofs.zero)(gateway_outcome_allocation_cont environment parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->
  value=Vptr object Ptrofs.zero /\
    returned_context object(Vptr data_block data_offset)class ledger owner ticket held after next /\Forall gateway_quiet_event events.
Proof.
  intros LAYOUT COPY CONTEXT RUN.
  set(input:=gateway_owned_outcome_construction_context environment object Vnullptr class ledger owner ticket held).
  set(output:=gateway_owned_outcome_construction_context environment object(Vptr data_block data_offset)class ledger owner ticket held).
  assert(CLOSED:gateway_ambient_closed backend input)by(apply gateway_owned_outcome_construction_ambient).
  assert(POINTER:forall memory current,input memory current->Mem.weak_valid_pointer memory object 0=true).
  { intros memory current[[NORMAL[[_[_[_[ACCESS POINTER]]]]REST]]ENV];exact POINTER. }
  assert(STORE:forall memory current,input memory current->exists changed,
    Mem.store Mptr memory object 16(Vptr data_block data_offset)=Some changed /\output changed current).
  { intros memory current[[NORMAL[CELL[LOAD[CLASS[LEASE HELD]]]]]ENV].
    destruct(gateway_outcome_data_store python objects owned memory current object(Vptr data_block data_offset)
      NORMAL CELL ltac:(eexists; eexists; reflexivity))as(changed &WRITE &AFTER_NORMAL &AFTER_CELL &AFTER_LOAD &FRAME).
    exists changed;split;[exact WRITE|]. split.
    - exact(conj AFTER_NORMAL(conj AFTER_CELL(conj AFTER_LOAD(conj CLASS(conj LEASE HELD))))).
    - intros identifier candidate ty LOOK;destruct(ENV identifier candidate ty LOOK)as[LIVE PRIVATE];split;
        [eapply Mem.store_valid_block_1;[exact WRITE|exact LIVE]|exact PRIVATE]. }
  pose proof(gateway_outcome_assignment_segment backend ge input output environment parameters object data_block data_offset before
    LAYOUT COPY CLOSED POINTER STORE)as SEGMENT.
  destruct(gateway_source_segment_cut backend ge _ _ _ _ SEGMENT before world events value after next CONTEXT RUN)
    as(prefix &suffix &assigned &current &EVENTS &QUIET &PREFIX &[AFTER_CONTEXT AFTER_ENVIRONMENT] &REST).
  destruct(gateway_actual_owned_outcome_return backend ge python objects types default_allocator instances leases owned decimal_float detached
    io stable thread_errno heap_allocation runtime allocations reference_threads environment parameters object(Vptr data_block data_offset)
    class ledger owner ticket held assigned current suffix value after next AFTER_ENVIRONMENT AFTER_CONTEXT REST)as[SAME[FINAL RETURN_QUIET]].
  split;[exact SAME|]. split;[exact FINAL|]. rewrite EVENTS;apply Forall_app;split;[exact QUIET|exact RETURN_QUIET].
Qed.

End OwnedOutcomeResult.
