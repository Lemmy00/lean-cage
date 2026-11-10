(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Returning the fresh Outcome retains its assigned data and exact
   source-selected reference credits without an unindexed lease-release law. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewayContexts GatewayCallPath GatewayOutcomeAllocation GatewayOutcomeConstruction GatewayOutcomeMemory
  GatewayObjects GatewayPython GatewayObjectThreads GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceThreads GatewayObjectDiscipline GatewayReferences
  GatewayScopedMemory GatewayLocalRuntime GatewayReadonly GatewayFrames GatewayPathEvents GatewayOperations GatewayFramedRuntime
  GatewayThreadRuntime GatewayStreamInterface.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Section OwnedOutcomeReturn.
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

Definition gateway_owned_outcome_return_context object data class ledger owner ticket held memory world:Prop:=
  gateway_objects_ready(python world)(objects world)memory /\
  gateway_outcome_private_cell python owned memory world object /\Mem.load Mptr memory object 16=Some data /\
  instances world(Vptr object Ptrofs.zero)=Some class /\gateway_reference_owns ledger owner ticket(Vptr object Ptrofs.zero) /\
  gateway_reference_scope python objects decimal_float ledger held world.

Lemma gateway_owned_outcome_return_cell_frame object ledger owner ticket held before after world :
  gateway_objects_ready(python world)(objects world)after ->gateway_reference_scope python objects decimal_float ledger held world ->gateway_reference_owns ledger owner ticket(Vptr object Ptrofs.zero) ->
  gateway_outcome_private_cell python owned before world object ->
  Mem.unchanged_on(gateway_outcome_cell_region object)before after ->
  gateway_outcome_private_cell python owned after world object.
Proof.
  intros READY SCOPE LEASE[OWNED[RUNTIME[SEPARATE[ACCESS POINTER]]]]FRAME.
  split;[exact OWNED|]. split;[exact RUNTIME|]. split;[exact SEPARATE|]. split.
  - destruct ACCESS as[PERMISSIONS ALIGNMENT];split;[|exact ALIGNMENT].
    intros position RANGE;eapply Mem.perm_unchanged_on;[exact FRAME|split;[reflexivity|exact RANGE]|apply PERMISSIONS;exact RANGE].
  - assert(ROOT:gateway_rooted(python world)(objects world)(Vptr object Ptrofs.zero)).
    { eapply gateway_reference_owned_rooted;[exact(proj1 SCOPE)|exact LEASE]. }
    destruct READY as[[_[_[_[_ POINTERS]]]]OTHER].
    destruct(POINTERS(Vptr object Ptrofs.zero)ROOT)as(block &offset &SAME &VALID).
    inversion SAME;subst;exact VALID.
Qed.

Lemma gateway_owned_outcome_return_context_ambient object data class ledger owner ticket held :
  gateway_ambient_closed backend(gateway_owned_outcome_return_context object data class ledger owner ticket held).
Proof.
  intros before world after next[READY[CELL[LOAD[CLASS[LEASE HELD]]]]]INTERFERENCE.
  destruct(gateway_thread_ambient _ _ _ _ _ _ runtime None before world after next READY INTERFERENCE)as[NORMAL OTHERS].
  destruct(@gateway_outcome_cell_ambient World Event backend python objects types default_allocator instances leases owned io
    native stable allocations before world after next object READY CELL INTERFERENCE)as[AFTER_CELL[AFTER_CLASS FRAME]].
  pose proof(@gateway_reference_thread_ambient World Event backend native stable discipline heap_allocation python objects
    reference_threads None before world after next READY INTERFERENCE)as EFFECT.
  split;[exact NORMAL|]. split;[exact AFTER_CELL|]. split.
  - eapply Mem.load_unchanged_on;[exact FRAME|intros;split;[reflexivity|exact H]|exact LOAD].
  - split;[rewrite AFTER_CLASS;exact CLASS|]. split;[exact LEASE|]. eapply gateway_reference_scope_thread_effect;[exact HELD|exact EFFECT].
Qed.

Definition gateway_owned_outcome_return_state object data class ledger owner ticket held(state:gateway_state World):Prop:=
  match state with
  |gateway_live source world=>gateway_local_readonly_source native world source /\
    gateway_scoped_readonly(gateway_outcome_cell_region object)source /\
    gateway_owned_outcome_return_context object data class ledger owner ticket held(memory_of source)world
  |gateway_dead _ _=>True end.

Lemma gateway_owned_outcome_nonprimitive_trace source trace target:
  ~gateway_at_primitive source ->step2 ge source trace target ->trace=E0.
Proof. intros INTERNAL STEP;inversion STEP;subst;try reflexivity;exfalso;apply INTERNAL;exact I. Qed.

Lemma gateway_owned_outcome_return_step object data class ledger owner ticket held source world event target :
  gateway_owned_outcome_return_state object data class ledger owner ticket held(gateway_live source world) ->
  gateway_step backend ge(gateway_live source world)event target ->
  gateway_owned_outcome_return_state object data class ledger owner ticket held target /\
    match target with gateway_live _ _=>gateway_quiet_event event|gateway_dead _ _=>True end.
Proof.
  intros[LOCAL[SCOPED[READY[CELL[LOAD[CLASS[LEASE HELD]]]]]]]STEP.
  assert(INTERNAL:~gateway_at_primitive source)by(eapply gateway_local_readonly_not_primitive;exact LOCAL).
  destruct(gateway_nonprimitive_step backend ge _ _ _ _ INTERNAL STEP)
    as[[trace[following[EVENT[REAL TARGET]]]]|
      [[changed[current[EVENT[INTERFERENCE TARGET]]]]|[EVENT TARGET]]];subst.
  - destruct(gateway_local_readonly_source_step backend io native stable discipline thread_errno runtime ge None source world trace following
      LOCAL READY REAL)as[AFTER_LOCAL AFTER_READY].
    assert(LIVE:gateway_region_live(gateway_outcome_cell_region object)(memory_of source)).
    { intros candidate position[SAME RANGE];subst candidate.
      destruct CELL as[_[_[_[[PERMISSION ALIGNMENT]POINTER]]]].
      eapply Mem.perm_valid_block;apply(PERMISSION position);exact RANGE. }
    destruct(gateway_scoped_readonly_source_step ge(gateway_outcome_cell_region object)source trace following SCOPED LIVE REAL)
      as[AFTER_SCOPED FRAME].
    split.
    + split;[exact AFTER_LOCAL|]. split;[exact AFTER_SCOPED|]. split;[exact AFTER_READY|].
      split;[eapply gateway_owned_outcome_return_cell_frame;[exact AFTER_READY|exact HELD|exact LEASE|exact CELL|exact FRAME]|].
      split;[eapply Mem.load_unchanged_on;[exact FRAME|intros;split;[reflexivity|exact H]|exact LOAD]|].
      split;[exact CLASS|]. split;assumption.
    + left;f_equal;eapply gateway_owned_outcome_nonprimitive_trace;[exact INTERNAL|exact REAL].
  - destruct(gateway_thread_ambient _ _ _ _ _ _ runtime None _ _ _ _ READY INTERFERENCE)
      as[NORMAL[ACCESS FRAME]]. split.
    + split;[eapply gateway_local_readonly_ambient;[exact LOCAL|exact ACCESS|exact FRAME]|].
      split;[apply gateway_scoped_readonly_replace;exact SCOPED|]. rewrite gateway_replace_memory_of.
      eapply gateway_owned_outcome_return_context_ambient;
        [exact(conj READY(conj CELL(conj LOAD(conj CLASS(conj LEASE HELD)))))|exact INTERFERENCE].
    + right;reflexivity.
  - split;exact I.
Qed.

Lemma gateway_owned_outcome_return_run object data class ledger owner ticket held first events last :
  gateway_owned_outcome_return_state object data class ledger owner ticket held first ->gateway_steps backend ge first events last ->
  gateway_owned_outcome_return_state object data class ledger owner ticket held last /\
    match last with gateway_live _ _=>Forall gateway_quiet_event events|gateway_dead _ _=>True end.
Proof.
  intros INITIAL RUN;revert INITIAL;induction RUN;intro GOOD.
  - split;[exact GOOD|]. destruct state;[constructor|exact I].
  - destruct first as[source current|memory current].
    + destruct(gateway_owned_outcome_return_step object data class ledger owner ticket held source current observed middle GOOD H)as[POST QUIET].
      destruct middle as[following following_world|memory current_world].
      * destruct(IHRUN POST)as[LAST EVENTS];split;[exact LAST|].
        destruct last;[constructor;assumption|exact I].
      * destruct(gateway_dead_steps _ _ _ _ _ _ RUN)as[EMPTY DEAD];subst rest last;split;exact I.
    + inversion H.
Qed.

Theorem gateway_actual_owned_outcome_return environment parameters object data class ledger owner ticket held before world events returned after next :
  gateway_native_environment native world before environment ->
  gateway_owned_outcome_return_context object data class ledger owner ticket held before world ->
  gateway_steps backend ge(gateway_live(gateway_outcome_assigned_state environment parameters object before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->
  returned=Vptr object Ptrofs.zero /\gateway_owned_outcome_return_context object data class ledger owner ticket held after next /\
    Forall gateway_quiet_event events.
Proof.
  intros ENVIRONMENT CONTEXT RUN.
  assert(AVOIDS:gateway_environment_avoids(gateway_outcome_cell_region object)environment).
  { intros identifier candidate ty position LOOK[SAME RANGE];subst candidate.
    destruct(ENVIRONMENT identifier object ty LOOK)as[LIVE NATIVE].
    destruct CONTEXT as[_[[_[RUNTIME REST]]MORE]];exact(NATIVE RUNTIME). }
  assert(INITIAL:gateway_owned_outcome_return_state object data class ledger owner ticket held
    (gateway_live(gateway_outcome_assigned_state environment parameters object before)world)).
  { split;[split;[reflexivity|split;[reflexivity|exact ENVIRONMENT]]|].
    split;[split;[reflexivity|split;[reflexivity|exact AVOIDS]]|exact CONTEXT]. }
  pose proof(gateway_owned_outcome_return_run object data class ledger owner ticket held _ _ _ INITIAL RUN)as FINAL.
  split;[eapply gateway_outcome_final_return_identity;exact RUN|].
  destruct FINAL as[[_[_ LAST]]QUIET];split;assumption.
Qed.

End OwnedOutcomeReturn.
