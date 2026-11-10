(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Getter roots survive the actual quiet suffix and source return. *)
From Stdlib Require Import List Lia.
From compcert Require Import Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectThreads
  GatewayObjectDiscipline GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceHeld GatewayReferenceThreads GatewayReferenceMoves
  GatewayReferenceFrames GatewayReferencePlaces GatewayReferenceExecution GatewayReferenceReturnPath GatewayReferenceRetained
  GatewayHeldGILViews GatewayValueReturns GatewayOutcomeGetterSource GatewayFramedRuntime GatewayThreadRuntime GatewayStreamInterface GatewayReadonly GatewayRuntimeCuts.
Import ListNotations.
Local Close Scope lean_scope.

Section ObservationContexts.
Context {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
  (python:World->python_world)(objects:World->gateway_object_heap)
  (decimal_float:list BinNums.Z->Floats.float->Prop)(detached:Values.val->mem->World->Prop)
  (io:Event->option gateway_native_io)(stable:World->block->BinNums.Z->Prop)(thread_errno:World->int)
  (heap_allocation:block->BinNums.Z->Prop).
Let native:=fun world object=>gateway_native_private(python world)object.
Let base:=gateway_python_discipline python objects detached.
Context(runtime:gateway_thread_runtime backend io native stable base thread_errno)
  (references:gateway_reference_thread_contract backend native stable base heap_allocation python objects).

Definition gateway_observation_owned_context ledger held memory world:Prop:=
  gateway_objects_ready(python world)(objects world)memory /\
    gateway_reference_scope python objects decimal_float ledger held world.

Lemma gateway_observation_owned_context_closed ledger held:
  gateway_ambient_closed backend(gateway_observation_owned_context ledger held).
Proof.
  intros before world after next[NORMAL SCOPE]INTERFERENCE;split.
  - exact(proj1(gateway_thread_ambient _ _ _ _ _ _ runtime None before world after next NORMAL INTERFERENCE)).
  - eapply gateway_reference_scope_thread_effect;[exact SCOPE|].
    eapply gateway_reference_thread_ambient with(mode:=None);[exact references|exact NORMAL|exact INTERFERENCE].
Qed.

Definition gateway_observation_borrowed_context ledger held pointer description memory world:Prop:=
  gateway_observation_owned_context ledger held memory world /\
    gateway_borrowed_description python objects decimal_float pointer description world.

Lemma gateway_observation_borrowed_context_closed(views:gateway_held_gil_views backend python objects)
    ledger held pointer description:
  gateway_ambient_closed backend(gateway_observation_borrowed_context ledger held pointer description).
Proof.
  intros before world after next[[NORMAL SCOPE]BORROWED]INTERFERENCE;split.
  - eapply gateway_observation_owned_context_closed;[exact(conj NORMAL SCOPE)|exact INTERFERENCE].
  - eapply gateway_borrowed_description_thread;[exact BORROWED| |].
    + eapply gateway_reference_thread_ambient with(mode:=None);[exact references|exact NORMAL|exact INTERFERENCE].
    + exact(proj1(gateway_held_gil_values _ _ _ views before world after next(proj1(proj2 NORMAL))INTERFERENCE)).
Qed.

Theorem gateway_actual_owned_observation_return parameters selected ignored before world events actual after next ledger ticket held:
  parameters!_value=Some selected->gateway_object_pointer_value selected->
  gateway_reference_ledger_well_formed ledger->
  gateway_reference_owns ledger(gateway_reference_temporary 0 _value)ticket selected->
  gateway_reference_take(gateway_reference_result 0)(gateway_reference_entries ledger)=None->
  gateway_observation_owned_context ledger held before world->
  gateway_steps backend ge
    (gateway_live(Returnstate ignored(gateway_observation_release_cont parameters)before)world)events
    (gateway_live(Returnstate actual Kstop after)next)->
  exists final,
    actual=selected /\gateway_reference_ledger_well_formed final /\
    gateway_reference_apply(gateway_reference_move(gateway_reference_temporary 0 _value)(gateway_reference_result 0))
      (gateway_reference_valid ledger)=gateway_reference_valid final /\
    gateway_reference_owns final(gateway_reference_result 0)ticket selected /\
    gateway_reference_place_value ge(Returnstate actual Kstop after)(gateway_reference_result 0)selected /\
    gateway_observation_owned_context final held after next.
Proof.
  intros SELECTED POINTER WELL OWNED VACANT CONTEXT RUN.
  pose proof(gateway_observation_owned_context_closed ledger held)as CLOSED.
  destruct(gateway_uniform_edge_side_cut backend ge _ CLOSED
    (Returnstate ignored(gateway_observation_release_cont parameters)before)
    (State f_host_outcome_observation Sskip(Kseq gateway_observation_return_statement Kstop)empty_env parameters before)
    before world events actual after next ltac:(cbn;tauto)
    ltac:(intros;apply unchanged_store_edge,edge_returnstate)CONTEXT RUN)
    as(prefix &rest &called &owner &EVENTS &AMBIENT &PREFIX &READY &REST).
  destruct(gateway_uniform_edge_side_cut backend ge _ CLOSED
    (State f_host_outcome_observation Sskip(Kseq gateway_observation_return_statement Kstop)empty_env parameters called)
    (State f_host_outcome_observation gateway_observation_return_statement Kstop empty_env parameters called)
    called owner rest actual after next ltac:(cbn;tauto)
    ltac:(intros;apply unchanged_store_edge,edge_skip_seq)READY REST)
    as(pending &suffix &return_memory &return_world &REST_EVENTS &WAITING &TO_RETURN &RETURN_READY &FROM_RETURN).
  destruct(gateway_reference_actual_source_return backend ge f_host_outcome_observation
    (Etempvar _value(tptr(Tstruct __object noattr)))_value Kstop empty_env parameters selected
    return_memory return_world suffix actual after next ledger ticket
    eq_refl eq_refl ltac:(intros;apply old_expression_value,value_temp;exact SELECTED)
    ltac:(intros memory converted CAST;destruct POINTER as[NULL|[object[offset SAME]]];subst selected;
      cbn in CAST;inversion CAST;reflexivity)WELL OWNED VACANT FROM_RETURN)
    as(final &SAME &EXECUTION &MOVE &FINAL_WELL &RESULT &COUNTS).
  destruct(gateway_reference_move_scope python objects decimal_float ledger(gateway_reference_temporary 0 _value)
    (gateway_reference_result 0)ticket selected held return_world WELL OWNED VACANT(proj2 RETURN_READY))
    as(moved &MOVED &MOVED_WELL &MOVED_OWNED &MOVED_SCOPE &OTHERS).
  cbn[gateway_reference_depth]in MOVE;rewrite MOVE in MOVED;injection MOVED as EQUAL;subst moved.
  assert(FINAL:gateway_observation_owned_context final held after next).
  { eapply(gateway_readonly_run_side backend ge(gateway_observation_owned_context final held)
      (gateway_observation_owned_context_closed final held)
      (State f_host_outcome_observation gateway_observation_return_statement Kstop empty_env parameters return_memory)
      return_world suffix actual after next).
    - repeat split;reflexivity.
    - exact(conj(proj1 RETURN_READY)MOVED_SCOPE).
    - exact FROM_RETURN. }
  exists final;split;[exact SAME|]. split;[exact FINAL_WELL|]. split;[exact MOVE|]. split;[exact RESULT|]. split.
  - rewrite SAME;apply gateway_reference_result_binding.
  - exact FINAL.
Qed.
End ObservationContexts.
