(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Primitive callbacks retain only actual stable caller regions. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Ctypes Clight.
From HostGateway Require Import GatewayMachine GatewayOperations GatewayPrimitiveCalls GatewayThreadRuntime
  GatewayReadContext GatewayReadMemory GatewayStreamInterface.
Import ListNotations.
Open Scope Z_scope.

Section ReadonlyOperations.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
  (native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
  (discipline:option val->mem->World->Prop)(thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).
Variables stream_block data_block:Values.block.
Variables stream_offset data_offset:ptrofs.
Variable initial:gateway_stream_values.
Variable amount:Z.
Variable readonly:Values.block->Z->Prop.
Local Definition read_context mode:=gateway_read_context native_private stable_readonly discipline mode
  stream_block stream_offset initial data_block data_offset amount readonly.

Lemma gateway_read_context_readonly_frame mode memory current changed :
  read_context mode memory current ->
  gateway_native_frame native_private stable_readonly gateway_native_no_output current memory changed ->
  Mem.unchanged_on readonly memory changed.
Proof.
  intros CONTEXT FRAME;eapply gateway_native_frame_restrict;[exact FRAME| |].
  - intros object position HERE;right;exact(proj1(proj2(proj2(proj2 CONTEXT)))object position HERE).
  - intros object position HERE BAD;exact BAD.
Qed.

Definition gateway_read_reference reference mode memory current :Prop:=
  read_context mode memory current /\Mem.unchanged_on readonly reference memory.

Lemma gateway_read_reference_ambient reference mode :
  gateway_runtime_discipline backend(gateway_read_reference reference mode).
Proof.
  intros memory current changed future[CONTEXT HISTORY]INTERFERENCE.
  destruct(gateway_thread_ambient _ _ _ _ _ _ runtime mode memory current changed future
    (proj1 CONTEXT)INTERFERENCE)as[SIDE[ACCESS FRAME]].
  split.
  - eapply gateway_read_context_preserved;[exact CONTEXT|exact SIDE|exact ACCESS|exact FRAME].
  - eapply Mem.unchanged_on_trans;[exact HISTORY|].
    eapply gateway_read_context_readonly_frame;[exact CONTEXT|exact FRAME].
Qed.

Theorem gateway_actual_primitive_readonly ge external types result_type convention arguments first
    (last:val->option val)
    (operation:forall memory current result changed future observed,
      read_context first memory current ->
      gateway_external backend external types result_type convention arguments memory current result changed future observed ->
      read_context(last result)changed future /\Mem.unchanged_on readonly memory changed)
    before world events returned after next :
  read_context first before world ->
  gateway_steps backend ge
    (gateway_live(Callstate(External external types result_type convention)arguments Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->
  read_context(last returned)after next /\Mem.unchanged_on readonly before after.
Proof.
  intros READY RUN.
  assert(POST:forall memory current result changed future observed,
    gateway_read_reference before first memory current ->
    gateway_external backend external types result_type convention arguments memory current result changed future observed ->
    gateway_read_reference before(last result)changed future).
  { intros memory current result changed future observed[CONTEXT HISTORY]OPERATION.
    destruct(operation memory current result changed future observed CONTEXT OPERATION)as[AFTER FRAME].
    split;[exact AFTER|eapply Mem.unchanged_on_trans;[exact HISTORY|exact FRAME]]. }
  destruct(gateway_actual_primitive_context backend ge external types result_type convention arguments
    (gateway_read_reference before first)(fun result=>gateway_read_reference before(last result))
    (gateway_read_reference_ambient before first)ltac:(intro result;apply gateway_read_reference_ambient)
    POST before world events returned after next(conj READY(Mem.unchanged_on_refl _ before))RUN)
    as(prefix & suffix & called & called_world & changed & changed_world & observed &
      EVENTS & PENDING & PREFIX & CALLED & OPERATION & OUTPUT & SUFFIX & FINAL).
  exact FINAL.
Qed.
End ReadonlyOperations.
