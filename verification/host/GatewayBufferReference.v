(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: Native buffers retain full permissions through individual APIs. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Ctypes Clight.
From HostGateway Require Import GatewayMachine GatewayOperations GatewayPrimitiveCalls GatewayThreadRuntime
  GatewayReadContext GatewayReadMemory GatewayStreamInterface GatewayReadonlyOperations.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_buffer_permissions first second before after :Prop:=
  forall object,object=first \/object=second ->forall position kind permission,
    Mem.perm before object position kind permission<->Mem.perm after object position kind permission.

Definition gateway_buffer_reference readonly first second before after :Prop:=
  Mem.unchanged_on readonly before after /\gateway_buffer_permissions first second before after.

Definition gateway_native_reference {World}(native_private:World->block->Prop)before world after next :Prop:=
  forall object,Mem.valid_block before object->native_private world object ->
    Mem.valid_block after object /\native_private next object.

Lemma gateway_native_reference_refl {World}(native_private:World->block->Prop)memory world :
  gateway_native_reference native_private memory world memory world.
Proof. intros object LIVE PRIVATE;split;assumption. Qed.

Lemma gateway_native_reference_transitive {World}(native_private:World->block->Prop)
    before world middle current after next :
  gateway_native_reference native_private before world middle current ->
  gateway_native_reference native_private middle current after next ->
  gateway_native_reference native_private before world after next.
Proof. intros FIRST SECOND object LIVE PRIVATE;destruct(FIRST object LIVE PRIVATE)as[MIDDLE RETAINED];apply SECOND;assumption. Qed.

Lemma gateway_native_reference_operation {World}(native_private:World->block->Prop)stable_readonly output
    before world after next :
  gateway_access_retained native_private stable_readonly before world next ->
  gateway_native_frame native_private stable_readonly output world before after ->
  gateway_native_reference native_private before world after next.
Proof.
  intros[NATIVE STABLE]FRAME object LIVE PRIVATE;split;
    [eapply Mem.valid_block_unchanged_on;[exact FRAME|exact LIVE]|apply NATIVE;assumption].
Qed.

Lemma gateway_buffer_reference_refl readonly first second memory :
  gateway_buffer_reference readonly first second memory memory.
Proof. split;[apply Mem.unchanged_on_refl|unfold gateway_buffer_permissions;intros;reflexivity]. Qed.

Lemma gateway_buffer_reference_transitive readonly first second before middle after :
  gateway_buffer_reference readonly first second before middle ->
  gateway_buffer_reference readonly first second middle after ->
  gateway_buffer_reference readonly first second before after.
Proof.
  intros[FIRST PERM_FIRST][SECOND PERM_SECOND];split;
    [eapply Mem.unchanged_on_trans;[exact FIRST|exact SECOND]|].
  intros object HERE position kind permission;rewrite(PERM_FIRST object HERE);apply PERM_SECOND;exact HERE.
Qed.

Section BufferReference.
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

Lemma gateway_context_buffer_private mode memory current object :
  read_context mode memory current ->(object=stream_block \/object=data_block) ->
  native_private current object /\Mem.valid_block memory object.
Proof.
  intros[SIDE[STREAM[DATA[IMMUTABLE INPUT]]]][SAME|SAME];subst object;split;auto.
  - eapply gateway_read_stream_live;exact INPUT.
  - exact(gateway_read_data_live _ _ _ _ _ _ _ _ INPUT).
Qed.

Lemma gateway_context_buffer_permissions mode memory current changed :
  read_context mode memory current ->
  gateway_native_frame native_private stable_readonly gateway_native_no_output current memory changed ->
  gateway_buffer_permissions stream_block data_block memory changed.
Proof.
  intros CONTEXT FRAME object HERE position kind permission.
  destruct(gateway_context_buffer_private mode memory current object CONTEXT HERE)as[PRIVATE LIVE].
  apply(Mem.unchanged_on_perm _ _ _ FRAME object position kind permission);
    [split;[left;exact PRIVATE|intro BAD;exact BAD]|exact LIVE].
Qed.

Lemma gateway_context_receive_permissions mode memory current changed requested written :
  read_context mode memory current ->0<=written<=requested ->
  gateway_native_permissions memory changed data_block data_offset requested ->
  gateway_native_frame native_private stable_readonly(gateway_native_region data_block data_offset written)
    current memory changed ->gateway_buffer_permissions stream_block data_block memory changed.
Proof.
  intros CONTEXT RANGE PERMISSIONS FRAME object HERE position kind permission.
  destruct(gateway_context_buffer_private mode memory current object CONTEXT HERE)as[PRIVATE LIVE].
  destruct(peq object data_block)as[SAME|DIFFERENT].
  - subst object.
    destruct(Z_lt_ge_dec position(Ptrofs.unsigned data_offset))as[BEFORE|AFTER].
    + apply(Mem.unchanged_on_perm _ _ _ FRAME data_block position kind permission);
        [split;[left;exact PRIVATE|intros[_ BOUND];lia]|exact LIVE].
    + destruct(Z_lt_ge_dec position(Ptrofs.unsigned data_offset+requested))as[INSIDE|OUTSIDE].
      * apply PERMISSIONS;lia.
      * apply(Mem.unchanged_on_perm _ _ _ FRAME data_block position kind permission);
          [split;[left;exact PRIVATE|intros[_ BOUND];lia]|exact LIVE].
  - apply(Mem.unchanged_on_perm _ _ _ FRAME object position kind permission);
      [split;[left;exact PRIVATE|intros[SAME BOUND];congruence]|exact LIVE].
Qed.

Definition gateway_buffer_context reference mode memory current :Prop:=
  read_context mode memory current /\gateway_buffer_reference readonly stream_block data_block reference memory.

Lemma gateway_buffer_context_ambient reference mode:
  gateway_runtime_discipline backend(gateway_buffer_context reference mode).
Proof.
  intros memory current changed future[CONTEXT HISTORY]INTERFERENCE.
  destruct(gateway_thread_ambient _ _ _ _ _ _ runtime mode memory current changed future
    (proj1 CONTEXT)INTERFERENCE)as[SIDE[ACCESS FRAME]].
  split.
  - eapply gateway_read_context_preserved;[exact CONTEXT|exact SIDE|exact ACCESS|exact FRAME].
  - eapply gateway_buffer_reference_transitive;[exact HISTORY|]. split.
    + eapply gateway_read_context_readonly_frame;[exact CONTEXT|exact FRAME].
    + eapply gateway_context_buffer_permissions;[exact CONTEXT|exact FRAME].
Qed.

Theorem gateway_actual_primitive_buffer ge external types result_type convention arguments first(last:val->option val)
    (operation:forall memory current result changed future observed,
      read_context first memory current ->
      gateway_external backend external types result_type convention arguments memory current result changed future observed ->
      read_context(last result)changed future /\gateway_buffer_reference readonly stream_block data_block memory changed)
    before world events returned after next :
  read_context first before world ->
  gateway_steps backend ge
    (gateway_live(Callstate(External external types result_type convention)arguments Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->
  read_context(last returned)after next /\gateway_buffer_reference readonly stream_block data_block before after.
Proof.
  intros READY RUN.
  assert(POST:forall memory current result changed future observed,
    gateway_buffer_context before first memory current ->
    gateway_external backend external types result_type convention arguments memory current result changed future observed ->
    gateway_buffer_context before(last result)changed future).
  { intros memory current result changed future observed[CONTEXT HISTORY]OPERATION.
    destruct(operation memory current result changed future observed CONTEXT OPERATION)as[AFTER FRAME].
    split;[exact AFTER|eapply gateway_buffer_reference_transitive;[exact HISTORY|exact FRAME]]. }
  destruct(gateway_actual_primitive_context backend ge external types result_type convention arguments
    (gateway_buffer_context before first)(fun result=>gateway_buffer_context before(last result))
    (gateway_buffer_context_ambient before first)ltac:(intro result;apply gateway_buffer_context_ambient)
    POST before world events returned after next(conj READY(gateway_buffer_reference_refl readonly stream_block data_block before))RUN)
    as(prefix & suffix & called & called_world & changed & changed_world & observed &
      EVENTS & PENDING & PREFIX & CALLED & OPERATION & OUTPUT & SUFFIX & FINAL).
  exact FINAL.
Qed.

Definition gateway_owned_buffer_context reference owner mode memory current :Prop:=
  read_context mode memory current /\gateway_buffer_reference readonly stream_block data_block reference memory /\
  gateway_native_reference native_private reference owner memory current.

Lemma gateway_owned_buffer_context_ambient reference owner mode:
  gateway_runtime_discipline backend(gateway_owned_buffer_context reference owner mode).
Proof.
  intros memory current changed future[CONTEXT[HISTORY OWNERSHIP]]INTERFERENCE.
  destruct(gateway_thread_ambient _ _ _ _ _ _ runtime mode memory current changed future
    (proj1 CONTEXT)INTERFERENCE)as[SIDE[ACCESS FRAME]].
  destruct(gateway_buffer_context_ambient reference mode memory current changed future(conj CONTEXT HISTORY)INTERFERENCE)
    as[AFTER BUFFER].
  split;[exact AFTER|]. split;[exact BUFFER|].
  eapply gateway_native_reference_transitive;[exact OWNERSHIP|].
  eapply gateway_native_reference_operation;[exact ACCESS|exact FRAME].
Qed.

Theorem gateway_actual_primitive_owned_buffer ge external types result_type convention arguments first(last:val->option val)
    (operation:forall memory current result changed future observed,
      read_context first memory current ->
      gateway_external backend external types result_type convention arguments memory current result changed future observed ->
      read_context(last result)changed future /\gateway_buffer_reference readonly stream_block data_block memory changed /\
      gateway_native_reference native_private memory current changed future)
    before world events returned after next :
  read_context first before world ->
  gateway_steps backend ge
    (gateway_live(Callstate(External external types result_type convention)arguments Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->
  read_context(last returned)after next /\gateway_buffer_reference readonly stream_block data_block before after /\
    gateway_native_reference native_private before world after next.
Proof.
  intros READY RUN.
  assert(POST:forall memory current result changed future observed,
    gateway_owned_buffer_context before world first memory current ->
    gateway_external backend external types result_type convention arguments memory current result changed future observed ->
    gateway_owned_buffer_context before world(last result)changed future).
  { intros memory current result changed future observed[CONTEXT[HISTORY OWNERSHIP]]OPERATION.
    destruct(operation memory current result changed future observed CONTEXT OPERATION)as[AFTER[FRAME ACCESS]].
    split;[exact AFTER|]. split.
    - eapply gateway_buffer_reference_transitive;[exact HISTORY|exact FRAME].
    - eapply gateway_native_reference_transitive;[exact OWNERSHIP|exact ACCESS]. }
  destruct(gateway_actual_primitive_context backend ge external types result_type convention arguments
    (gateway_owned_buffer_context before world first)(fun result=>gateway_owned_buffer_context before world(last result))
    (gateway_owned_buffer_context_ambient before world first)ltac:(intro result;apply gateway_owned_buffer_context_ambient)
    POST before world events returned after next
    (conj READY(conj(gateway_buffer_reference_refl readonly stream_block data_block before)
      (gateway_native_reference_refl native_private before world)))RUN)
    as(prefix & suffix & called & called_world & changed & changed_world & observed &
      EVENTS & PENDING & PREFIX & CALLED & OPERATION & OUTPUT & SUFFIX & FINAL).
  exact FINAL.
Qed.
End BufferReference.
