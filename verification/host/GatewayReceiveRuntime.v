(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: Actual returned receive bytes survive the same primitive suffix. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Memdata Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayRuntime GatewayRuntimeABI GatewayOperations
  GatewayThreadRuntime GatewayReadContext GatewayReadMemory GatewayStreamInterface GatewayStreamMemory
  GatewayReceiveMemory GatewayPrimitiveCalls GatewayReadonly.
Import ListNotations.
Open Scope Z_scope.

Section ReceiveRuntime.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
  (native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
  (discipline:option val->mem->World->Prop)(thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).
Variable ge:Clight.genv.
Variables stream_block:Values.block.
Variable stream_offset:ptrofs.
Variable initial:gateway_stream_values.
Variable data_block:Values.block.
Variable data_offset:ptrofs.
Variable amount:Z.
Variable readonly:Values.block->Z->Prop.
Local Definition read_context mode:=gateway_read_context native_private stable_readonly discipline mode
  stream_block stream_offset initial data_block data_offset amount readonly.

Lemma receive_context_ambient mode:gateway_runtime_discipline backend(read_context mode).
Proof. apply gateway_read_context_ambient with(io:=io)(thread_errno:=thread_errno);exact runtime. Qed.

Lemma receive_loaded_context_ambient mode count bytes :
  gateway_runtime_discipline backend(fun memory current=>read_context mode memory current /\
    Mem.loadbytes memory data_block(Ptrofs.unsigned data_offset)count=Some(inj_bytes bytes)).
Proof.
  intros memory current changed future[CONTEXT LOAD]INTERFERENCE;split.
  - eapply receive_context_ambient;[exact CONTEXT|exact INTERFERENCE].
  - destruct(gateway_thread_ambient _ _ _ _ _ _ runtime mode memory current changed future
      (proj1 CONTEXT)INTERFERENCE)as[SIDE[ACCESS FRAME]].
    assert(DATA_FRAME:Mem.unchanged_on(fun block _=>block=data_block)memory changed).
    { eapply gateway_native_frame_restrict;[exact FRAME| |].
      - intros block position SAME;subst block;left;exact(proj1(proj2(proj2 CONTEXT))).
      - intros block position SAME BAD;exact BAD. }
    eapply Mem.loadbytes_unchanged_on;[exact DATA_FRAME|intros;reflexivity|exact LOAD].
Qed.

Lemma receive_context_pointer mode memory current chunk :
  read_context mode memory current ->0<=chunk<=amount ->
  gateway_native_pointer memory data_block data_offset chunk Writable.
Proof.
  intros[SIDE[STREAM_PRIVATE[DATA_PRIVATE[IMMUTABLE INPUT]]]]CHUNK.
  split;[lia|]. split;[pose proof(gateway_read_data_bounds _ _ _ _ _ _ _ _ INPUT);lia|].
  split;[exact(gateway_read_data_live _ _ _ _ _ _ _ _ INPUT)|].
  intros position RANGE;apply(gateway_read_data_owned _ _ _ _ _ _ _ _ INPUT position);lia.
Qed.

Theorem actual_receive_read_context saved chunk before world events returned after next :
  read_context(Some saved)before world ->0<chunk<=65536 ->chunk<=amount ->
  gateway_steps backend ge
    (gateway_live(Callstate gateway_receive_definition
      [Vint(stream_descriptor initial);Vptr data_block data_offset;Vlong(Int64.repr chunk);Vint Int.zero]Kstop before)world)
    events(gateway_live(Returnstate returned Kstop after)next) ->
  exists count bytes,
    -1<=count<=chunk /\returned=Vlong(Int64.repr count) /\Z.of_nat(length bytes)=Z.max 0 count /\
    gateway_received_bytes io(stream_descriptor initial)events=bytes /\
    Mem.loadbytes after data_block(Ptrofs.unsigned data_offset)(Z.max 0 count)=Some(inj_bytes bytes) /\
    read_context(Some saved)after next.
Proof.
  intros READY CHUNK SPACE RUN.
  destruct(gateway_external_operation_of_run backend ge _ _ _ _ _ before world events returned after next RUN)
    as[prefix[suffix[called[called_world[changed[changed_world[observed
      [EVENTS[PENDING[PREFIX[OPERATION SUFFIX]]]]]]]]]]].
  assert(CALLED:read_context(Some saved)called called_world).
  { eapply gateway_pending_run_ready with(source:=Callstate gateway_receive_definition
      [Vint(stream_descriptor initial);Vptr data_block data_offset;Vlong(Int64.repr chunk);Vint Int.zero]Kstop before);
      [apply receive_context_ambient|exact READY|exact PENDING|exact PREFIX]. }
  destruct(gateway_receive_operation _ _ _ _ _ _ runtime saved called called_world
    (stream_descriptor initial)data_block data_offset chunk returned changed changed_world observed
    (proj1 CALLED)(proj1(proj2(proj2 CALLED)))CHUNK
    (receive_context_pointer(Some saved)called called_world chunk CALLED ltac:(lia))OPERATION)
    as[count[bytes[COUNT[RETURNED[LENGTH[LOAD[IO[SIDE[ACCESS[PERMISSIONS FRAME]]]]]]]]]].
  assert(CONTEXT:read_context(Some saved)changed changed_world).
  { eapply gateway_receive_read_context with(chunk:=chunk)(written:=Z.max 0 count);
      [exact CALLED|exact SIDE|exact ACCESS|lia|exact SPACE|exact PERMISSIONS|exact FRAME]. }
  assert(FINAL:read_context(Some saved)after next /\
    Mem.loadbytes after data_block(Ptrofs.unsigned data_offset)(Z.max 0 count)=Some(inj_bytes bytes)).
  { exact(gateway_readonly_run_side backend ge
      (fun memory current=>read_context(Some saved)memory current /\
        Mem.loadbytes memory data_block(Ptrofs.unsigned data_offset)(Z.max 0 count)=Some(inj_bytes bytes))
      (receive_loaded_context_ambient(Some saved)(Z.max 0 count)bytes)
      (Returnstate returned Kstop changed)changed_world suffix returned after next I(conj CONTEXT LOAD)SUFFIX). }
  exists count,bytes;split;[exact COUNT|]. split;[exact RETURNED|]. split;[exact LENGTH|]. split.
  - rewrite(gateway_external_received_projection backend ge io events returned after next prefix suffix
      changed changed_world observed(stream_descriptor initial)EVENTS PENDING SUFFIX).
    unfold gateway_received_event;rewrite IO,Int.eq_true;reflexivity.
  - split;[exact(proj2 FINAL)|exact(proj1 FINAL)].
Qed.
End ReceiveRuntime.
