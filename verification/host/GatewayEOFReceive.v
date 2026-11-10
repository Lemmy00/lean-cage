(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: The actual held EOF receive retains its own bytes and caller
   context. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Memdata Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayRuntime GatewayRuntimeABI GatewayOperations
  GatewayThreadRuntime GatewayReadContext GatewayReadMemory GatewayStreamInterface GatewayStreamMemory
  GatewayReceiveMemory GatewayReceiveRuntime GatewayPrimitiveCalls GatewayReadonly GatewayEOFNative GatewaySendRuntime GatewayBufferReference GatewayTransportFrame.
Import ListNotations.
Open Scope Z_scope.

Section ReceiveRuntime.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
  (native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
  (discipline:option val->mem->World->Prop)(thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno)
  (held:gateway_eof_receive_runtime backend io native_private stable_readonly discipline).
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

Theorem actual_eof_receive_read_context before world events returned after next :
  read_context None before world ->1<=amount ->
  gateway_steps backend ge
    (gateway_live(Callstate gateway_receive_definition
      [Vint(stream_descriptor initial);Vptr data_block data_offset;Vlong Int64.one;Vint Int.zero]Kstop before)world)
    events(gateway_live(Returnstate returned Kstop after)next) ->
  exists count bytes,
    -1<=count<=1 /\returned=Vlong(Int64.repr count) /\Z.of_nat(length bytes)=Z.max 0 count /\
    gateway_received_bytes io(stream_descriptor initial)events=bytes /\
    Mem.loadbytes after data_block(Ptrofs.unsigned data_offset)(Z.max 0 count)=Some(inj_bytes bytes) /\
    read_context None after next.
Proof.
  intros READY SPACE RUN.
  destruct(gateway_external_operation_of_run backend ge _ _ _ _ _ before world events returned after next RUN)
    as[prefix[suffix[called[called_world[changed[changed_world[observed
      [EVENTS[PENDING[PREFIX[OPERATION SUFFIX]]]]]]]]]]].
  assert(CALLED:read_context None called called_world).
  { eapply gateway_pending_run_ready with(source:=Callstate gateway_receive_definition
      [Vint(stream_descriptor initial);Vptr data_block data_offset;Vlong Int64.one;Vint Int.zero]Kstop before);
      [apply receive_context_ambient with(io:=io)(thread_errno:=thread_errno);exact runtime|exact READY|exact PENDING|exact PREFIX]. }
  destruct(gateway_eof_receive_operation _ _ _ _ _ held called called_world
    (stream_descriptor initial)data_block data_offset returned changed changed_world observed
    (proj1 CALLED)(proj1(proj2(proj2 CALLED)))
    (receive_context_pointer native_private stable_readonly discipline stream_block stream_offset initial
      data_block data_offset amount readonly None called called_world 1 CALLED ltac:(lia))OPERATION)
    as[count[bytes[COUNT[RETURNED[LENGTH[LOAD[IO[SIDE[ACCESS[PERMISSIONS FRAME]]]]]]]]]].
  assert(CONTEXT:read_context None changed changed_world).
  { eapply gateway_receive_read_context with(chunk:=1)(written:=Z.max 0 count);
      [exact CALLED|exact SIDE|exact ACCESS|lia|exact SPACE|exact PERMISSIONS|exact FRAME]. }
  assert(FINAL:read_context None after next /\
    Mem.loadbytes after data_block(Ptrofs.unsigned data_offset)(Z.max 0 count)=Some(inj_bytes bytes)).
  { exact(gateway_readonly_run_side backend ge
      (fun memory current=>read_context None memory current /\
        Mem.loadbytes memory data_block(Ptrofs.unsigned data_offset)(Z.max 0 count)=Some(inj_bytes bytes))
      (receive_loaded_context_ambient backend io native_private stable_readonly discipline thread_errno runtime
        stream_block stream_offset initial data_block data_offset amount readonly None(Z.max 0 count)bytes)
      (Returnstate returned Kstop changed)changed_world suffix returned after next I(conj CONTEXT LOAD)SUFFIX). }
  exists count,bytes;split;[exact COUNT|]. split;[exact RETURNED|]. split;[exact LENGTH|]. split.
  - rewrite(gateway_external_received_projection backend ge io events returned after next prefix suffix
      changed changed_world observed(stream_descriptor initial)EVENTS PENDING SUFFIX).
    unfold gateway_received_event;rewrite IO,Int.eq_true;reflexivity.
  - split;[exact(proj2 FINAL)|exact(proj1 FINAL)].
Qed.

Theorem actual_eof_receive_owned_buffer before world events returned after next:
  read_context None before world->1<=amount->
  gateway_steps backend ge
    (gateway_live(Callstate gateway_receive_definition
      [Vint(stream_descriptor initial);Vptr data_block data_offset;Vlong Int64.one;Vint Int.zero]Kstop before)world)
    events(gateway_live(Returnstate returned Kstop after)next)->
  gateway_buffer_reference readonly stream_block data_block before after /\
  gateway_native_reference native_private before world after next.
Proof.
  intros READY SPACE RUN.
  assert(RESULT:read_context None after next /\gateway_buffer_reference readonly stream_block data_block before after /\
    gateway_native_reference native_private before world after next).
  { eapply gateway_actual_primitive_owned_buffer with(first:=None)(last:=fun _=>None);
      [exact runtime| |exact READY|exact RUN].
    intros memory current result changed future observed CONTEXT OPERATION.
    destruct(gateway_eof_receive_operation _ _ _ _ _ held memory current(stream_descriptor initial)data_block data_offset
      result changed future observed(proj1 CONTEXT)(proj1(proj2(proj2 CONTEXT)))
      (receive_context_pointer native_private stable_readonly discipline stream_block stream_offset initial data_block data_offset amount readonly
        None memory current 1 CONTEXT ltac:(lia))OPERATION)
      as(count&bytes&COUNT&VALUE&LENGTH&LOAD&IO&SIDE&ACCESS&PERMISSIONS&FRAME).
    destruct(gateway_receive_read_context native_private stable_readonly discipline None memory current changed future
      stream_block stream_offset initial data_block data_offset amount readonly 1(Z.max 0 count)
      CONTEXT SIDE ACCESS ltac:(lia)SPACE PERMISSIONS FRAME)as[AFTER[PROTECTED FULL_PERMISSIONS]].
    split;[exact AFTER|]. split.
    - split.
      + eapply Mem.unchanged_on_implies;[exact PROTECTED|]. intros object position HERE;right;exact HERE.
      + eapply gateway_context_receive_permissions with(requested:=1)(written:=Z.max 0 count);
          [exact CONTEXT|lia|exact PERMISSIONS|exact FRAME].
    - eapply gateway_native_reference_operation;[exact ACCESS|exact FRAME]. }
  exact(proj2 RESULT).
Qed.

Theorem actual_eof_receive_no_send before world events returned after next descriptor:
  read_context None before world->1<=amount->
  gateway_steps backend ge
    (gateway_live(Callstate gateway_receive_definition
      [Vint(stream_descriptor initial);Vptr data_block data_offset;Vlong Int64.one;Vint Int.zero]Kstop before)world)
    events(gateway_live(Returnstate returned Kstop after)next)->gateway_sent_bytes io descriptor events=[].
Proof.
  intros READY SPACE RUN.
  destruct(gateway_external_operation_of_run backend ge _ _ _ _ _ before world events returned after next RUN)
    as(prefix&suffix&called&called_world&changed&changed_world&observed&EVENTS&PENDING&PREFIX&OPERATION&SUFFIX).
  assert(CALLED:read_context None called called_world).
  { eapply gateway_pending_run_ready with(source:=Callstate gateway_receive_definition
      [Vint(stream_descriptor initial);Vptr data_block data_offset;Vlong Int64.one;Vint Int.zero]Kstop before);
      [apply receive_context_ambient with(io:=io)(thread_errno:=thread_errno);exact runtime|exact READY|exact PENDING|exact PREFIX]. }
  destruct(gateway_eof_receive_operation _ _ _ _ _ held called called_world(stream_descriptor initial)data_block data_offset
    returned changed changed_world observed(proj1 CALLED)(proj1(proj2(proj2 CALLED)))
    (receive_context_pointer native_private stable_readonly discipline stream_block stream_offset initial data_block data_offset amount readonly
      None called called_world 1 CALLED ltac:(lia))OPERATION)
    as(count&bytes&COUNT&VALUE&LENGTH&LOAD&IO&REST).
  assert(EMPTY:gateway_sent_bytes io descriptor suffix=[]).
  { apply gateway_quiet_sent_empty;eapply Forall_impl.
    - intros event SAME;right;exact SAME.
    - eapply gateway_terminal_return_ambient;exact SUFFIX. }
  rewrite EVENTS,gateway_sent_bytes_append,(gateway_pending_sent_empty io descriptor prefix PENDING).
  change(gateway_sent_event io descriptor(gateway_primitive observed)++gateway_sent_bytes io descriptor suffix=[]).
  unfold gateway_sent_event;rewrite IO,EMPTY;reflexivity.
Qed.
End ReceiveRuntime.
