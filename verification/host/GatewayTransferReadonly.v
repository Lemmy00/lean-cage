(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: The actual transfer APIs preserve the caller's stable readonly cells. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayRuntime GatewayRuntimeABI GatewayThreadRuntime
  GatewayReadContext GatewayReadMemory GatewayStreamInterface GatewayTransferRuntime GatewayReceiveRuntime
  GatewayReceiveMemory GatewayReadonlyOperations GatewayBufferReference.
Import ListNotations.
Open Scope Z_scope.

Section TransferReadonly.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
  (native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
  (discipline:option val->mem->World->Prop)(thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).
Variable ge:Clight.genv.
Variables stream_block data_block:Values.block.
Variables stream_offset data_offset:ptrofs.
Variable initial:gateway_stream_values.
Variable amount:Z.
Variable readonly:Values.block->Z->Prop.
Local Definition read_context mode:=gateway_read_context native_private stable_readonly discipline mode
  stream_block stream_offset initial data_block data_offset amount readonly.

Theorem actual_saved_thread_owned_buffer before world events returned after next :
  read_context None before world ->
  gateway_steps backend ge(gateway_live(Callstate gateway_save_thread_definition[]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->gateway_buffer_reference readonly stream_block data_block before after /\
    gateway_native_reference native_private before world after next.
Proof.
  intros READY RUN.
  assert(RESULT:read_context(Some returned)after next /\gateway_buffer_reference readonly stream_block data_block before after /\
    gateway_native_reference native_private before world after next).
  { eapply gateway_actual_primitive_owned_buffer with(first:=None)(last:=@Some val);
      [exact runtime| |exact READY|exact RUN].
    intros memory current result changed future observed CONTEXT OPERATION.
    destruct(gateway_save_thread_operation _ _ _ _ _ _ runtime memory current result changed future observed
      (proj1 CONTEXT)OPERATION)as[POINTER[SIDE[ACCESS[FRAME IO]]]].
    split.
    - eapply gateway_read_context_rethread;[exact CONTEXT|exact SIDE|exact ACCESS|exact FRAME].
    - split.
      + split.
        * eapply gateway_read_context_readonly_frame;[exact CONTEXT|exact FRAME].
        * eapply gateway_context_buffer_permissions;[exact CONTEXT|exact FRAME].
      + eapply gateway_native_reference_operation;[exact ACCESS|exact FRAME]. }
  exact(proj2 RESULT).
Qed.

Theorem actual_errno_location_owned_buffer mode before world events returned after next :
  read_context mode before world ->
  gateway_steps backend ge(gateway_live(Callstate gateway_errno_location_definition[]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->gateway_buffer_reference readonly stream_block data_block before after /\
    gateway_native_reference native_private before world after next.
Proof.
  intros READY RUN.
  assert(RESULT:read_context mode after next /\gateway_buffer_reference readonly stream_block data_block before after /\
    gateway_native_reference native_private before world after next).
  { eapply gateway_actual_primitive_owned_buffer with(first:=mode)(last:=fun _=>mode);
      [exact runtime| |exact READY|exact RUN].
    intros memory current result changed future observed CONTEXT OPERATION.
    destruct(gateway_errno_location_operation _ _ _ _ _ _ runtime mode memory current result changed future observed
      (proj1 CONTEXT)OPERATION)
      as[object[offset[VALUE[POINTER[LOAD[NOT_NATIVE[NOT_STABLE[SIDE[ACCESS[FRAME IO]]]]]]]]]].
    split.
    - eapply gateway_read_context_preserved;[exact CONTEXT|exact SIDE|exact ACCESS|exact FRAME].
    - split.
      + split.
        * eapply gateway_read_context_readonly_frame;[exact CONTEXT|exact FRAME].
        * eapply gateway_context_buffer_permissions;[exact CONTEXT|exact FRAME].
      + eapply gateway_native_reference_operation;[exact ACCESS|exact FRAME]. }
  exact(proj2 RESULT).
Qed.

Theorem actual_restored_thread_owned_buffer saved before world events returned after next :
  read_context(Some saved)before world ->
  gateway_steps backend ge(gateway_live(Callstate gateway_restore_thread_definition[saved]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->gateway_buffer_reference readonly stream_block data_block before after /\
    gateway_native_reference native_private before world after next.
Proof.
  intros READY RUN.
  assert(RESULT:read_context None after next /\gateway_buffer_reference readonly stream_block data_block before after /\
    gateway_native_reference native_private before world after next).
  { eapply gateway_actual_primitive_owned_buffer with(first:=Some saved)(last:=fun _=>None);
      [exact runtime| |exact READY|exact RUN].
    intros memory current result changed future observed CONTEXT OPERATION.
    destruct(gateway_restore_thread_operation _ _ _ _ _ _ runtime saved memory current result changed future observed
      (proj1 CONTEXT)OPERATION)as[SIDE[ACCESS[FRAME IO]]].
    split.
    - eapply gateway_read_context_rethread;[exact CONTEXT|exact SIDE|exact ACCESS|exact FRAME].
    - split.
      + split.
        * eapply gateway_read_context_readonly_frame;[exact CONTEXT|exact FRAME].
        * eapply gateway_context_buffer_permissions;[exact CONTEXT|exact FRAME].
      + eapply gateway_native_reference_operation;[exact ACCESS|exact FRAME]. }
  exact(proj2 RESULT).
Qed.

Theorem actual_receive_owned_buffer saved chunk before world events returned after next :
  read_context(Some saved)before world ->0<chunk<=65536 ->chunk<=amount ->
  gateway_steps backend ge
    (gateway_live(Callstate gateway_receive_definition
      [Vint(stream_descriptor initial);Vptr data_block data_offset;Vlong(Int64.repr chunk);Vint Int.zero]Kstop before)world)
    events(gateway_live(Returnstate returned Kstop after)next) ->gateway_buffer_reference readonly stream_block data_block before after /\
    gateway_native_reference native_private before world after next.
Proof.
  intros READY CHUNK SPACE RUN.
  assert(RESULT:read_context(Some saved)after next /\gateway_buffer_reference readonly stream_block data_block before after /\
    gateway_native_reference native_private before world after next).
  { eapply gateway_actual_primitive_owned_buffer with(first:=Some saved)(last:=fun _=>Some saved);
      [exact runtime| |exact READY|exact RUN].
    intros memory current result changed future observed CONTEXT OPERATION.
    assert(POINTER:gateway_native_pointer memory data_block data_offset chunk Writable).
    { destruct CONTEXT as[SIDE[STREAM[DATA[IMMUTABLE INPUT]]]].
      split;[lia|]. split;[pose proof(gateway_read_data_bounds _ _ _ _ _ _ _ _ INPUT);lia|].
      split;[exact(gateway_read_data_live _ _ _ _ _ _ _ _ INPUT)|].
      intros position RANGE;apply(gateway_read_data_owned _ _ _ _ _ _ _ _ INPUT position);lia. }
    destruct(gateway_receive_operation _ _ _ _ _ _ runtime saved memory current(stream_descriptor initial)
      data_block data_offset chunk result changed future observed(proj1 CONTEXT)
      (proj1(proj2(proj2 CONTEXT)))CHUNK POINTER OPERATION)
      as[count[bytes[COUNT[VALUE[LENGTH[LOAD[IO[SIDE[ACCESS[PERMISSIONS FRAME]]]]]]]]]].
    destruct(gateway_receive_read_context native_private stable_readonly discipline(Some saved)memory current changed future
      stream_block stream_offset initial data_block data_offset amount readonly chunk(Z.max 0 count)
      CONTEXT SIDE ACCESS ltac:(lia)SPACE PERMISSIONS FRAME)as[AFTER[PROTECTED FULL_PERMISSIONS]].
    split;[exact AFTER|]. split.
    - split.
      + eapply Mem.unchanged_on_implies;[exact PROTECTED|]. intros block position HERE;right;exact HERE.
      + eapply gateway_context_receive_permissions with(requested:=chunk)(written:=Z.max 0 count);
          [exact CONTEXT|lia|exact PERMISSIONS|exact FRAME].
    - eapply gateway_native_reference_operation;[exact ACCESS|exact FRAME]. }
  exact(proj2 RESULT).
Qed.
Theorem actual_saved_thread_buffer before world events returned after next :
  read_context None before world ->
  gateway_steps backend ge(gateway_live(Callstate gateway_save_thread_definition[]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->gateway_buffer_reference readonly stream_block data_block before after.
Proof.
  intros READY RUN.
  exact(proj1(actual_saved_thread_owned_buffer before world events returned after next READY RUN)).
Qed.

Theorem actual_errno_location_buffer mode before world events returned after next :
  read_context mode before world ->
  gateway_steps backend ge(gateway_live(Callstate gateway_errno_location_definition[]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->gateway_buffer_reference readonly stream_block data_block before after.
Proof.
  intros READY RUN.
  exact(proj1(actual_errno_location_owned_buffer mode before world events returned after next READY RUN)).
Qed.

Theorem actual_restored_thread_buffer saved before world events returned after next :
  read_context(Some saved)before world ->
  gateway_steps backend ge(gateway_live(Callstate gateway_restore_thread_definition[saved]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->gateway_buffer_reference readonly stream_block data_block before after.
Proof.
  intros READY RUN.
  exact(proj1(actual_restored_thread_owned_buffer saved before world events returned after next READY RUN)).
Qed.

Theorem actual_receive_buffer saved chunk before world events returned after next :
  read_context(Some saved)before world ->0<chunk<=65536 ->chunk<=amount ->
  gateway_steps backend ge
    (gateway_live(Callstate gateway_receive_definition
      [Vint(stream_descriptor initial);Vptr data_block data_offset;Vlong(Int64.repr chunk);Vint Int.zero]Kstop before)world)
    events(gateway_live(Returnstate returned Kstop after)next) ->gateway_buffer_reference readonly stream_block data_block before after.
Proof.
  intros READY CHUNK SPACE RUN.
  exact(proj1(actual_receive_owned_buffer saved chunk before world events returned after next READY CHUNK SPACE RUN)).
Qed.

Theorem actual_saved_thread_readonly before world events returned after next :
  read_context None before world ->
  gateway_steps backend ge(gateway_live(Callstate gateway_save_thread_definition[]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->Mem.unchanged_on readonly before after.
Proof.
  intros READY RUN.
  exact(proj1(actual_saved_thread_buffer before world events returned after next READY RUN)).
Qed.

Theorem actual_errno_location_readonly mode before world events returned after next :
  read_context mode before world ->
  gateway_steps backend ge(gateway_live(Callstate gateway_errno_location_definition[]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->Mem.unchanged_on readonly before after.
Proof.
  intros READY RUN.
  exact(proj1(actual_errno_location_buffer mode before world events returned after next READY RUN)).
Qed.

Theorem actual_restored_thread_readonly saved before world events returned after next :
  read_context(Some saved)before world ->
  gateway_steps backend ge(gateway_live(Callstate gateway_restore_thread_definition[saved]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->Mem.unchanged_on readonly before after.
Proof.
  intros READY RUN.
  exact(proj1(actual_restored_thread_buffer saved before world events returned after next READY RUN)).
Qed.

Theorem actual_receive_readonly saved chunk before world events returned after next :
  read_context(Some saved)before world ->0<chunk<=65536 ->chunk<=amount ->
  gateway_steps backend ge
    (gateway_live(Callstate gateway_receive_definition
      [Vint(stream_descriptor initial);Vptr data_block data_offset;Vlong(Int64.repr chunk);Vint Int.zero]Kstop before)world)
    events(gateway_live(Returnstate returned Kstop after)next) ->Mem.unchanged_on readonly before after.
Proof.
  intros READY CHUNK SPACE RUN.
  exact(proj1(actual_receive_buffer saved chunk before world events returned after next READY CHUNK SPACE RUN)).
Qed.
End TransferReadonly.
