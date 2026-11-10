(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Actual thread APIs retain the current native read buffers. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayRuntime GatewayRuntimeABI GatewayOperations
  GatewayThreadRuntime GatewayReadContext GatewayReadMemory GatewayStreamInterface GatewayPrimitiveCalls.
From HostGateway Require Import GatewayReceiveRuntime.
Import ListNotations.
Open Scope Z_scope.

Lemma gateway_read_context_rethread {World}(native_private:World->block->Prop)
    (stable_readonly:World->block->Z->Prop)(discipline:option val->mem->World->Prop)
    first last stream_block stream_offset initial data_block data_offset amount readonly before world after next :
  gateway_read_context native_private stable_readonly discipline first stream_block stream_offset initial
    data_block data_offset amount readonly before world ->
  discipline last after next ->gateway_access_retained native_private stable_readonly before world next ->
  gateway_native_frame native_private stable_readonly gateway_native_no_output world before after ->
  gateway_read_context native_private stable_readonly discipline last stream_block stream_offset initial
    data_block data_offset amount readonly after next.
Proof.
  intros[SIDE BUFFER]LAST ACCESS FRAME.
  assert(RAW:gateway_read_context native_private stable_readonly(fun _ _ _=>True)first
    stream_block stream_offset initial data_block data_offset amount readonly before world)
    by(split;[exact I|exact BUFFER]).
  pose proof(gateway_read_context_preserved native_private stable_readonly(fun _ _ _=>True)first
    stream_block stream_offset initial data_block data_offset amount readonly before world after next
    RAW I ACCESS FRAME)as[_ RETAINED].
  split;[exact LAST|exact RETAINED].
Qed.

Section ThreadCalls.
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

Lemma transfer_context_ambient mode:gateway_runtime_discipline backend(read_context mode).
Proof. apply gateway_read_context_ambient with(io:=io)(thread_errno:=thread_errno);exact runtime. Qed.

Theorem actual_no_output_loaded_context external types result_type convention arguments first
    (last:val->option val)(result_property:val->Prop)
    (operation:forall memory current result changed future observed,
      discipline first memory current ->
      gateway_external backend external types result_type convention arguments memory current result changed future observed ->
      discipline(last result)changed future /\gateway_access_retained native_private stable_readonly memory current future /\
      gateway_native_frame native_private stable_readonly gateway_native_no_output current memory changed /\
      result_property result)
    count bytes before world events returned after next :
  read_context first before world ->
  Mem.loadbytes before data_block(Ptrofs.unsigned data_offset)count=Some(inj_bytes bytes) ->
  gateway_steps backend ge
    (gateway_live(Callstate(External external types result_type convention)arguments Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->
  result_property returned /\read_context(last returned)after next /\
  Mem.loadbytes after data_block(Ptrofs.unsigned data_offset)count=Some(inj_bytes bytes).
Proof.
  intros READY LOAD RUN.
  set(input:=fun memory current=>read_context first memory current /\
    Mem.loadbytes memory data_block(Ptrofs.unsigned data_offset)count=Some(inj_bytes bytes)).
  set(output:=fun result memory current=>result_property result /\read_context(last result)memory current /\
    Mem.loadbytes memory data_block(Ptrofs.unsigned data_offset)count=Some(inj_bytes bytes)).
  assert(POST:forall memory current result changed future observed,input memory current ->
    gateway_external backend external types result_type convention arguments memory current result changed future observed ->
    output result changed future).
  { intros memory current result changed future observed[CONTEXT DATA]OPERATION.
    destruct(operation memory current result changed future observed(proj1 CONTEXT)OPERATION)
      as[SIDE[ACCESS[FRAME PROPERTY]]].
    split;[exact PROPERTY|]. split.
    - eapply gateway_read_context_rethread;[exact CONTEXT|exact SIDE|exact ACCESS|exact FRAME].
    - assert(DATA_FRAME:Mem.unchanged_on(fun block _=>block=data_block)memory changed).
      { eapply gateway_native_frame_restrict;[exact FRAME| |].
        - intros block position SAME;subst block;left;exact(proj1(proj2(proj2 CONTEXT))).
        - intros block position SAME BAD;exact BAD. }
      eapply Mem.loadbytes_unchanged_on;[exact DATA_FRAME|intros;reflexivity|exact DATA]. }
  assert(INPUT_DISCIPLINE:gateway_runtime_discipline backend input).
  { apply(receive_loaded_context_ambient backend io native_private stable_readonly discipline thread_errno runtime
      stream_block stream_offset initial data_block data_offset amount readonly first count bytes). }
  assert(OUTPUT_DISCIPLINE:forall result,gateway_runtime_discipline backend(output result)).
  { intros result memory current changed future[PROPERTY CONTEXT]INTERFERENCE;split;[exact PROPERTY|].
    eapply(receive_loaded_context_ambient backend io native_private stable_readonly discipline thread_errno runtime
      stream_block stream_offset initial data_block data_offset amount readonly(last result)count bytes);
      [exact CONTEXT|exact INTERFERENCE]. }
  destruct(gateway_actual_primitive_context backend ge external types result_type convention arguments
    input output INPUT_DISCIPLINE OUTPUT_DISCIPLINE POST before world events returned after next(conj READY LOAD)RUN)
    as[prefix[suffix[called[called_world[changed[changed_world[observed
      [EVENTS[PENDING[PREFIX[CALLED[OPERATION[OUTPUT[SUFFIX FINAL]]]]]]]]]]]]]].
  exact FINAL.
Qed.

Theorem actual_saved_thread_read_context before world events returned after next :
  read_context None before world ->
  gateway_steps backend ge(gateway_live(Callstate gateway_save_thread_definition[]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->
  (exists block offset,returned=Vptr block offset) /\read_context(Some returned)after next.
Proof.
  intros READY RUN.
  assert(POST:forall memory current result changed future observed,
    read_context None memory current ->
    gateway_runtime_operation backend gateway_save_thread_definition[]memory current result changed future observed ->
    (exists block offset,result=Vptr block offset) /\read_context(Some result)changed future).
  { intros memory current result changed future observed CONTEXT OPERATION.
    destruct(gateway_save_thread_operation _ _ _ _ _ _ runtime memory current result changed future observed
      (proj1 CONTEXT)OPERATION)as[POINTER[SIDE[ACCESS[FRAME IO]]]].
    split;[exact POINTER|]. eapply gateway_read_context_rethread;
      [exact CONTEXT|exact SIDE|exact ACCESS|exact FRAME]. }
  destruct(gateway_actual_primitive_context backend ge _ _ _ _ []
    (read_context None)(fun result memory current=>
      (exists block offset,result=Vptr block offset) /\read_context(Some result)memory current)
    (transfer_context_ambient None)
    ltac:(intro result;intros memory current changed future[POINTER CONTEXT]INTERFERENCE;split;
      [exact POINTER|eapply transfer_context_ambient;[exact CONTEXT|exact INTERFERENCE]])
    POST before world events returned after next READY RUN)
    as[prefix[suffix[called[called_world[changed[changed_world[observed
      [EVENTS[PENDING[PREFIX[CALLED[OPERATION[OUTPUT[SUFFIX FINAL]]]]]]]]]]]]]].
  exact FINAL.
Qed.

Theorem actual_restored_thread_read_context saved before world events returned after next :
  read_context(Some saved)before world ->
  gateway_steps backend ge(gateway_live(Callstate gateway_restore_thread_definition[saved]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->read_context None after next.
Proof.
  intros READY RUN.
  assert(POST:forall memory current result changed future observed,
    read_context(Some saved)memory current ->
    gateway_runtime_operation backend gateway_restore_thread_definition[saved]memory current result changed future observed ->
    read_context None changed future).
  { intros memory current result changed future observed CONTEXT OPERATION.
    destruct(gateway_restore_thread_operation _ _ _ _ _ _ runtime saved memory current result changed future observed
      (proj1 CONTEXT)OPERATION)as[SIDE[ACCESS[FRAME IO]]].
    eapply gateway_read_context_rethread;[exact CONTEXT|exact SIDE|exact ACCESS|exact FRAME]. }
  destruct(gateway_actual_primitive_context backend ge _ _ _ _ [saved]
    (read_context(Some saved))(fun _=>read_context None)(transfer_context_ambient(Some saved))
    ltac:(intro result;apply transfer_context_ambient)POST before world events returned after next READY RUN)
    as[prefix[suffix[called[called_world[changed[changed_world[observed
      [EVENTS[PENDING[PREFIX[CALLED[OPERATION[OUTPUT[SUFFIX FINAL]]]]]]]]]]]]]].
  exact FINAL.
Qed.

Theorem actual_errno_location_read_context mode before world events returned after next :
  read_context mode before world ->
  gateway_steps backend ge(gateway_live(Callstate gateway_errno_location_definition[]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->
  (exists block offset,returned=Vptr block offset) /\read_context mode after next.
Proof.
  intros READY RUN.
  assert(POST:forall memory current result changed future observed,
    read_context mode memory current ->
    gateway_runtime_operation backend gateway_errno_location_definition[]memory current result changed future observed ->
    (exists block offset,result=Vptr block offset) /\read_context mode changed future).
  { intros memory current result changed future observed CONTEXT OPERATION.
    destruct(gateway_errno_location_operation _ _ _ _ _ _ runtime mode memory current result changed future observed
      (proj1 CONTEXT)OPERATION)
      as[object[offset[VALUE[POINTER[LOAD[NOT_NATIVE[NOT_STABLE[SIDE[ACCESS[FRAME IO]]]]]]]]]].
    split;[exists object,offset;exact VALUE|].
    eapply gateway_read_context_preserved;[exact CONTEXT|exact SIDE|exact ACCESS|exact FRAME]. }
  destruct(gateway_actual_primitive_context backend ge _ _ _ _ []
    (read_context mode)(fun result memory current=>
      (exists block offset,result=Vptr block offset) /\read_context mode memory current)
    (transfer_context_ambient mode)
    ltac:(intro result;intros memory current changed future[POINTER CONTEXT]INTERFERENCE;split;
      [exact POINTER|eapply transfer_context_ambient;[exact CONTEXT|exact INTERFERENCE]])
    POST before world events returned after next READY RUN)
    as[prefix[suffix[called[called_world[changed[changed_world[observed
      [EVENTS[PENDING[PREFIX[CALLED[OPERATION[OUTPUT[SUFFIX FINAL]]]]]]]]]]]]]].
  exact FINAL.
Qed.

Theorem actual_errno_location_loaded_context mode count bytes before world events returned after next :
  read_context mode before world ->
  Mem.loadbytes before data_block(Ptrofs.unsigned data_offset)count=Some(inj_bytes bytes) ->
  gateway_steps backend ge(gateway_live(Callstate gateway_errno_location_definition[]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->
  (exists block offset,returned=Vptr block offset) /\read_context mode after next /\
  Mem.loadbytes after data_block(Ptrofs.unsigned data_offset)count=Some(inj_bytes bytes).
Proof.
  intros READY LOAD RUN.
  eapply actual_no_output_loaded_context with(first:=mode)(last:=fun _=>mode)
    (result_property:=fun result=>exists block offset,result=Vptr block offset);
    [|exact READY|exact LOAD|exact RUN].
  intros memory current result changed future observed SIDE OPERATION.
  destruct(gateway_errno_location_operation _ _ _ _ _ _ runtime mode memory current result changed future observed SIDE OPERATION)
    as[object[offset[VALUE[POINTER[DATA[NOT_NATIVE[NOT_STABLE[AFTER[ACCESS[FRAME IO]]]]]]]]]].
  split;[exact AFTER|]. split;[exact ACCESS|]. split;[exact FRAME|]. exists object,offset;exact VALUE.
Qed.

Theorem actual_restored_thread_loaded_context saved count bytes before world events returned after next :
  read_context(Some saved)before world ->
  Mem.loadbytes before data_block(Ptrofs.unsigned data_offset)count=Some(inj_bytes bytes) ->
  gateway_steps backend ge(gateway_live(Callstate gateway_restore_thread_definition[saved]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->read_context None after next /\
  Mem.loadbytes after data_block(Ptrofs.unsigned data_offset)count=Some(inj_bytes bytes).
Proof.
  intros READY LOAD RUN.
  assert(RESULT:True /\read_context None after next /\
    Mem.loadbytes after data_block(Ptrofs.unsigned data_offset)count=Some(inj_bytes bytes)).
  { eapply actual_no_output_loaded_context with(first:=Some saved)(last:=fun _=>None)
      (result_property:=fun _=>True);
      [|exact READY|exact LOAD|exact RUN].
    intros memory current result changed future observed SIDE OPERATION.
    destruct(gateway_restore_thread_operation _ _ _ _ _ _ runtime saved memory current result changed future observed SIDE OPERATION)
      as[AFTER[ACCESS[FRAME IO]]].
    split;[exact AFTER|]. split;[exact ACCESS|]. split;[exact FRAME|exact I]. }
  exact(proj2 RESULT).
Qed.

Theorem actual_saved_thread_no_receive before world events returned after next descriptor :
  read_context None before world ->
  gateway_steps backend ge(gateway_live(Callstate gateway_save_thread_definition[]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->gateway_received_bytes io descriptor events=[].
Proof.
  intros READY RUN.
  eapply gateway_actual_primitive_no_receive with(input:=read_context None);
    [apply transfer_context_ambient| |exact READY|exact RUN].
  intros memory current result changed future observed CONTEXT OPERATION.
  destruct(gateway_save_thread_operation _ _ _ _ _ _ runtime memory current result changed future observed
    (proj1 CONTEXT)OPERATION)as[POINTER[SIDE[ACCESS[FRAME IO]]]];exact IO.
Qed.

Theorem actual_restored_thread_no_receive saved before world events returned after next descriptor :
  read_context(Some saved)before world ->
  gateway_steps backend ge(gateway_live(Callstate gateway_restore_thread_definition[saved]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->gateway_received_bytes io descriptor events=[].
Proof.
  intros READY RUN.
  eapply gateway_actual_primitive_no_receive with(input:=read_context(Some saved));
    [apply transfer_context_ambient| |exact READY|exact RUN].
  intros memory current result changed future observed CONTEXT OPERATION.
  destruct(gateway_restore_thread_operation _ _ _ _ _ _ runtime saved memory current result changed future observed
    (proj1 CONTEXT)OPERATION)as[SIDE[ACCESS[FRAME IO]]];exact IO.
Qed.

Theorem actual_errno_location_no_receive mode before world events returned after next descriptor :
  read_context mode before world ->
  gateway_steps backend ge(gateway_live(Callstate gateway_errno_location_definition[]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->gateway_received_bytes io descriptor events=[].
Proof.
  intros READY RUN.
  eapply gateway_actual_primitive_no_receive with(input:=read_context mode);
    [apply transfer_context_ambient| |exact READY|exact RUN].
  intros memory current result changed future observed CONTEXT OPERATION.
  destruct(gateway_errno_location_operation _ _ _ _ _ _ runtime mode memory current result changed future observed
    (proj1 CONTEXT)OPERATION)
    as[object[offset[VALUE[POINTER[LOAD[NOT_NATIVE[NOT_STABLE[SIDE[ACCESS[FRAME IO]]]]]]]]]];exact IO.
Qed.
End ThreadCalls.
