(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: A send observes the actual retained payload, including retries. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Memdata Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewayMachine GatewayRuntime GatewayRuntimeABI GatewayOperations
  GatewayThreadRuntime GatewayReadContext GatewayStreamInterface GatewayReadonly GatewayReadonlyOperations
  GatewayPrimitiveCalls GatewayBufferReference GatewayTransferMath.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_sent_event {Event}(io:Event->option gateway_native_io)
    (descriptor:int)(event:gateway_event Event):list Byte.int:=
  match event with
  |gateway_primitive observed|gateway_committed_lost observed=>
    match io observed with
    |Some(gateway_native_send actual _ _ bytes)=>if Int.eq actual descriptor then bytes else []
    |_=>[]
    end
  |_=>[]
  end.
Definition gateway_sent_bytes {Event}(io:Event->option gateway_native_io)
    (descriptor:int)(events:list(gateway_event Event)):=flat_map(gateway_sent_event io descriptor)events.

Lemma gateway_sent_bytes_append {Event}io descriptor(first second:list(gateway_event Event)):
  gateway_sent_bytes io descriptor(first++second)=
    gateway_sent_bytes io descriptor first++gateway_sent_bytes io descriptor second.
Proof. apply flat_map_app. Qed.
Lemma gateway_pending_sent_empty {Event}io descriptor(events:list(gateway_event Event)):
  Forall gateway_pending_event events->gateway_sent_bytes io descriptor events=[].
Proof. intro PENDING;induction PENDING;[reflexivity|]. destruct H as[SAME|SAME];subst;cbn;exact IHPENDING. Qed.
Lemma gateway_quiet_sent_empty {Event}io descriptor(events:list(gateway_event Event)):
  Forall gateway_quiet_event events->gateway_sent_bytes io descriptor events=[].
Proof. intro QUIET;induction QUIET;[reflexivity|]. destruct H as[SAME|SAME];subst;cbn;exact IHQUIET. Qed.

Section SendRuntime.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
  (native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
  (discipline:option val->mem->World->Prop)(thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).
Variable ge:Clight.genv.
Variables stream_block auxiliary_block data_block:Values.block.
Variables stream_offset auxiliary_offset data_offset:ptrofs.
Variable initial:gateway_stream_values.
Variables auxiliary_amount amount:Z.
Variable readonly:Values.block->Z->Prop.
Hypothesis PAYLOAD:forall position,
  Ptrofs.unsigned data_offset<=position<Ptrofs.unsigned data_offset+amount->readonly data_block position.
Hypothesis BOUND:Ptrofs.unsigned data_offset+amount<=Ptrofs.modulus.
Local Definition context mode:=gateway_read_context native_private stable_readonly discipline mode
  stream_block stream_offset initial auxiliary_block auxiliary_offset auxiliary_amount readonly.
Local Definition history reference owner mode:=gateway_owned_buffer_context native_private stable_readonly discipline
  stream_block auxiliary_block stream_offset auxiliary_offset initial auxiliary_amount readonly reference owner mode.
Local Definition loaded reference owner mode count bytes memory current:=history reference owner mode memory current /\
  Mem.loadbytes memory data_block(Ptrofs.unsigned data_offset)(Z.max 0 count)=Some(inj_bytes bytes).

Lemma gateway_send_context_pointer mode before world requested:
  context mode before world->0<requested<=amount->
  gateway_native_pointer before data_block data_offset requested Readable.
Proof.
  intros[SIDE[STREAM[AUX[STABLE INPUT]]]]REQUEST.
  split;[lia|]. split;[lia|]. split.
  - apply(gateway_read_readonly_live _ _ _ _ _ _ _ _ INPUT data_block(Ptrofs.unsigned data_offset)).
    apply PAYLOAD;lia.
  - intros position RANGE;apply(gateway_read_readonly_readable _ _ _ _ _ _ _ _ INPUT).
    apply PAYLOAD;lia.
Qed.

Local Lemma history_ambient reference owner mode:
  gateway_runtime_discipline backend(history reference owner mode).
Proof. eapply gateway_owned_buffer_context_ambient;exact runtime. Qed.
Local Lemma loaded_ambient reference owner mode count bytes:
  0<=Z.max 0 count<=amount->gateway_runtime_discipline backend(loaded reference owner mode count bytes).
Proof.
  intros COUNT before world after next[CONTEXT LOAD]AMBIENT.
  pose proof(history_ambient reference owner mode before world after next CONTEXT AMBIENT)as RETAINED.
  destruct(gateway_thread_ambient _ _ _ _ _ _ runtime mode before world after next
    (proj1(proj1 CONTEXT))AMBIENT)as[SIDE[ACCESS FRAME]].
  split;[exact RETAINED|].
  eapply Mem.loadbytes_unchanged_on.
  - eapply gateway_read_context_readonly_frame;[exact(proj1 CONTEXT)|exact FRAME].
  - intros;apply PAYLOAD;lia.
  - exact LOAD.
Qed.

Theorem actual_send_retained_context mode requested before world events returned after next:
  context mode before world->0<requested<=65536->requested<=amount->
  gateway_steps backend ge
    (gateway_live(Callstate gateway_send_definition
      [Vint(stream_descriptor initial);Vptr data_block data_offset;Vlong(Int64.repr requested);Vint(Int.repr 16384)]Kstop before)world)
    events(gateway_live(Returnstate returned Kstop after)next)->
  exists count bytes,
    -1<=count<=requested /\returned=Vlong(Int64.repr count) /\Z.of_nat(length bytes)=Z.max 0 count /\
    gateway_sent_bytes io(stream_descriptor initial)events=bytes /\
    gateway_received_bytes io(stream_descriptor initial)events=[] /\
    Mem.loadbytes after data_block(Ptrofs.unsigned data_offset)(Z.max 0 count)=Some(inj_bytes bytes) /\
    context mode after next /\gateway_buffer_reference readonly stream_block auxiliary_block before after /\
    gateway_native_reference native_private before world after next.
Proof.
  intros READY REQUEST SPACE RUN.
  destruct(gateway_external_operation_of_run backend ge _ _ _ _ _ before world events returned after next RUN)
    as(prefix & suffix & called & called_world & changed & changed_world & observed &
      EVENTS & PENDING & PREFIX & OPERATION & SUFFIX).
  assert(INPUT:history before world mode before world).
  { split;[exact READY|]. split;[apply gateway_buffer_reference_refl|apply gateway_native_reference_refl]. }
  assert(CALLED:history before world mode called called_world).
  { eapply gateway_pending_run_ready with(source:=Callstate gateway_send_definition
      [Vint(stream_descriptor initial);Vptr data_block data_offset;
       Vlong(Int64.repr requested);Vint(Int.repr 16384)]Kstop before);
      [apply history_ambient|exact INPUT|exact PENDING|exact PREFIX]. }
  destruct(gateway_send_operation _ _ _ _ _ _ runtime mode called called_world(stream_descriptor initial)
    data_block data_offset requested returned changed changed_world observed(proj1(proj1 CALLED))
    ltac:(right;intros;apply(proj1(proj2(proj2(proj2(proj1 CALLED)))));apply PAYLOAD;lia)
    REQUEST(gateway_send_context_pointer mode called called_world requested(proj1 CALLED)ltac:(lia))OPERATION)
    as(count & bytes & COUNT & VALUE & LENGTH & LOAD & IO & SIDE & ACCESS & FRAME).
  assert(AFTER:context mode changed changed_world).
  { eapply gateway_read_context_preserved;[exact(proj1 CALLED)|exact SIDE|exact ACCESS|exact FRAME]. }
  assert(HISTORY:history before world mode changed changed_world).
  { split;[exact AFTER|]. split.
    - eapply gateway_buffer_reference_transitive;[exact(proj1(proj2 CALLED))|]. split.
      + eapply gateway_read_context_readonly_frame;[exact(proj1 CALLED)|exact FRAME].
      + eapply gateway_context_buffer_permissions;[exact(proj1 CALLED)|exact FRAME].
    - eapply gateway_native_reference_transitive;[exact(proj2(proj2 CALLED))|].
      eapply gateway_native_reference_operation;[exact ACCESS|exact FRAME]. }
  assert(DATA:Mem.loadbytes changed data_block(Ptrofs.unsigned data_offset)(Z.max 0 count)=Some(inj_bytes bytes)).
  { eapply Mem.loadbytes_unchanged_on.
    - eapply gateway_read_context_readonly_frame;[exact(proj1 CALLED)|exact FRAME].
    - intros;apply PAYLOAD;lia.
    - exact LOAD. }
  assert(FINAL:loaded before world mode count bytes after next).
  { eapply gateway_readonly_run_side with(source:=Returnstate returned Kstop changed);
      [apply loaded_ambient;lia|exact I|split;[exact HISTORY|exact DATA]|exact SUFFIX]. }
  exists count,bytes;split;[exact COUNT|]. split;[exact VALUE|]. split;[exact LENGTH|]. split.
  - rewrite EVENTS,gateway_sent_bytes_append,(gateway_pending_sent_empty io _ _ PENDING).
    assert(EMPTY:gateway_sent_bytes io(stream_descriptor initial)suffix=[]).
    { apply gateway_quiet_sent_empty;eapply Forall_impl;
        [intros event SAME;right;exact SAME|eapply gateway_terminal_return_ambient;exact SUFFIX]. }
    change(gateway_sent_event io(stream_descriptor initial)(gateway_primitive observed)++
      gateway_sent_bytes io(stream_descriptor initial)suffix=bytes).
    rewrite EMPTY;unfold gateway_sent_event;rewrite IO,Int.eq_true,app_nil_r;reflexivity.
  - split.
    + rewrite(gateway_external_received_projection backend ge io events returned after next prefix suffix
        changed changed_world observed(stream_descriptor initial)EVENTS PENDING SUFFIX).
      unfold gateway_received_event;rewrite IO;reflexivity.
    + split;[exact(proj2 FINAL)|exact(proj1 FINAL)].
Qed.
End SendRuntime.
