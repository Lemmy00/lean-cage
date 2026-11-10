(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: Sender callbacks retain the actual stable payload cells. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Memdata Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewayMachine GatewayRuntime GatewayRuntimeABI GatewayOperations
  GatewayThreadRuntime GatewayReadContext GatewayStreamInterface GatewayReadonly GatewayReadonlyOperations
  GatewayPrimitiveCalls GatewayBufferReference GatewayTransferRuntime GatewaySendRuntime.
Import ListNotations.
Open Scope Z_scope.

Section Retention.
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
Local Definition context mode:=gateway_read_context native_private stable_readonly discipline mode
  stream_block stream_offset initial auxiliary_block auxiliary_offset auxiliary_amount readonly.
Definition gateway_send_loaded reference owner mode count bytes memory current:=
  gateway_owned_buffer_context native_private stable_readonly discipline
    stream_block auxiliary_block stream_offset auxiliary_offset initial auxiliary_amount readonly reference owner mode memory current /\
  Mem.loadbytes memory data_block(Ptrofs.unsigned data_offset)count=Some(inj_bytes bytes).

Lemma gateway_send_loaded_ambient reference owner mode count bytes:
  0<=count<=amount->gateway_runtime_discipline backend(gateway_send_loaded reference owner mode count bytes).
Proof.
  intros COUNT before world after next[CONTEXT LOAD]AMBIENT.
  pose proof(gateway_owned_buffer_context_ambient backend io native_private stable_readonly discipline thread_errno runtime
    stream_block auxiliary_block stream_offset auxiliary_offset initial auxiliary_amount readonly reference owner mode
    before world after next CONTEXT AMBIENT)as RETAINED.
  destruct(gateway_thread_ambient _ _ _ _ _ _ runtime mode before world after next
    (proj1(proj1 CONTEXT))AMBIENT)as[SIDE[ACCESS FRAME]].
  split;[exact RETAINED|].
  eapply Mem.loadbytes_unchanged_on.
  - eapply gateway_read_context_readonly_frame;[exact(proj1 CONTEXT)|exact FRAME].
  - intros;apply PAYLOAD;lia.
  - exact LOAD.
Qed.

Theorem gateway_actual_no_output_sender external types result_type convention arguments first
    (last:val->option val)(property:val->Prop)
    (operation:forall memory current result changed future observed,
      discipline first memory current->
      gateway_external backend external types result_type convention arguments memory current result changed future observed->
      discipline(last result)changed future /\gateway_access_retained native_private stable_readonly memory current future /\
      gateway_native_frame native_private stable_readonly gateway_native_no_output current memory changed /\
      property result)
    reference owner count bytes before world events returned after next:
  0<=count<=amount->gateway_send_loaded reference owner first count bytes before world->
  gateway_steps backend ge
    (gateway_live(Callstate(External external types result_type convention)arguments Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next)->
  property returned /\gateway_send_loaded reference owner(last returned)count bytes after next.
Proof.
  intros COUNT READY RUN.
  destruct(gateway_actual_primitive_context backend ge external types result_type convention arguments
    (gateway_send_loaded reference owner first count bytes)
    (fun result memory current=>property result /\gateway_send_loaded reference owner(last result)count bytes memory current)
    (gateway_send_loaded_ambient reference owner first count bytes COUNT)
    ltac:(intros result memory current changed future[PROP CONTEXT]AMBIENT;split;[exact PROP|];
      exact(gateway_send_loaded_ambient reference owner(last result)count bytes COUNT memory current changed future CONTEXT AMBIENT))
    ltac:(intros memory current result changed future observed[[CONTEXT[HISTORY OWNERSHIP]]LOAD]OPERATION;
      destruct(operation memory current result changed future observed(proj1 CONTEXT)OPERATION)
        as[SIDE[ACCESS[FRAME PROPERTY]]];split;[exact PROPERTY|];split;
      [split;[eapply gateway_read_context_rethread;[exact CONTEXT|exact SIDE|exact ACCESS|exact FRAME]|];split;
        [eapply gateway_buffer_reference_transitive;[exact HISTORY|];split;
          [eapply gateway_read_context_readonly_frame;[exact CONTEXT|exact FRAME]
          |eapply gateway_context_buffer_permissions;[exact CONTEXT|exact FRAME]]
        |eapply gateway_native_reference_transitive;[exact OWNERSHIP|];
          eapply gateway_native_reference_operation;[exact ACCESS|exact FRAME]]
      |eapply Mem.loadbytes_unchanged_on;
        [eapply gateway_read_context_readonly_frame;[exact CONTEXT|exact FRAME]
        |intros;apply PAYLOAD;lia|exact LOAD]])
    before world events returned after next READY RUN)
    as(prefix & suffix & called & called_world & changed & changed_world & observed &
      EVENTS & PENDING & PREFIX & CALLED & OPERATION & OUTPUT & SUFFIX & FINAL).
  exact FINAL.
Qed.

Theorem gateway_actual_sender_errno mode reference owner count bytes before world events returned after next:
  0<=count<=amount->gateway_send_loaded reference owner mode count bytes before world->
  gateway_steps backend ge(gateway_live(Callstate gateway_errno_location_definition[]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next)->
  (exists object offset,returned=Vptr object offset) /\
    gateway_send_loaded reference owner mode count bytes after next.
Proof.
  intros COUNT READY RUN.
  eapply gateway_actual_no_output_sender with(first:=mode)(last:=fun _=>mode)
    (property:=fun result=>exists object offset,result=Vptr object offset);
    [|exact COUNT|exact READY|exact RUN].
  intros memory current result changed future observed SIDE OPERATION.
  destruct(gateway_errno_location_operation _ _ _ _ _ _ runtime mode memory current result changed future observed SIDE OPERATION)
    as(object & offset & VALUE & POINTER & LOAD & NOT_NATIVE & NOT_STABLE & AFTER & ACCESS & FRAME & IO).
  split;[exact AFTER|]. split;[exact ACCESS|]. split;[exact FRAME|]. exists object,offset;exact VALUE.
Qed.

Theorem gateway_actual_sender_restore saved reference owner count bytes before world events returned after next:
  0<=count<=amount->gateway_send_loaded reference owner(Some saved)count bytes before world->
  gateway_steps backend ge(gateway_live(Callstate gateway_restore_thread_definition[saved]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next)->
  gateway_send_loaded reference owner None count bytes after next.
Proof.
  intros COUNT READY RUN.
  assert(RESULT:True /\gateway_send_loaded reference owner None count bytes after next).
  { eapply gateway_actual_no_output_sender with(first:=Some saved)(last:=fun _=>None)
      (property:=fun _=>True);
      [|exact COUNT|exact READY|exact RUN].
    intros memory current result changed future observed SIDE OPERATION.
    destruct(gateway_restore_thread_operation _ _ _ _ _ _ runtime saved memory current result changed future observed SIDE OPERATION)
      as(AFTER & ACCESS & FRAME & IO).
    split;[exact AFTER|]. split;[exact ACCESS|]. split;[exact FRAME|exact I]. }
  exact(proj2 RESULT).
Qed.
End Retention.
