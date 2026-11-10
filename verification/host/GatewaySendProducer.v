(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual sends preserve null empty fields and exact nonempty bytes. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Memdata Events Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayOperations GatewayReadonly GatewayThreadRuntime
  GatewayRuntimeABI GatewayStreamInterface GatewayReadContext GatewayStreamLayout GatewayReadyInterface
  GatewayTransferZero GatewayBufferReference GatewayTransportFrame GatewaySendSource GatewaySendReady
  GatewaySendRuntime GatewaySendPayload GatewaySendInterface GatewayStreamRelations GatewayReadMemory.
Import ListNotations.
Open Scope Z_scope.

Section Producer.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
  (native:World->block->Prop)(stable:World->block->Z->Prop)
  (discipline:option val->mem->World->Prop)(thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native stable discipline thread_errno).
Variable ge:Clight.genv.
Context(ready_source:gateway_ready_source_producer backend ge io native stable(discipline None))
  (ready_no_send:gateway_ready_no_data_send_source backend ge io native stable(discipline None)).
Variables ready_symbol save_symbol send_symbol errno_symbol restore_symbol:Values.block.
Hypotheses
  (READY_SYMBOL:Genv.find_symbol ge _host_ready=Some ready_symbol)
  (READY_FUNCTION:Genv.find_funct_ptr ge ready_symbol=Some(Internal f_host_ready))
  (SAVE_SYMBOL:Genv.find_symbol ge _PyEval_SaveThread=Some save_symbol)
  (SAVE_FUNCTION:Genv.find_funct_ptr ge save_symbol=Some gateway_save_thread_definition)
  (SEND_SYMBOL:Genv.find_symbol ge _send=Some send_symbol)
  (SEND_FUNCTION:Genv.find_funct_ptr ge send_symbol=Some gateway_send_definition)
  (ERRNO_SYMBOL:Genv.find_symbol ge ___errno_location=Some errno_symbol)
  (ERRNO_FUNCTION:Genv.find_funct_ptr ge errno_symbol=Some gateway_errno_location_definition)
  (RESTORE_SYMBOL:Genv.find_symbol ge _PyEval_RestoreThread=Some restore_symbol)
  (RESTORE_FUNCTION:Genv.find_funct_ptr ge restore_symbol=Some gateway_restore_thread_definition)
  (DESCRIPTOR:stream_member_layout ge _descriptor 0).

Theorem gateway_send_producer_of_ready:
  gateway_send_source_producer backend ge io native stable(discipline None).
Proof.
  intros before world stream_block stream_offset initial pointer amount readonly events after next
    SIDE PRIVATE STABLE INPUT AMOUNT PAYLOAD SEPARATE RUN.
  assert(RAW:gateway_read_context native stable discipline None stream_block stream_offset initial
    stream_block stream_offset 0 readonly before world).
  { split;[exact SIDE|]. split;[exact PRIVATE|]. split;[exact PRIVATE|]. split;assumption. }
  destruct(Z.eq_dec amount 0)as[ZERO|NONZERO].
  - subst amount.
    set(context:=gateway_owned_buffer_context native stable discipline stream_block stream_block
      stream_offset stream_offset initial 0 readonly before world None).
    assert(INITIAL:context before world).
    { split;[exact RAW|]. split;[apply gateway_buffer_reference_refl|apply gateway_native_reference_refl]. }
    destruct(gateway_actual_empty_transfer backend ge context
      (gateway_owned_buffer_context_ambient backend io native stable discipline thread_errno runtime stream_block stream_block
        stream_offset stream_offset initial 0 readonly before world None)
      (Vptr stream_block stream_offset)pointer Int.one before world events(Vint Int.zero)after next INITIAL RUN)
      as[VALUE[FINAL QUIET]].
    destruct FINAL as[[AFTER[AFTER_PRIVATE[AUX[AFTER_STABLE AFTER_INPUT]]]][BUFFER NATIVE]].
    exists[];split.
    + constructor.
      * reflexivity.
      * apply gateway_quiet_sent_empty;exact QUIET.
      * left;split;reflexivity.
      * exists initial;split;[exact(gateway_read_stream_cells _ _ _ _ _ _ _ _ AFTER_INPUT)|apply gateway_transport_refl].
      * eapply gateway_transport_frame_buffers with(protected:=readonly);
          [intros;assumption|exact BUFFER|exact NATIVE].
    + split;[exact AFTER|]. split;assumption.
  - destruct PAYLOAD as[ZERO|(object & offset & POINTER & BOUND & COVER)];[contradiction|subst pointer].
    assert(LIVE:Mem.valid_block before object).
    { eapply(gateway_read_readonly_live _ _ _ _ _ _ _ _ INPUT object(Ptrofs.unsigned offset)).
      apply COVER;lia. }
    assert(INITIAL:gateway_read_context native stable discipline None stream_block stream_offset initial
      stream_block stream_offset 0 readonly before world /\
      gateway_transport_frame native readonly stream_block stream_offset stream_block stream_offset 0 before world before world).
    { split;[exact RAW|apply gateway_transport_frame_refl]. }
    destruct(actual_send_transfer_payload backend io native stable discipline thread_errno runtime ge ready_source ready_no_send
      stream_block object stream_offset readonly before world LIVE ready_symbol save_symbol send_symbol errno_symbol restore_symbol
      READY_SYMBOL READY_FUNCTION SAVE_SYMBOL SAVE_FUNCTION SEND_SYMBOL SEND_FUNCTION ERRNO_SYMBOL ERRNO_FUNCTION
      RESTORE_SYMBOL RESTORE_FUNCTION DESCRIPTOR events initial offset amount before world after next
      AMOUNT COVER BOUND SEPARATE INITIAL RUN)
      as[COUNT[LOAD(final & final_offset & final_size & FINAL & TRANSPORT)]].
    destruct FINAL as[[AFTER[AFTER_PRIVATE[AUX[AFTER_STABLE AFTER_INPUT]]]]FRAME].
    exists(gateway_sent_bytes io(stream_descriptor initial)events);split.
    + constructor;try assumption.
      * reflexivity.
      * right;exists object,offset;split;[reflexivity|exact LOAD].
      * exists final;split;[exact(gateway_read_stream_cells _ _ _ _ _ _ _ _ AFTER_INPUT)|exact TRANSPORT].
    + split;[exact AFTER|]. split;assumption.
Qed.
End Producer.
