(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: Supply the parser's read producer from actual application source. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayStreamInterface GatewayReadyInterface GatewayReadContext
  GatewayReadStable GatewayThreadRuntime GatewayReadComplete GatewayStreamLayout GatewayRuntimeABI GatewayBufferReference.
Import ListNotations.
Open Scope Z_scope.

Lemma gateway_read_receipt_restrict {Event}io before stream_block stream_offset initial data_block data_offset amount
    large small(events:list(gateway_event Event))after bytes :
  gateway_read_receipt io before stream_block stream_offset initial data_block data_offset amount large events after bytes ->
  (forall object position,small object position->large object position) ->
  gateway_read_receipt io before stream_block stream_offset initial data_block data_offset amount small events after bytes.
Proof.
  intros[COUNT FITS OBSERVED INITIALIZED DATA_PERMISSIONS STREAM_PERMISSIONS FINAL FRAME]INCLUDED;constructor;try assumption.
  eapply Mem.unchanged_on_implies;[exact FRAME|]. intros object position HERE LIVE;apply INCLUDED;exact HERE.
Qed.

Section ReadProducer.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
  (native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
  (discipline:option val->mem->World->Prop)(thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).
Variable ge:Clight.genv.
Context(ready_source:gateway_ready_source_producer backend ge io native_private stable_readonly(discipline None)).
Variables transfer_symbol ready_symbol save_symbol receive_symbol errno_symbol restore_symbol:Values.block.
Hypotheses
  (TRANSFER_SYMBOL:Genv.find_symbol ge _host_transfer=Some transfer_symbol)
  (TRANSFER_FUNCTION:Genv.find_funct_ptr ge transfer_symbol=Some(Internal f_host_transfer))
  (READY_SYMBOL:Genv.find_symbol ge _host_ready=Some ready_symbol)
  (READY_FUNCTION:Genv.find_funct_ptr ge ready_symbol=Some(Internal f_host_ready))
  (SAVE_SYMBOL:Genv.find_symbol ge _PyEval_SaveThread=Some save_symbol)
  (SAVE_FUNCTION:Genv.find_funct_ptr ge save_symbol=Some gateway_save_thread_definition)
  (RECEIVE_SYMBOL:Genv.find_symbol ge _recv=Some receive_symbol)
  (RECEIVE_FUNCTION:Genv.find_funct_ptr ge receive_symbol=Some gateway_receive_definition)
  (ERRNO_SYMBOL:Genv.find_symbol ge ___errno_location=Some errno_symbol)
  (ERRNO_FUNCTION:Genv.find_funct_ptr ge errno_symbol=Some gateway_errno_location_definition)
  (RESTORE_SYMBOL:Genv.find_symbol ge _PyEval_RestoreThread=Some restore_symbol)
  (RESTORE_FUNCTION:Genv.find_funct_ptr ge restore_symbol=Some gateway_restore_thread_definition)
  (DESCRIPTOR:stream_member_layout ge _descriptor 0)(REMAINING:stream_member_layout ge _remaining 24).

Theorem gateway_read_producer_of_ready :
  gateway_read_source_producer backend ge io native_private stable_readonly(discipline None).
Proof.
  intros before world stream_block stream_offset initial data_block data_offset amount readonly
    events after next SIDE STREAM DATA IMMUTABLE INPUT RUN.
  assert(CONTEXT:gateway_read_context native_private stable_readonly discipline None stream_block stream_offset initial
    data_block data_offset amount readonly before world).
  { split;[exact SIDE|]. split;[exact STREAM|]. split;[exact DATA|]. split;assumption. }
  pose proof(gateway_read_stable_context native_private stable_readonly discipline None before world stream_block stream_offset
    initial data_block data_offset amount readonly CONTEXT)as LARGE_CONTEXT.
  destruct(actual_read_complete backend io native_private stable_readonly discipline thread_errno runtime ge ready_source
    stream_block data_block stream_offset data_offset initial amount
    (gateway_stable_readonly stable_readonly before world stream_block data_block readonly)
    transfer_symbol ready_symbol save_symbol receive_symbol errno_symbol restore_symbol
    TRANSFER_SYMBOL TRANSFER_FUNCTION READY_SYMBOL READY_FUNCTION SAVE_SYMBOL SAVE_FUNCTION RECEIVE_SYMBOL RECEIVE_FUNCTION
    ERRNO_SYMBOL ERRNO_FUNCTION RESTORE_SYMBOL RESTORE_FUNCTION DESCRIPTOR REMAINING
    before world events after next LARGE_CONTEXT RUN)
    as(bytes & final & RECEIPT & FINAL_CONTEXT & NATIVE).
  exists bytes;split.
  - eapply gateway_read_receipt_restrict;[exact RECEIPT|]. intros object position HERE;left;exact HERE.
  - split;[exact(proj1 FINAL_CONTEXT)|]. split;[exact(proj1(proj2 FINAL_CONTEXT))|].
    split;[exact(proj1(proj2(proj2 FINAL_CONTEXT)))|]. split.
    + intros object position HERE;apply(proj1(proj2(proj2(proj2 FINAL_CONTEXT))));left;exact HERE.
    + split.
      * intros object LIVE PRIVATE;exact(proj2(NATIVE object LIVE PRIVATE)).
      * exact(gateway_read_stable_retained backend io native_private stable_readonly discipline thread_errno runtime
          before world stream_block stream_offset final data_block data_offset amount readonly after next FINAL_CONTEXT).
Qed.
End ReadProducer.
