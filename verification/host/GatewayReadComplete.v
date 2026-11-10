(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: Actual read entry, receive loop and counter store yield one receipt. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayOperations GatewayReadonly GatewayPrimitiveCalls
  GatewayRuntimeABI GatewayThreadRuntime GatewayReadContext GatewayStreamInterface GatewayReadyInterface GatewayStreamLayout
  GatewayStreamRelations GatewayReadSource GatewayReadGuard GatewayTransferBuffer GatewayTransferState GatewayTransferPost
  GatewayReadCounterMemory GatewayReadCounterSource GatewayFramedRuntime GatewayRuntimeTrace GatewayBufferReference
  GatewayPrefixContext GatewayPrefixBuffer GatewayTransportFrame GatewayTransferMath.
Import ListNotations.
Open Scope Z_scope.

Section CompleteRead.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
  (native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
  (discipline:option val->mem->World->Prop)(thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).
Variable ge:Clight.genv.
Context(ready_source:gateway_ready_source_producer backend ge io native_private stable_readonly(discipline None)).
Variables stream_block data_block:Values.block.
Variables stream_offset data_offset:ptrofs.
Variable initial:gateway_stream_values.
Variable amount:Z.
Variable readonly:Values.block->Z->Prop.
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
Local Definition context snapshot:=gateway_read_context native_private stable_readonly discipline None
  stream_block stream_offset snapshot data_block data_offset amount readonly.
Local Definition entry_context before owner:=gateway_owned_buffer_context native_private stable_readonly discipline
  stream_block data_block stream_offset data_offset initial amount readonly before owner None.
Local Lemma entry_ambient before owner:gateway_runtime_discipline backend(entry_context before owner).
Proof. apply gateway_owned_buffer_context_ambient with(io:=io)(thread_errno:=thread_errno);exact runtime. Qed.

Theorem actual_read_complete before world events after next :
  context initial before world ->
  gateway_steps backend ge
    (gateway_live(Callstate(Internal f_host_read)
      [Vptr stream_block stream_offset;Vptr data_block data_offset;Vlong(Int64.repr amount)]Kstop before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next) ->
  exists bytes final,gateway_read_receipt io before stream_block stream_offset initial data_block data_offset amount readonly
      events after bytes /\context final after next /\gateway_native_reference native_private before world after next.
Proof.
  intros CONTEXT RUN.
  assert(ENTRY:entry_context before world before world).
  { split;[exact CONTEXT|]. split;[apply gateway_buffer_reference_refl|apply gateway_native_reference_refl]. }
  destruct(actual_successful_read_source_transfer_execution backend ge stream_block stream_offset data_block data_offset
    amount initial before world events after next(entry_context before world)(entry_ambient before world)
    ltac:(intros memory current READY;exact(gateway_read_stream_cells _ _ _ _ _ _ _ _
      (proj2(proj2(proj2(proj2(proj1 READY)))))))transfer_symbol REMAINING ENTRY
    (gateway_read_amount _ _ _ _ _ _ _ _(proj2(proj2(proj2(proj2 CONTEXT)))))TRANSFER_SYMBOL TRANSFER_FUNCTION RUN)
    as[FITS[prefix[transfer_events[caller_events[called[called_world[transferred[transferred_world
      [EVENTS[QUIET[PREFIX[CALLED[TRANSFER CALLER]]]]]]]]]]]]].
  destruct CALLED as[CALLED[ENTRY_BUFFER ENTRY_NATIVE]].
  pose proof(proj2(proj2(proj2(proj2 CALLED))))as INPUT.
  destruct(actual_receive_transfer_buffer backend io native_private stable_readonly discipline thread_errno runtime ge ready_source
    stream_block data_block stream_offset readonly data_offset ready_symbol save_symbol receive_symbol errno_symbol restore_symbol
    READY_SYMBOL READY_FUNCTION SAVE_SYMBOL SAVE_FUNCTION RECEIVE_SYMBOL RECEIVE_FUNCTION ERRNO_SYMBOL ERRNO_FUNCTION
    RESTORE_SYMBOL RESTORE_FUNCTION DESCRIPTOR transfer_events initial amount called called_world transferred transferred_world CALLED TRANSFER)
    as(bytes & COUNT & OBSERVED & INITIALIZED & STATE & FRAME).
  destruct(gateway_transfer_read_context native_private stable_readonly discipline called called_world stream_block stream_offset
    initial data_block data_offset amount readonly transferred transferred_world INPUT STATE FRAME)
    as(final & FINAL_CONTEXT & TRANSPORT).
  set(tail_context:=gateway_prefix_context native_private stable_readonly discipline stream_block data_block stream_offset data_offset
    final amount readonly transferred transferred_world None data_offset amount bytes).
  assert(TAIL:tail_context transferred transferred_world).
  { split;[split;[exact FINAL_CONTEXT|split;[apply gateway_buffer_reference_refl|apply gateway_native_reference_refl]]|exact INITIALIZED]. }
  pose proof(actual_read_counter_script backend io native_private stable_readonly discipline thread_errno runtime ge
    stream_block data_block stream_offset data_offset final amount readonly bytes transferred transferred_world
    (stream_remaining initial)REMAINING transferred)as SCRIPT.
  destruct(gateway_runtime_path_return_exact backend ge tail_context
    (Returnstate(Vint Int.zero)(read_transfer_cont(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount
      (stream_remaining initial))transferred)(Vint Int.zero)
    (gateway_prefix_context native_private stable_readonly discipline stream_block data_block stream_offset data_offset
      (gateway_stream_debit final amount)amount readonly transferred transferred_world None data_offset amount bytes)
    transferred transferred_world caller_events(Vint Int.zero)after next TAIL SCRIPT CALLER)
    as[VALUE[[COUNTER_CONTEXT[COUNTER_BUFFER COUNTER_NATIVE]]AFTER_BYTES]].
  assert(CALLER_QUIET:Forall gateway_quiet_event caller_events).
  { eapply gateway_runtime_path_return_events;[exact TAIL|exact SCRIPT|exact CALLER]. }
  assert(DATA_PERMISSIONS:gateway_native_permissions before after data_block data_offset amount).
  { eapply gateway_native_permissions_transitive.
    - eapply gateway_buffer_native_permissions;[exact ENTRY_BUFFER|right;reflexivity].
    - eapply gateway_native_permissions_transitive;
        [exact(gateway_transport_data_permissions _ _ _ _ _ _ _ _ _ _ _ FRAME)|].
      eapply gateway_buffer_native_permissions;[exact COUNTER_BUFFER|right;reflexivity]. }
  assert(STREAM_PERMISSIONS:gateway_native_permissions before after stream_block stream_offset 48).
  { eapply gateway_native_permissions_transitive.
    - eapply gateway_buffer_native_permissions;[exact ENTRY_BUFFER|left;reflexivity].
    - eapply gateway_native_permissions_transitive;
        [exact(gateway_transport_stream_permissions _ _ _ _ _ _ _ _ _ _ _ FRAME)|].
      eapply gateway_buffer_native_permissions;[exact COUNTER_BUFFER|left;reflexivity]. }
  exists bytes,(gateway_stream_debit final amount);split.
  - constructor.
    + exact COUNT.
    + exact FITS.
    + rewrite EVENTS;repeat rewrite gateway_received_bytes_append.
      rewrite(gateway_quiet_received_empty io(stream_descriptor initial)prefix QUIET),OBSERVED,
        (gateway_quiet_received_empty io(stream_descriptor initial)caller_events CALLER_QUIET);cbn;apply app_nil_r.
    + exact AFTER_BYTES.
    + exact DATA_PERMISSIONS.
    + exact STREAM_PERMISSIONS.
    + exists(gateway_stream_debit final amount);split.
      * exact(gateway_read_stream_cells _ _ _ _ _ _ _ _(proj2(proj2(proj2(proj2 COUNTER_CONTEXT))))).
      * eapply gateway_read_after_transport;[exact TRANSPORT|apply gateway_stream_debit_relation].
    + eapply Mem.unchanged_on_trans;[exact(proj1 ENTRY_BUFFER)|].
      eapply Mem.unchanged_on_trans;
        [exact(gateway_transport_readonly _ _ _ _ _ _ _ _ _ _ _ FRAME)|exact(proj1 COUNTER_BUFFER)].
  - split;[exact COUNTER_CONTEXT|].
    eapply gateway_native_reference_transitive;[exact ENTRY_NATIVE|].
    eapply gateway_native_reference_transitive;
      [exact(gateway_transport_native _ _ _ _ _ _ _ _ _ _ _ FRAME)|exact COUNTER_NATIVE].
Qed.
End CompleteRead.
