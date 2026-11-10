(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: One actual receive iteration keeps its thread and byte provenance. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Globalenvs
  Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps.
From HostGateway Require Import GatewaySource GatewayMachine GatewayOperations GatewayReadonly GatewayContexts
  GatewayThreadRuntime GatewayRuntimeABI GatewayReadContext GatewayReadMemory GatewayStreamInterface GatewayStreamLayout
  GatewayTransferMath GatewayTransferSource GatewayTransferChunk GatewayTransferReceive GatewayTransferErrno
  GatewayTransferRestore GatewayTransferCalls GatewayTransferRuntime GatewayReceiveRuntime GatewayPrimitiveCalls
  GatewayControlPaths GatewayTransferClassification GatewayReadonlyOperations GatewayTransferReadonly GatewayBufferReference.
Import ListNotations.
Open Scope Z_scope.

Lemma actual_restored_iteration_prefix ge temporaries amount saved descriptor count pointer number ignored memory :
  gateway_retained_prefix ge
    (State f_host_transfer transfer_after_restore transfer_iteration_cont empty_env
      (transfer_number_values temporaries amount saved descriptor count pointer number)memory)
    (Returnstate ignored(transfer_restore_cont temporaries amount saved descriptor count pointer number)memory).
Proof.
  eapply gateway_prefix_next with(next:=State f_host_transfer Sskip
    (Kseq transfer_after_restore transfer_iteration_cont)empty_env
    (transfer_number_values temporaries amount saved descriptor count pointer number)memory);
    [cbn;tauto|intro another;apply unchanged_store_edge,edge_returnstate|].
  eapply gateway_prefix_next with(next:=State f_host_transfer transfer_after_restore transfer_iteration_cont empty_env
    (transfer_number_values temporaries amount saved descriptor count pointer number)memory);
    [cbn;tauto|intro another;apply unchanged_store_edge,edge_skip_seq|].
  change(gateway_retained_prefix ge
    (State f_host_transfer transfer_after_restore transfer_iteration_cont empty_env
      (transfer_number_values temporaries amount saved descriptor count pointer number)memory)
    (GatewayMachine.gateway_replace_memory
      (State f_host_transfer transfer_after_restore transfer_iteration_cont empty_env
        (transfer_number_values temporaries amount saved descriptor count pointer number)memory)memory));constructor.
Qed.

Section Iteration.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
  (native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
  (discipline:option val->mem->World->Prop)(thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).
Variable ge:Clight.genv.
Variables stream_block data_block:Values.block.
Variables stream_offset data_offset:ptrofs.
Variable initial:gateway_stream_values.
Variable size:Z.
Variable readonly:Values.block->Z->Prop.
Variables save_symbol receive_symbol errno_symbol restore_symbol:Values.block.
Hypotheses
  (SAVE_SYMBOL:Genv.find_symbol ge _PyEval_SaveThread=Some save_symbol)
  (SAVE_FUNCTION:Genv.find_funct_ptr ge save_symbol=Some gateway_save_thread_definition)
  (RECEIVE_SYMBOL:Genv.find_symbol ge _recv=Some receive_symbol)
  (RECEIVE_FUNCTION:Genv.find_funct_ptr ge receive_symbol=Some gateway_receive_definition)
  (ERRNO_SYMBOL:Genv.find_symbol ge ___errno_location=Some errno_symbol)
  (ERRNO_FUNCTION:Genv.find_funct_ptr ge errno_symbol=Some gateway_errno_location_definition)
  (RESTORE_SYMBOL:Genv.find_symbol ge _PyEval_RestoreThread=Some restore_symbol)
  (RESTORE_FUNCTION:Genv.find_funct_ptr ge restore_symbol=Some gateway_restore_thread_definition)
  (DESCRIPTOR:stream_member_layout ge _descriptor 0).
Local Definition read_context mode:=gateway_read_context native_private stable_readonly discipline mode
  stream_block stream_offset initial data_block data_offset size readonly.
Local Definition loaded_context mode count bytes memory current:=read_context mode memory current /\
  Mem.loadbytes memory data_block(Ptrofs.unsigned data_offset)(Z.max 0 count)=Some(inj_bytes bytes).
Local Lemma context_ambient mode:gateway_runtime_discipline backend(read_context mode).
Proof. apply gateway_read_context_ambient with(io:=io)(thread_errno:=thread_errno);exact runtime. Qed.
Local Lemma loaded_ambient mode count bytes:gateway_runtime_discipline backend(loaded_context mode count bytes).
Proof.
  apply(receive_loaded_context_ambient backend io native_private stable_readonly discipline thread_errno runtime
    stream_block stream_offset initial data_block data_offset size readonly mode(Z.max 0 count)bytes).
Qed.

Local Definition history_context reference owner mode memory current:=read_context mode memory current /\
  gateway_buffer_reference readonly stream_block data_block reference memory /\
  gateway_native_reference native_private reference owner memory current.
Local Definition loaded_history reference owner mode count bytes memory current:=history_context reference owner mode memory current /\
  Mem.loadbytes memory data_block(Ptrofs.unsigned data_offset)(Z.max 0 count)=Some(inj_bytes bytes).
Local Lemma history_ambient reference owner mode:gateway_runtime_discipline backend(history_context reference owner mode).
Proof.
  apply gateway_owned_buffer_context_ambient with(io:=io)(thread_errno:=thread_errno);exact runtime.
Qed.
Local Lemma loaded_history_ambient reference owner mode count bytes:
  gateway_runtime_discipline backend(loaded_history reference owner mode count bytes).
Proof.
  intros memory current changed future[[CONTEXT HISTORY]LOAD]INTERFERENCE.
  destruct(loaded_ambient mode count bytes memory current changed future(conj CONTEXT LOAD)INTERFERENCE)
    as[AFTER DATA].
  destruct(history_ambient reference owner mode memory current changed future(conj CONTEXT HISTORY)INTERFERENCE)
    as[_ RETAINED].
  split;[split;assumption|exact DATA].
Qed.

Theorem actual_receive_iteration_from_ready_readonly temporaries before world events after next :
  0<size<=Int64.max_unsigned ->temporaries!_size=Some(Vlong(Int64.repr size)) ->
  temporaries!_stream=Some(Vptr stream_block stream_offset) ->temporaries!_sending=Some(Vint Int.zero) ->
  temporaries!_cursor=Some(Vptr data_block data_offset) ->read_context None before world ->
  gateway_steps backend ge
    (gateway_live(Returnstate(Vint Int.zero)(transfer_ready_cont temporaries)before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next) ->
  exists prefix suffix memory current saved count bytes pointer number,
    events=prefix++suffix /\
    gateway_steps backend ge
      (gateway_live(Returnstate(Vint Int.zero)(transfer_ready_cont temporaries)before)world)prefix
      (gateway_live(State f_host_transfer transfer_after_restore transfer_iteration_cont empty_env
        (transfer_number_values temporaries size saved(stream_descriptor initial)(Int64.repr count)pointer number)memory)current) /\
    gateway_received_bytes io(stream_descriptor initial)prefix=bytes /\
    -1<=count<=transfer_chunk size /\Z.of_nat(length bytes)=Z.max 0 count /\
    loaded_context None count bytes memory current /\
    Mem.unchanged_on readonly before memory /\
    gateway_buffer_permissions stream_block data_block before memory /\
    gateway_native_reference native_private before world memory current /\
    (number=Vundef \/exists integer,number=Vint integer) /\
    gateway_steps backend ge
      (gateway_live(State f_host_transfer transfer_after_restore transfer_iteration_cont empty_env
        (transfer_number_values temporaries size saved(stream_descriptor initial)(Int64.repr count)pointer number)memory)current)suffix
      (gateway_live(Returnstate(Vint Int.zero)Kstop after)next).
Proof.
  intros SIZE SIZE_LOOK STREAM RECEIVE CURSOR READY RUN.
  assert(HREADY:history_context before world None before world)by(split;[exact READY|split;[apply gateway_buffer_reference_refl|apply gateway_native_reference_refl]]).
  destruct(actual_ready_callback_saves_thread backend ge(history_context before world None)(history_ambient before world None)
    temporaries size before world events(Vint Int.zero)after next save_symbol HREADY ltac:(lia)
    SIZE_LOOK SAVE_SYMBOL SAVE_FUNCTION RUN)
    as(p0 & save_events & save_rest & m0 & w0 & saved & m1 & w1 & E0S & Q0 & P0 & C0 & SAVE & R0).
  destruct(actual_saved_thread_read_context backend io native_private stable_readonly discipline thread_errno runtime ge
    stream_block stream_offset initial data_block data_offset size readonly m0 w0 save_events saved m1 w1(proj1 C0)SAVE)
    as(SAVED_POINTER & C1).
  pose proof(actual_saved_thread_owned_buffer backend io native_private stable_readonly discipline thread_errno runtime ge
    stream_block data_block stream_offset data_offset initial size readonly m0 w0 save_events saved m1 w1(proj1 C0)SAVE)as FSAVE.
  assert(H1:history_context before world(Some saved)m1 w1).
  { split;[exact C1|]. split.
    - eapply gateway_buffer_reference_transitive;[exact(proj1(proj2 C0))|exact(proj1 FSAVE)].
    - eapply gateway_native_reference_transitive;[exact(proj2(proj2 C0))|exact(proj2 FSAVE)]. }
  destruct(actual_saved_callback_receives backend ge(history_context before world(Some saved))(history_ambient before world(Some saved))
    temporaries size saved initial stream_block stream_offset data_block data_offset m1 w1 save_rest
    (Vint Int.zero)after next receive_symbol H1
    ltac:(intros memory current CONTEXT;exact(gateway_read_stream_cells _ _ _ _ _ _ _ _(proj2(proj2(proj2(proj2(proj1 CONTEXT)))))))
    STREAM RECEIVE CURSOR DESCRIPTOR RECEIVE_SYMBOL RECEIVE_FUNCTION R0)
    as(p1 & receive_events & receive_rest & m2 & w2 & received & m3 & w3 & E1 & Q1 & P1 & C2 & RECEIVED & R1).
  destruct(actual_receive_read_context backend io native_private stable_readonly discipline thread_errno runtime ge
    stream_block stream_offset initial data_block data_offset size readonly saved(transfer_chunk size)
    m2 w2 receive_events received m3 w3(proj1 C2)(proj1(transfer_chunk_bounds size ltac:(lia)))
    (proj2(transfer_chunk_bounds size ltac:(lia)))RECEIVED)
    as(count & bytes & COUNT & RECEIVED_VALUE & LENGTH & RECEIVE_BYTES & LOAD & C3).
  subst received.
  pose proof(actual_receive_owned_buffer backend io native_private stable_readonly discipline thread_errno runtime ge
    stream_block data_block stream_offset data_offset initial size readonly saved(transfer_chunk size)m2 w2 receive_events
    (Vlong(Int64.repr count))m3 w3(proj1 C2)(proj1(transfer_chunk_bounds size ltac:(lia)))
    (proj2(transfer_chunk_bounds size ltac:(lia)))RECEIVED)as FRECEIVE.
  assert(L3:loaded_history before world(Some saved)count bytes m3 w3).
  { split;[split;[exact C3|]|exact LOAD]. split.
    - eapply gateway_buffer_reference_transitive;[exact(proj1(proj2 C2))|exact(proj1 FRECEIVE)].
    - eapply gateway_native_reference_transitive;[exact(proj2(proj2 C2))|exact(proj2 FRECEIVE)]. }
  destruct(actual_received_callback_reads_errno backend ge(loaded_history before world(Some saved)count bytes)
    (loaded_history_ambient before world(Some saved)count bytes)temporaries size saved(stream_descriptor initial)(Int64.repr count)
    m3 w3 receive_rest(Vint Int.zero)after next errno_symbol L3 ERRNO_SYMBOL ERRNO_FUNCTION R1)
    as(p2 & errno_events & errno_rest & m4 & w4 & pointer & m5 & w5 & E2 & Q2 & P2 & C4 & ERRNO & R2).
  destruct(actual_errno_location_loaded_context backend io native_private stable_readonly discipline thread_errno runtime ge
    stream_block stream_offset initial data_block data_offset size readonly(Some saved)(Z.max 0 count)bytes
    m4 w4 errno_events pointer m5 w5(proj1(proj1 C4))(proj2 C4)ERRNO)as(ERRNO_POINTER & C5 & LOAD5).
  pose proof(actual_errno_location_owned_buffer backend io native_private stable_readonly discipline thread_errno runtime ge
    stream_block data_block stream_offset data_offset initial size readonly(Some saved)m4 w4 errno_events pointer m5 w5
    (proj1(proj1 C4))ERRNO)as FERRNO.
  assert(L5:loaded_history before world(Some saved)count bytes m5 w5).
  { split;[split;[exact C5|]|exact LOAD5]. split.
    - eapply gateway_buffer_reference_transitive;[exact(proj1(proj2(proj1 C4)))|exact(proj1 FERRNO)].
    - eapply gateway_native_reference_transitive;[exact(proj2(proj2(proj1 C4)))|exact(proj2 FERRNO)]. }
  destruct(actual_transfer_captures_errno backend ge temporaries size saved(stream_descriptor initial)(Int64.repr count)
    pointer m5 w5 errno_rest(Vint Int.zero)after next(loaded_history before world(Some saved)count bytes)
    (loaded_history_ambient before world(Some saved)count bytes)L5 R2)
    as(pc & capture_rest & mc & wc & number & EC & QC & PC & VALUE & CC & RC).
  destruct(actual_captured_callback_restores_thread backend ge(loaded_history before world(Some saved)count bytes)
    (loaded_history_ambient before world(Some saved)count bytes)temporaries size saved(stream_descriptor initial)(Int64.repr count)pointer number
    mc wc capture_rest(Vint Int.zero)after next restore_symbol CC SAVED_POINTER RESTORE_SYMBOL RESTORE_FUNCTION RC)
    as(p3 & restore_events & restore_rest & m6 & w6 & ignored & m7 & w7 & E3 & Q3 & P3 & C6 & RESTORED & R3).
  destruct(actual_restored_thread_loaded_context backend io native_private stable_readonly discipline thread_errno runtime ge
    stream_block stream_offset initial data_block data_offset size readonly saved(Z.max 0 count)bytes
    m6 w6 restore_events ignored m7 w7(proj1(proj1 C6))(proj2 C6)RESTORED)as(C7 & LOAD7).
  pose proof(actual_restored_thread_owned_buffer backend io native_private stable_readonly discipline thread_errno runtime ge
    stream_block data_block stream_offset data_offset initial size readonly saved m6 w6 restore_events ignored m7 w7
    (proj1(proj1 C6))RESTORED)as FRESTORE.
  assert(L7:loaded_history before world None count bytes m7 w7).
  { split;[split;[exact C7|]|exact LOAD7]. split.
    - eapply gateway_buffer_reference_transitive;[exact(proj1(proj2(proj1 C6)))|exact(proj1 FRESTORE)].
    - eapply gateway_native_reference_transitive;[exact(proj2(proj2(proj1 C6)))|exact(proj2 FRESTORE)]. }
  destruct(gateway_prefix_side_cut backend ge(loaded_history before world None count bytes)(loaded_history_ambient before world None count bytes)
    (State f_host_transfer transfer_after_restore transfer_iteration_cont empty_env
      (transfer_number_values temporaries size saved(stream_descriptor initial)(Int64.repr count)pointer number)m7)
    (Returnstate ignored(transfer_restore_cont temporaries size saved(stream_descriptor initial)(Int64.repr count)pointer number)m7)
    (actual_restored_iteration_prefix ge temporaries size saved(stream_descriptor initial)(Int64.repr count)pointer number ignored m7)
    m7 w7 restore_rest(Vint Int.zero)after next L7 R3)
    as(p4 & suffix & memory & current & E4 & Q4 & P4 & C8 & R4).
  cbn[GatewayMachine.gateway_replace_memory]in P4,R4.
  set(prefix:=(p0++save_events)++(p1++receive_events)++(p2++errno_events)++pc++
    gateway_source E0::(p3++restore_events)++p4).
  exists prefix,suffix,memory,current,saved,count,bytes,pointer,number.
  split.
  - unfold prefix;rewrite E0S,E1,E2,EC,E3,E4.
    repeat(rewrite <-app_assoc;cbn[app]);reflexivity.
  - split.
    + unfold prefix.
      eapply gateway_steps_append.
      * eapply gateway_call_body_prefix with(continuation:=transfer_save_cont temporaries size);
          [reflexivity|exact P0|exact SAVE].
      * eapply gateway_steps_append.
        -- eapply gateway_call_body_prefix with
             (continuation:=transfer_receive_cont temporaries size saved(stream_descriptor initial));
             [reflexivity|exact P1|exact RECEIVED].
        -- eapply gateway_steps_append.
           ++ eapply gateway_call_body_prefix with
                (continuation:=transfer_errno_cont temporaries size saved(stream_descriptor initial)(Int64.repr count));
                [reflexivity|exact P2|exact ERRNO].
           ++ eapply gateway_steps_append;[exact PC|].
              econstructor;[apply gateway_internal;[exact I|apply step_set;exact VALUE]|].
              eapply gateway_steps_append.
              ** eapply gateway_call_body_prefix with
                   (continuation:=transfer_restore_cont temporaries size saved(stream_descriptor initial)(Int64.repr count)pointer number);
                   [reflexivity|exact P3|exact RESTORED].
              ** exact P4.
    + split.
      * assert(B0:gateway_received_bytes io(stream_descriptor initial)p0=[])
          by(apply gateway_quiet_received_empty;exact Q0).
        assert(B1:gateway_received_bytes io(stream_descriptor initial)p1=[])
          by(apply gateway_quiet_received_empty;exact Q1).
        assert(B2:gateway_received_bytes io(stream_descriptor initial)p2=[])
          by(apply gateway_quiet_received_empty;exact Q2).
        assert(BC:gateway_received_bytes io(stream_descriptor initial)pc=[])
          by(apply gateway_quiet_received_empty;exact QC).
        assert(B3:gateway_received_bytes io(stream_descriptor initial)p3=[])
          by(apply gateway_quiet_received_empty;exact Q3).
        assert(B4:gateway_received_bytes io(stream_descriptor initial)p4=[])
          by(apply gateway_quiet_received_empty;exact Q4).
        pose proof(actual_saved_thread_no_receive backend io native_private stable_readonly discipline thread_errno runtime ge
          stream_block stream_offset initial data_block data_offset size readonly m0 w0 save_events saved m1 w1
          (stream_descriptor initial)(proj1 C0)SAVE)as BSAVE.
        pose proof(actual_errno_location_no_receive backend io native_private stable_readonly discipline thread_errno runtime ge
          stream_block stream_offset initial data_block data_offset size readonly(Some saved)m4 w4 errno_events pointer m5 w5
          (stream_descriptor initial)(proj1(proj1 C4))ERRNO)as BERRNO.
        pose proof(actual_restored_thread_no_receive backend io native_private stable_readonly discipline thread_errno runtime ge
          stream_block stream_offset initial data_block data_offset size readonly saved m6 w6 restore_events ignored m7 w7
          (stream_descriptor initial)(proj1(proj1 C6))RESTORED)as BRESTORE.
        unfold prefix;repeat rewrite gateway_received_bytes_append.
        rewrite B0,BSAVE,B1,RECEIVE_BYTES,B2,BERRNO,BC.
        cbn[app].
        change(bytes++gateway_received_bytes io(stream_descriptor initial)((p3++restore_events)++p4)=bytes).
        repeat rewrite gateway_received_bytes_append;rewrite B3,BRESTORE,B4;cbn;apply app_nil_r.
      * split;[exact COUNT|]. split;[exact LENGTH|]. split;[split;[exact(proj1(proj1 C8))|exact(proj2 C8)]|].
        split;[exact(proj1(proj1(proj2(proj1 C8))))|].
        split;[exact(proj2(proj1(proj2(proj1 C8))))|].
        split;[exact(proj2(proj2(proj1 C8)))|]. split.
        -- eapply actual_captured_errno_shape;exact VALUE.
        -- exact R4.
Qed.
Theorem actual_receive_iteration_from_ready temporaries before world events after next :
  0<size<=Int64.max_unsigned ->temporaries!_size=Some(Vlong(Int64.repr size)) ->
  temporaries!_stream=Some(Vptr stream_block stream_offset) ->temporaries!_sending=Some(Vint Int.zero) ->
  temporaries!_cursor=Some(Vptr data_block data_offset) ->read_context None before world ->
  gateway_steps backend ge
    (gateway_live(Returnstate(Vint Int.zero)(transfer_ready_cont temporaries)before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next) ->
  exists prefix suffix memory current saved count bytes pointer number,
    events=prefix++suffix /\
    gateway_steps backend ge
      (gateway_live(Returnstate(Vint Int.zero)(transfer_ready_cont temporaries)before)world)prefix
      (gateway_live(State f_host_transfer transfer_after_restore transfer_iteration_cont empty_env
        (transfer_number_values temporaries size saved(stream_descriptor initial)(Int64.repr count)pointer number)memory)current) /\
    gateway_received_bytes io(stream_descriptor initial)prefix=bytes /\
    -1<=count<=transfer_chunk size /\Z.of_nat(length bytes)=Z.max 0 count /\
    loaded_context None count bytes memory current /\
    (number=Vundef \/exists integer,number=Vint integer) /\
    gateway_steps backend ge
      (gateway_live(State f_host_transfer transfer_after_restore transfer_iteration_cont empty_env
        (transfer_number_values temporaries size saved(stream_descriptor initial)(Int64.repr count)pointer number)memory)current)suffix
      (gateway_live(Returnstate(Vint Int.zero)Kstop after)next).
Proof.
  intros SIZE SIZE_LOOK STREAM RECEIVE CURSOR READY RUN.
  destruct(actual_receive_iteration_from_ready_readonly temporaries before world events after next
    SIZE SIZE_LOOK STREAM RECEIVE CURSOR READY RUN)
    as(prefix & suffix & memory & current & saved & count & bytes & pointer & number &
      EVENTS & PREFIX & OBSERVED & COUNT & BYTES & CONTEXT & FRAME & PERMISSIONS & NATIVE & TYPE & SUFFIX).
  exists prefix,suffix,memory,current,saved,count,bytes,pointer,number.
  split;[exact EVENTS|]. split;[exact PREFIX|]. split;[exact OBSERVED|]. split;[exact COUNT|].
  split;[exact BYTES|]. split;[exact CONTEXT|]. split;assumption.
Qed.
End Iteration.
