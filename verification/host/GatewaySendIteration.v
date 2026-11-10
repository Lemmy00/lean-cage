(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: One real outgoing iteration retains its payload and exact byte event. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Globalenvs
  Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps.
From HostGateway Require Import GatewaySource GatewayMachine GatewayOperations GatewayReadonly GatewayContexts
  GatewayThreadRuntime GatewayRuntimeABI GatewayReadContext GatewayReadMemory GatewayStreamInterface GatewayStreamLayout
  GatewayTransferMath GatewayTransferSource GatewayTransferChunk GatewayTransferReceive GatewayTransferErrno
  GatewayTransferRestore GatewayTransferCalls GatewayTransferRuntime GatewayPrimitiveCalls GatewayControlPaths
  GatewayTransferClassification GatewayReadonlyOperations GatewayTransferReadonly GatewayBufferReference
  GatewaySendSource GatewaySendChunk GatewaySendOperation GatewaySendErrno GatewaySendRestore GatewaySendCuts
  GatewaySendRuntime GatewaySendRetention GatewaySendTrace.
Import ListNotations.
Open Scope Z_scope.

Lemma actual_restored_send_prefix ge temporaries amount saved descriptor count pointer number ignored memory:
  gateway_retained_prefix ge
    (State f_host_transfer transfer_after_restore transfer_iteration_cont empty_env
      (send_number_values temporaries amount saved descriptor count pointer number)memory)
    (Returnstate ignored(send_restore_cont temporaries amount saved descriptor count pointer number)memory).
Proof.
  eapply gateway_prefix_next with(next:=State f_host_transfer Sskip
    (Kseq transfer_after_restore transfer_iteration_cont)empty_env
    (send_number_values temporaries amount saved descriptor count pointer number)memory);
    [cbn;tauto|intro another;apply unchanged_store_edge,edge_returnstate|].
  eapply gateway_prefix_next with(next:=State f_host_transfer transfer_after_restore transfer_iteration_cont empty_env
    (send_number_values temporaries amount saved descriptor count pointer number)memory);
    [cbn;tauto|intro another;apply unchanged_store_edge,edge_skip_seq|].
  change(gateway_retained_prefix ge
    (State f_host_transfer transfer_after_restore transfer_iteration_cont empty_env
      (send_number_values temporaries amount saved descriptor count pointer number)memory)
    (gateway_replace_memory(State f_host_transfer transfer_after_restore transfer_iteration_cont empty_env
      (send_number_values temporaries amount saved descriptor count pointer number)memory)memory));constructor.
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
Hypothesis PAYLOAD:forall position,
  Ptrofs.unsigned data_offset<=position<Ptrofs.unsigned data_offset+size->readonly data_block position.
Hypothesis BOUND:Ptrofs.unsigned data_offset+size<=Ptrofs.modulus.
Variables save_symbol send_symbol errno_symbol restore_symbol:Values.block.
Hypotheses
  (SAVE_SYMBOL:Genv.find_symbol ge _PyEval_SaveThread=Some save_symbol)
  (SAVE_FUNCTION:Genv.find_funct_ptr ge save_symbol=Some gateway_save_thread_definition)
  (SEND_SYMBOL:Genv.find_symbol ge _send=Some send_symbol)
  (SEND_FUNCTION:Genv.find_funct_ptr ge send_symbol=Some gateway_send_definition)
  (ERRNO_SYMBOL:Genv.find_symbol ge ___errno_location=Some errno_symbol)
  (ERRNO_FUNCTION:Genv.find_funct_ptr ge errno_symbol=Some gateway_errno_location_definition)
  (RESTORE_SYMBOL:Genv.find_symbol ge _PyEval_RestoreThread=Some restore_symbol)
  (RESTORE_FUNCTION:Genv.find_funct_ptr ge restore_symbol=Some gateway_restore_thread_definition)
  (DESCRIPTOR:stream_member_layout ge _descriptor 0).
Local Definition context mode:=gateway_read_context native_private stable_readonly discipline mode
  stream_block stream_offset initial stream_block stream_offset 0 readonly.
Local Definition history reference owner mode:=gateway_owned_buffer_context native_private stable_readonly discipline
  stream_block stream_block stream_offset stream_offset initial 0 readonly reference owner mode.
Local Definition loaded reference owner mode count bytes:=gateway_send_loaded native_private stable_readonly discipline
  stream_block stream_block data_block stream_offset stream_offset data_offset initial 0 readonly reference owner mode count bytes.
Local Lemma history_ambient reference owner mode:gateway_runtime_discipline backend(history reference owner mode).
Proof. apply gateway_owned_buffer_context_ambient with(io:=io)(thread_errno:=thread_errno);exact runtime. Qed.
Local Lemma loaded_ambient reference owner mode count bytes:
  0<=count<=size->gateway_runtime_discipline backend(loaded reference owner mode count bytes).
Proof.
  intro COUNT;apply gateway_send_loaded_ambient with(io:=io)(thread_errno:=thread_errno)(amount:=size);
    [exact runtime|exact PAYLOAD|exact COUNT].
Qed.

Theorem actual_send_iteration_from_ready temporaries before world events after next:
  0<size<=Int64.max_unsigned->temporaries!_size=Some(Vlong(Int64.repr size))->
  temporaries!_stream=Some(Vptr stream_block stream_offset)->temporaries!_sending=Some(Vint Int.one)->
  temporaries!_cursor=Some(Vptr data_block data_offset)->context None before world->
  gateway_steps backend ge
    (gateway_live(Returnstate(Vint Int.zero)(transfer_send_ready_cont temporaries)before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next)->
  exists prefix suffix memory current saved count bytes pointer number,
    events=prefix++suffix /\
    gateway_steps backend ge
      (gateway_live(Returnstate(Vint Int.zero)(transfer_send_ready_cont temporaries)before)world)prefix
      (gateway_live(State f_host_transfer transfer_after_restore transfer_iteration_cont empty_env
        (send_number_values temporaries size saved(stream_descriptor initial)(Int64.repr count)pointer number)memory)current) /\
    gateway_sent_bytes io(stream_descriptor initial)prefix=bytes /\
    -1<=count<=transfer_chunk size /\Z.of_nat(length bytes)=Z.max 0 count /\
    loaded before world None(Z.max 0 count)bytes memory current /\
    (number=Vundef \/exists integer,number=Vint integer) /\
    gateway_steps backend ge
      (gateway_live(State f_host_transfer transfer_after_restore transfer_iteration_cont empty_env
        (send_number_values temporaries size saved(stream_descriptor initial)(Int64.repr count)pointer number)memory)current)suffix
      (gateway_live(Returnstate(Vint Int.zero)Kstop after)next).
Proof.
  intros SIZE SIZE_LOOK STREAM SENDING CURSOR READY RUN.
  assert(HREADY:history before world None before world).
  { split;[exact READY|]. split;[apply gateway_buffer_reference_refl|apply gateway_native_reference_refl]. }
  destruct(actual_send_ready_callback_saves_thread backend ge(history before world None)(history_ambient before world None)
    temporaries size before world events(Vint Int.zero)after next save_symbol HREADY ltac:(lia)
    SIZE_LOOK SAVE_SYMBOL SAVE_FUNCTION RUN)
    as(p0 & save_events & save_rest & m0 & w0 & saved & m1 & w1 & E0S & Q0 & P0 & C0 & SAVE & R0).
  destruct(actual_saved_thread_read_context backend io native_private stable_readonly discipline thread_errno runtime ge
    stream_block stream_offset initial stream_block stream_offset 0 readonly m0 w0 save_events saved m1 w1(proj1 C0)SAVE)
    as(SAVED_POINTER & C1).
  pose proof(actual_saved_thread_owned_buffer backend io native_private stable_readonly discipline thread_errno runtime ge
    stream_block stream_block stream_offset stream_offset initial 0 readonly m0 w0 save_events saved m1 w1(proj1 C0)SAVE)as FSAVE.
  assert(H1:history before world(Some saved)m1 w1).
  { split;[exact C1|]. split.
    - eapply gateway_buffer_reference_transitive;[exact(proj1(proj2 C0))|exact(proj1 FSAVE)].
    - eapply gateway_native_reference_transitive;[exact(proj2(proj2 C0))|exact(proj2 FSAVE)]. }
  destruct(actual_saved_callback_sends backend ge(history before world(Some saved))(history_ambient before world(Some saved))
    temporaries size saved initial stream_block stream_offset data_block data_offset m1 w1 save_rest
    (Vint Int.zero)after next send_symbol H1
    ltac:(intros memory current CONTEXT;exact(gateway_read_stream_cells _ _ _ _ _ _ _ _(proj2(proj2(proj2(proj2(proj1 CONTEXT)))))))
    STREAM SENDING CURSOR DESCRIPTOR SEND_SYMBOL SEND_FUNCTION R0)
    as(p1 & send_events & send_rest & m2 & w2 & sent & m3 & w3 & E1 & Q1 & P1 & C2 & SENT & R1).
  destruct(actual_send_retained_context backend io native_private stable_readonly discipline thread_errno runtime ge
    stream_block stream_block data_block stream_offset stream_offset data_offset initial 0 size readonly PAYLOAD BOUND
    (Some saved)(transfer_chunk size)m2 w2 send_events sent m3 w3(proj1 C2)
    (proj1(transfer_chunk_bounds size ltac:(lia)))(proj2(transfer_chunk_bounds size ltac:(lia)))SENT)
    as(count & bytes & COUNT & SENT_VALUE & LENGTH & SEND_BYTES & NO_RECEIVE & LOAD & C3 & BUFFER & NATIVE).
  subst sent.
  assert(L3:loaded before world(Some saved)(Z.max 0 count)bytes m3 w3).
  { split;[split;[exact C3|]|exact LOAD]. split.
    - eapply gateway_buffer_reference_transitive;[exact(proj1(proj2 C2))|exact BUFFER].
    - eapply gateway_native_reference_transitive;[exact(proj2(proj2 C2))|exact NATIVE]. }
  assert(SPAN:0<=Z.max 0 count<=size)by(pose proof(transfer_chunk_bounds size ltac:(lia));lia).
  destruct(actual_sent_callback_reads_errno backend ge(loaded before world(Some saved)(Z.max 0 count)bytes)
    (loaded_ambient before world(Some saved)(Z.max 0 count)bytes SPAN)
    temporaries size saved(stream_descriptor initial)(Int64.repr count)m3 w3 send_rest(Vint Int.zero)after next errno_symbol
    L3 ERRNO_SYMBOL ERRNO_FUNCTION R1)
    as(p2 & errno_events & errno_rest & m4 & w4 & pointer & m5 & w5 & E2 & Q2 & P2 & C4 & ERRNO & R2).
  destruct(gateway_actual_sender_errno backend io native_private stable_readonly discipline thread_errno runtime ge
    stream_block stream_block data_block stream_offset stream_offset data_offset initial 0 size readonly PAYLOAD
    (Some saved)before world(Z.max 0 count)bytes m4 w4 errno_events pointer m5 w5 SPAN C4 ERRNO)
    as(ERRNO_POINTER & L5).
  destruct(actual_send_captures_errno backend ge temporaries size saved(stream_descriptor initial)(Int64.repr count)
    pointer m5 w5 errno_rest(Vint Int.zero)after next(loaded before world(Some saved)(Z.max 0 count)bytes)
    (loaded_ambient before world(Some saved)(Z.max 0 count)bytes SPAN)L5 R2)
    as(pc & capture_rest & mc & wc & number & EC & QC & PC & VALUE & CC & RC).
  destruct(actual_send_captured_callback_restores_thread backend ge(loaded before world(Some saved)(Z.max 0 count)bytes)
    (loaded_ambient before world(Some saved)(Z.max 0 count)bytes SPAN)
    temporaries size saved(stream_descriptor initial)(Int64.repr count)pointer number mc wc capture_rest
    (Vint Int.zero)after next restore_symbol CC SAVED_POINTER RESTORE_SYMBOL RESTORE_FUNCTION RC)
    as(p3 & restore_events & restore_rest & m6 & w6 & ignored & m7 & w7 & E3 & Q3 & P3 & C6 & RESTORED & R3).
  pose proof(gateway_actual_sender_restore backend io native_private stable_readonly discipline thread_errno runtime ge
    stream_block stream_block data_block stream_offset stream_offset data_offset initial 0 size readonly PAYLOAD
    saved before world(Z.max 0 count)bytes m6 w6 restore_events ignored m7 w7 SPAN C6 RESTORED)as L7.
  destruct(gateway_prefix_side_cut backend ge(loaded before world None(Z.max 0 count)bytes)
    (loaded_ambient before world None(Z.max 0 count)bytes SPAN)
    (State f_host_transfer transfer_after_restore transfer_iteration_cont empty_env
      (send_number_values temporaries size saved(stream_descriptor initial)(Int64.repr count)pointer number)m7)
    (Returnstate ignored(send_restore_cont temporaries size saved(stream_descriptor initial)(Int64.repr count)pointer number)m7)
    (actual_restored_send_prefix ge temporaries size saved(stream_descriptor initial)(Int64.repr count)pointer number ignored m7)
    m7 w7 restore_rest(Vint Int.zero)after next L7 R3)
    as(p4 & suffix & memory & current & E4 & Q4 & P4 & C8 & R4).
  cbn[gateway_replace_memory]in P4,R4.
  set(prefix:=(p0++save_events)++(p1++send_events)++(p2++errno_events)++pc++
    gateway_source E0::(p3++restore_events)++p4).
  exists prefix,suffix,memory,current,saved,count,bytes,pointer,number.
  split.
  - unfold prefix;rewrite E0S,E1,E2,EC,E3,E4;repeat(rewrite <-app_assoc;cbn[app]);reflexivity.
  - split.
    + unfold prefix;eapply gateway_steps_append.
      * eapply gateway_call_body_prefix with(continuation:=send_save_cont temporaries size);[reflexivity|exact P0|exact SAVE].
      * eapply gateway_steps_append.
        -- eapply gateway_call_body_prefix with(continuation:=send_transfer_cont temporaries size saved(stream_descriptor initial));
             [reflexivity|exact P1|exact SENT].
        -- eapply gateway_steps_append.
           ++ eapply gateway_call_body_prefix with(continuation:=send_errno_cont temporaries size saved(stream_descriptor initial)(Int64.repr count));
                [reflexivity|exact P2|exact ERRNO].
           ++ eapply gateway_steps_append;[exact PC|].
              econstructor;[apply gateway_internal;[exact I|apply step_set;exact VALUE]|].
              eapply gateway_steps_append.
              ** eapply gateway_call_body_prefix with(continuation:=send_restore_cont temporaries size saved(stream_descriptor initial)(Int64.repr count)pointer number);
                   [reflexivity|exact P3|exact RESTORED].
              ** exact P4.
    + split.
      * assert(B0:gateway_sent_bytes io(stream_descriptor initial)p0=[])by(apply gateway_quiet_sent_empty;exact Q0).
        assert(B1:gateway_sent_bytes io(stream_descriptor initial)p1=[])by(apply gateway_quiet_sent_empty;exact Q1).
        assert(B2:gateway_sent_bytes io(stream_descriptor initial)p2=[])by(apply gateway_quiet_sent_empty;exact Q2).
        assert(BC:gateway_sent_bytes io(stream_descriptor initial)pc=[])by(apply gateway_quiet_sent_empty;exact QC).
        assert(B3:gateway_sent_bytes io(stream_descriptor initial)p3=[])by(apply gateway_quiet_sent_empty;exact Q3).
        assert(B4:gateway_sent_bytes io(stream_descriptor initial)p4=[])by(apply gateway_quiet_sent_empty;exact Q4).
        assert(BSAVE:gateway_sent_bytes io(stream_descriptor initial)save_events=[]).
        { eapply gateway_actual_primitive_no_send with(input:=history before world None);
            [apply history_ambient| |exact C0|exact SAVE].
          intros available owner result changed future observed CONTEXT OPERATION.
          pose proof(gateway_save_thread_operation _ _ _ _ _ _ runtime available owner result changed future observed
            (proj1(proj1 CONTEXT))OPERATION)as POST;tauto. }
        assert(BERRNO:gateway_sent_bytes io(stream_descriptor initial)errno_events=[]).
        { eapply gateway_actual_primitive_no_send with(input:=loaded before world(Some saved)(Z.max 0 count)bytes);
            [apply loaded_ambient;exact SPAN| |exact C4|exact ERRNO].
          intros available owner result changed future observed CONTEXT OPERATION.
          destruct(gateway_errno_location_operation _ _ _ _ _ _ runtime(Some saved)available owner result changed future observed
            (proj1(proj1(proj1 CONTEXT)))OPERATION)as(object & offset & REST);tauto. }
        assert(BRESTORE:gateway_sent_bytes io(stream_descriptor initial)restore_events=[]).
        { eapply gateway_actual_primitive_no_send with(input:=loaded before world(Some saved)(Z.max 0 count)bytes);
            [apply loaded_ambient;exact SPAN| |exact C6|exact RESTORED].
          intros available owner result changed future observed CONTEXT OPERATION.
          pose proof(gateway_restore_thread_operation _ _ _ _ _ _ runtime saved available owner result changed future observed
            (proj1(proj1(proj1 CONTEXT)))OPERATION)as POST;tauto. }
        unfold prefix;repeat rewrite gateway_sent_bytes_append.
        rewrite B0,BSAVE,B1,SEND_BYTES,B2,BERRNO,BC;cbn[app].
        change(bytes++gateway_sent_bytes io(stream_descriptor initial)((p3++restore_events)++p4)=bytes).
        repeat rewrite gateway_sent_bytes_append;rewrite B3,BRESTORE,B4;cbn;apply app_nil_r.
      * split;[exact COUNT|]. split;[exact LENGTH|]. split;[exact C8|]. split.
        -- eapply actual_captured_errno_shape;exact VALUE.
        -- exact R4.
Qed.
End Iteration.
