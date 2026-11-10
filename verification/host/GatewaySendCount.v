(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: Complete outgoing source execution sends the requested byte count. *)
From Stdlib Require Import ZArith List Lia Arith.Wf_nat.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayOperations GatewayReadonly GatewayPrimitiveCalls
  GatewayRuntimeABI GatewayThreadRuntime GatewayReadContext GatewayReadWindow GatewayStreamInterface GatewayReadyInterface
  GatewayStreamLayout GatewayStreamRelations GatewayTransferSource GatewayTransferMath GatewayTransferClassification
  GatewayTransferErrno GatewayTransferRestore GatewayTransferProgress GatewayTransferRetry GatewayTransferLoop GatewayControlPaths
  GatewaySendSource GatewaySendReady GatewaySendIteration GatewaySendValues GatewaySendRestore GatewaySendErrno GatewaySendRuntime
  GatewaySendRetention.
Import ListNotations.
Open Scope Z_scope.

Section SendCount.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
  (native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
  (discipline:option val->mem->World->Prop)(thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).
Variable ge:Clight.genv.
Context(ready_source:gateway_ready_source_producer backend ge io native_private stable_readonly(discipline None)).
Context(ready_no_send:gateway_ready_no_data_send_source backend ge io native_private stable_readonly(discipline None)).
Variables stream_block data_block:Values.block.
Variable stream_offset:ptrofs.
Variable readonly:Values.block->Z->Prop.
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

Local Definition context(initial:gateway_stream_values)(offset:ptrofs)(size:Z):=gateway_read_context native_private stable_readonly discipline None
  stream_block stream_offset initial stream_block stream_offset 0 readonly.
Local Lemma context_ambient initial offset size:gateway_runtime_discipline backend(context initial offset size).
Proof. apply gateway_read_context_ambient with(io:=io)(thread_errno:=thread_errno);exact runtime. Qed.
Definition gateway_send_final initial memory current :Prop:=
  exists final offset size,context final offset size memory current /\gateway_stream_transport_after initial final.

Theorem actual_send_loop_count_bounded fuel :
  forall events,(length events<fuel)%nat ->
  forall temporaries initial offset size before world after next,
    0<=size<=Int64.max_unsigned ->
    (forall position,Ptrofs.unsigned offset<=position<Ptrofs.unsigned offset+size->readonly data_block position) ->
    Ptrofs.unsigned offset+size<=Ptrofs.modulus ->
    stream_descriptor initial<>stream_control initial ->
    gateway_send_locals temporaries(Vptr stream_block stream_offset)(Vptr data_block offset)size ->
    context initial offset size before world ->
    gateway_steps backend ge
      (gateway_live(State f_host_transfer transfer_loop transfer_loop_cont empty_env temporaries before)world)events
      (gateway_live(Returnstate(Vint Int.zero)Kstop after)next) ->
    Z.of_nat(length(gateway_sent_bytes io(stream_descriptor initial)events))=size /\
    gateway_send_final initial after next.
Proof.
  induction fuel as[|fuel IH];intros events LIMIT temporaries initial offset size before world after next
    SIZE PAYLOAD BOUND SEPARATE LOCALS CONTEXT RUN;[lia|].
  destruct(Z.eq_dec size 0)as[ZERO|POSITIVE].
  - subst size.
    destruct LOCALS as[STREAM[RECEIVE[CURSOR SIZE_LOOK]]].
    destruct(gateway_pure_path_ready_return backend ge(context initial offset 0)(context_ambient initial offset 0)
      (State f_host_transfer transfer_loop transfer_loop_cont empty_env temporaries before)(Vint Int.zero)
      world events(Vint Int.zero)after next(actual_zero_transfer_loop_path ge temporaries before SIZE_LOOK)CONTEXT RUN)
      as[VALUE[FINAL QUIET]].
    split;[rewrite(gateway_quiet_sent_empty io(stream_descriptor initial)events QUIET);reflexivity|].
    exists initial,offset,0;split;[exact FINAL|apply gateway_transport_refl].
  - assert(POS:0<size<=Int64.max_unsigned)by lia.
    destruct LOCALS as[STREAM[RECEIVE[CURSOR SIZE_LOOK]]].
    destruct(actual_positive_send_loop_ready_execution backend ge temporaries size stream_block stream_offset
      before world events after next(context initial offset size)(context_ambient initial offset size)ready_symbol
      CONTEXT POS SIZE_LOOK STREAM RECEIVE READY_SYMBOL READY_FUNCTION RUN)
      as(rprefix & readiness & caller & rm & rw & changed & changed_world & ER & QR & PR & CR & READINESS & RR).
    destruct CR as[SIDE[STREAM_PRIVATE[DATA_PRIVATE[IMMUTABLE INPUT]]]].
    pose proof(ready_no_send rm rw stream_block stream_offset initial stream_block stream_offset 0 readonly(Int.repr 4)
      readiness changed changed_world SIDE STREAM_PRIVATE DATA_PRIVATE IMMUTABLE INPUT SEPARATE
      ltac:(right;reflexivity)READINESS)as READY_SENT.
    destruct(ready_source rm rw stream_block stream_offset initial stream_block stream_offset 0 readonly(Int.repr 4)
      readiness changed changed_world SIDE STREAM_PRIVATE DATA_PRIVATE IMMUTABLE INPUT
      ltac:(right;reflexivity)READINESS)
      as(updated & UPDATED_INPUT & TRANSPORT & READY_FRAME & READY_BYTES & UPDATED_SIDE & UPDATED_STREAM & UPDATED_DATA &
        UPDATED_READONLY & STREAM_PERMISSIONS & NATIVE_ACCESS & STABLE_ACCESS).
    assert(UPDATED_CONTEXT:context updated offset size changed changed_world).
    { split;[exact UPDATED_SIDE|]. split;[exact UPDATED_STREAM|]. split;[exact UPDATED_DATA|].
      split;[exact UPDATED_READONLY|exact UPDATED_INPUT]. }
    destruct(actual_send_iteration_from_ready backend io native_private stable_readonly discipline thread_errno runtime ge
      stream_block data_block stream_offset offset updated size readonly PAYLOAD BOUND save_symbol send_symbol errno_symbol restore_symbol
      SAVE_SYMBOL SAVE_FUNCTION SEND_SYMBOL SEND_FUNCTION ERRNO_SYMBOL ERRNO_FUNCTION RESTORE_SYMBOL RESTORE_FUNCTION
      DESCRIPTOR temporaries changed changed_world caller after next POS SIZE_LOOK STREAM RECEIVE CURSOR UPDATED_CONTEXT RR)
      as(iprefix & isuffix & im & iw & saved & count & bytes & pointer & number & EI & PI & OBSERVED & COUNT & BYTES &
        ITER_CONTEXT & NUMBER_TYPE & RI).
    set(temps:=send_number_values temporaries size saved(stream_descriptor updated)(Int64.repr count)pointer number).
    assert(ITER_LOCALS:gateway_send_locals temps(Vptr stream_block stream_offset)(Vptr data_block offset)size).
    { apply gateway_send_number_locals;repeat split;assumption. }
    assert(COUNT_LOOK:temps!_count=Some(Vlong(Int64.repr count)))by(apply gateway_send_number_count).
    assert(NUMBER_LOOK:temps!_number=Some number)by(apply gateway_send_number_errno).
    assert(CHUNK_LOOK:temps!_amount=Some(Vlong(Int64.repr(transfer_chunk size))))by(apply gateway_send_number_chunk).
    pose proof(actual_successful_receive_iteration_classified backend ge temps count(transfer_chunk size)number im iw
      isuffix after next COUNT COUNT_LOOK NUMBER_LOOK NUMBER_TYPE RI)as CLASSIFIED.
    assert(NONEMPTY:(0<length iprefix)%nat).
    { destruct iprefix;[inversion PI|cbn;lia]. }
    assert(READY_PREFIX_BYTES:gateway_sent_bytes io(stream_descriptor initial)rprefix=[])
      by(apply gateway_quiet_sent_empty;exact QR).
    assert(ITER_BYTES:gateway_sent_bytes io(stream_descriptor initial)iprefix=bytes).
    { rewrite <-(gateway_transport_descriptor initial updated TRANSPORT);exact OBSERVED. }
    destruct ITER_CONTEXT as[[ITER_CONTEXT[BUFFER NATIVE]]INITIALIZED].
    destruct ITER_LOCALS as[ITER_STREAM[ITER_RECEIVE[ITER_CURSOR ITER_SIZE]]].
    destruct CLASSIFIED as[ADVANCE|[RETRY[integer[NUMBER RETRY_NUMBER]]]].
    + pose proof(transfer_chunk_bounds size ltac:(lia))as[CHUNK BELOW].
      destruct(Z.eq_dec count size)as[LAST|MORE].
      * destruct(gateway_pure_path_ready_return backend ge(context updated offset size)(context_ambient updated offset size)
          (State f_host_transfer transfer_after_restore transfer_iteration_cont empty_env temps im)(Vint Int.zero)
          iw isuffix(Vint Int.zero)after next
          (actual_positive_count_last_path ge temps size count data_block offset im POS ADVANCE ltac:(lia)
            COUNT_LOOK CHUNK_LOOK ITER_CURSOR ITER_SIZE)ITER_CONTEXT RI)
          as[VALUE[FINAL QUIET]].
        assert(REST_BYTES:gateway_sent_bytes io(stream_descriptor initial)isuffix=[])
          by(apply gateway_quiet_sent_empty;exact QUIET).
        split.
        -- rewrite ER,EI;repeat rewrite gateway_sent_bytes_append.
           rewrite READY_PREFIX_BYTES,READY_SENT,ITER_BYTES,REST_BYTES;cbn;rewrite app_nil_r,BYTES.
           subst count;rewrite Z.max_r by lia;reflexivity.
        -- exists updated,offset,size;split;assumption.
      * assert(PARTIAL:0<count<size)by lia.
        destruct(gateway_prefix_side_cut backend ge(context updated offset size)(context_ambient updated offset size)
          (State f_host_transfer transfer_loop transfer_loop_cont empty_env
            (transfer_advanced_values temps size count data_block offset)im)
          (State f_host_transfer transfer_after_restore transfer_iteration_cont empty_env temps im)
          (actual_positive_count_loop_prefix ge temps size count data_block offset im POS ADVANCE
            COUNT_LOOK CHUNK_LOOK ITER_CURSOR ITER_SIZE)im iw isuffix(Vint Int.zero)after next ITER_CONTEXT RI)
          as(aprefix & suffix & am & aw & EA & QA & PA & AC & RA).
        cbn[GatewayMachine.gateway_replace_memory]in PA,RA.
        assert(SMALLER:(length suffix<fuel)%nat).
        { rewrite ER,EI,EA in LIMIT;repeat rewrite length_app in LIMIT;lia. }
        destruct(IH suffix SMALLER(transfer_advanced_values temps size count data_block offset)updated
          (Ptrofs.add offset(Ptrofs.repr count))(size-count)am aw after next ltac:(lia)
          ltac:(intros position RANGE;apply PAYLOAD;
            rewrite(gateway_read_advanced_offset offset size count SIZE ltac:(lia)BOUND)in RANGE;lia)
          ltac:(rewrite(gateway_read_advanced_offset offset size count SIZE ltac:(lia)BOUND);lia)
          ltac:(unfold gateway_stream_transport_after in TRANSPORT;rewrite(proj1 TRANSPORT),(proj1(proj2 TRANSPORT));exact SEPARATE)
          (gateway_send_advanced_locals temps size count data_block offset(Vptr stream_block stream_offset)
            ltac:(repeat split;assumption))
          AC RA)as[REST_COUNT FINAL].
        rewrite(gateway_transport_descriptor initial updated TRANSPORT)in REST_COUNT.
        assert(ADVANCE_BYTES:gateway_sent_bytes io(stream_descriptor initial)aprefix=[])
          by(apply gateway_quiet_sent_empty;exact QA).
        split.
        -- rewrite ER,EI,EA;repeat rewrite gateway_sent_bytes_append.
           rewrite READY_PREFIX_BYTES,READY_SENT,ITER_BYTES,ADVANCE_BYTES;cbn.
           rewrite length_app,Nat2Z.inj_add,BYTES,REST_COUNT,Z.max_r by lia;lia.
        -- destruct FINAL as(final & final_offset & final_size & FINAL_CONTEXT & FINAL_TRANSPORT).
           exists final,final_offset,final_size;split;[exact FINAL_CONTEXT|].
           eapply gateway_transport_transitive;[exact TRANSPORT|exact FINAL_TRANSPORT].
    + subst count.
      destruct(gateway_prefix_side_cut backend ge(context updated offset size)(context_ambient updated offset size)
        (State f_host_transfer transfer_loop transfer_loop_cont empty_env(transfer_retry_values temps)im)
        (State f_host_transfer transfer_after_restore transfer_iteration_cont empty_env temps im)
        (actual_negative_retry_loop_prefix ge temps integer im COUNT_LOOK ltac:(rewrite NUMBER_LOOK,NUMBER;reflexivity)RETRY_NUMBER)
        im iw isuffix(Vint Int.zero)after next ITER_CONTEXT RI)
        as(aprefix & suffix & am & aw & EA & QA & PA & AC & RA).
      cbn[GatewayMachine.gateway_replace_memory]in PA,RA.
      assert(SMALLER:(length suffix<fuel)%nat).
      { rewrite ER,EI,EA in LIMIT;repeat rewrite length_app in LIMIT;lia. }
      destruct(IH suffix SMALLER(transfer_retry_values temps)updated offset size am aw after next SIZE PAYLOAD BOUND
        ltac:(unfold gateway_stream_transport_after in TRANSPORT;rewrite(proj1 TRANSPORT),(proj1(proj2 TRANSPORT));exact SEPARATE)
        (gateway_send_retried_locals temps(Vptr stream_block stream_offset)(Vptr data_block offset)size
          ltac:(repeat split;assumption))AC RA)as[REST_COUNT FINAL].
      rewrite(gateway_transport_descriptor initial updated TRANSPORT)in REST_COUNT.
      assert(ADVANCE_BYTES:gateway_sent_bytes io(stream_descriptor initial)aprefix=[])
        by(apply gateway_quiet_sent_empty;exact QA).
      split.
      * rewrite ER,EI,EA;repeat rewrite gateway_sent_bytes_append.
        rewrite READY_PREFIX_BYTES,READY_SENT,ITER_BYTES,ADVANCE_BYTES;cbn.
        rewrite length_app,Nat2Z.inj_add,BYTES,REST_COUNT;cbn;lia.
      * destruct FINAL as(final & final_offset & final_size & FINAL_CONTEXT & FINAL_TRANSPORT).
        exists final,final_offset,final_size;split;[exact FINAL_CONTEXT|].
        eapply gateway_transport_transitive;[exact TRANSPORT|exact FINAL_TRANSPORT].
Qed.

Theorem actual_send_loop_count events temporaries initial offset size before world after next :
  0<=size<=Int64.max_unsigned ->
  (forall position,Ptrofs.unsigned offset<=position<Ptrofs.unsigned offset+size->readonly data_block position) ->
  Ptrofs.unsigned offset+size<=Ptrofs.modulus ->stream_descriptor initial<>stream_control initial ->
  gateway_send_locals temporaries(Vptr stream_block stream_offset)(Vptr data_block offset)size ->
  context initial offset size before world ->
  gateway_steps backend ge
    (gateway_live(State f_host_transfer transfer_loop transfer_loop_cont empty_env temporaries before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next) ->
  Z.of_nat(length(gateway_sent_bytes io(stream_descriptor initial)events))=size /\
  gateway_send_final initial after next.
Proof. eapply actual_send_loop_count_bounded with(fuel:=S(length events));lia||eassumption. Qed.

Theorem actual_send_transfer_count events initial offset size before world after next :
  0<=size<=Int64.max_unsigned ->
  (forall position,Ptrofs.unsigned offset<=position<Ptrofs.unsigned offset+size->readonly data_block position) ->
  Ptrofs.unsigned offset+size<=Ptrofs.modulus ->stream_descriptor initial<>stream_control initial ->
  context initial offset size before world ->
  gateway_steps backend ge
    (gateway_live(Callstate(Internal f_host_transfer)
      [Vptr stream_block stream_offset;Vptr data_block offset;Vlong(Int64.repr size);Vint Int.one]Kstop before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next) ->
  Z.of_nat(length(gateway_sent_bytes io(stream_descriptor initial)events))=size /\
  gateway_send_final initial after next.
Proof.
  intros SIZE PAYLOAD BOUND SEPARATE CONTEXT RUN.
  destruct(gateway_prefix_side_cut backend ge(context initial offset size)(context_ambient initial offset size)
    (State f_host_transfer transfer_loop transfer_loop_cont empty_env
      (send_initial_values(Vptr stream_block stream_offset)(Vptr data_block offset)size)before)
    (Callstate(Internal f_host_transfer)
      [Vptr stream_block stream_offset;Vptr data_block offset;Vlong(Int64.repr size);Vint Int.one]Kstop before)
    (actual_transfer_direction_enters_loop ge(Vptr stream_block stream_offset)(Vptr data_block offset)size Int.one before)
    before world events(Vint Int.zero)after next CONTEXT RUN)
    as(prefix & suffix & memory & current & EVENTS & QUIET & PREFIX & CALLED & SUFFIX).
  cbn[GatewayMachine.gateway_replace_memory]in PREFIX,SUFFIX.
  destruct(actual_send_loop_count suffix
    (send_initial_values(Vptr stream_block stream_offset)(Vptr data_block offset)size)
    initial offset size memory current after next
    SIZE PAYLOAD BOUND SEPARATE
    (gateway_send_initial_locals(Vptr stream_block stream_offset)(Vptr data_block offset)size)CALLED SUFFIX)
    as[COUNT FINAL].
  split;[|exact FINAL]. rewrite EVENTS,gateway_sent_bytes_append,
    (gateway_quiet_sent_empty io(stream_descriptor initial)prefix QUIET);exact COUNT.
Qed.
End SendCount.
