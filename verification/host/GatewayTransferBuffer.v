(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: Actual receives assemble the exact retained parser input buffer. *)
From Stdlib Require Import ZArith List Lia Arith.Wf_nat.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayOperations GatewayReadonly GatewayPrimitiveCalls
  GatewayRuntimeABI GatewayThreadRuntime GatewayReadContext GatewayReadWindow GatewayStreamInterface GatewayReadyInterface
  GatewayStreamLayout GatewayStreamRelations GatewayTransferSource GatewayTransferMath GatewayTransferReady
  GatewayTransferIteration GatewayTransferClassification GatewayTransferValues GatewayTransferRestore
  GatewayTransferErrno GatewayTransferProgress GatewayTransferRetry GatewayTransferLoop GatewayControlPaths
  GatewayPrefixBuffer GatewayPrefixContext GatewayBufferReference GatewayTransportFrame GatewayTransferState
  GatewayReadMemory.
Import ListNotations.
Open Scope Z_scope.

Section LoopBuffer.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
  (native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
  (discipline:option val->mem->World->Prop)(thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).
Variable ge:Clight.genv.
Context(ready_source:gateway_ready_source_producer backend ge io native_private stable_readonly(discipline None)).
Variables stream_block data_block:Values.block.
Variable stream_offset:ptrofs.
Variable readonly:Values.block->Z->Prop.
Variable base:ptrofs.
Variables ready_symbol save_symbol receive_symbol errno_symbol restore_symbol:Values.block.
Hypotheses
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
  (DESCRIPTOR:stream_member_layout ge _descriptor 0).

Local Definition written(prefix:list Byte.int):Z:=Z.of_nat(length prefix).
Local Definition protected prefix:=gateway_prefix_readonly readonly data_block base(written prefix).
Local Definition context initial offset size prefix:=gateway_read_context native_private stable_readonly discipline None
  stream_block stream_offset initial data_block offset size(protected prefix).
Local Definition framed reference owner initial offset size kept loaded:=
  gateway_prefix_context native_private stable_readonly discipline stream_block data_block stream_offset offset
    initial size(protected kept)reference owner None base(written loaded)loaded.
Local Lemma framed_ambient reference owner initial offset size kept loaded:
  gateway_runtime_discipline backend(framed reference owner initial offset size kept loaded).
Proof. apply gateway_prefix_context_ambient with(io:=io)(thread_errno:=thread_errno);exact runtime. Qed.

Definition gateway_buffer_result initial prefix size before world events after next :Prop:=
  exists bytes,Z.of_nat(length bytes)=size /\gateway_received_bytes io(stream_descriptor initial)events=bytes /\
    Mem.loadbytes after data_block(Ptrofs.unsigned base)(written prefix+size)=Some(inj_bytes(prefix++bytes)) /\
    gateway_transfer_state native_private stable_readonly discipline stream_block stream_offset data_block readonly
      initial after next /\
    gateway_transport_frame native_private readonly stream_block stream_offset data_block base(written prefix+size)
      before world after next.

Theorem actual_receive_loop_buffer_bounded fuel :
  forall events,(length events<fuel)%nat ->
  forall temporaries initial offset size prefix before world after next,
    0<=size<=Int64.max_unsigned ->
    gateway_transfer_locals temporaries(Vptr stream_block stream_offset)(Vptr data_block offset)size ->
    context initial offset size prefix before world ->
    Ptrofs.unsigned offset=Ptrofs.unsigned base+written prefix ->
    gateway_whole_data_separate stream_block stream_offset data_block base(written prefix+size) ->
    Mem.loadbytes before data_block(Ptrofs.unsigned base)(written prefix)=Some(inj_bytes prefix) ->
    gateway_steps backend ge
      (gateway_live(State f_host_transfer transfer_loop transfer_loop_cont empty_env temporaries before)world)events
      (gateway_live(Returnstate(Vint Int.zero)Kstop after)next) ->
    gateway_buffer_result initial prefix size before world events after next.
Proof.
  induction fuel as[|fuel IH];intros events LIMIT temporaries initial offset size prefix before world after next
    SIZE LOCALS CONTEXT OFFSET WHOLE LOAD RUN;[lia|].
  assert(FRAMED:framed before world initial offset size prefix prefix before world).
  { split;[split;[exact CONTEXT|split;[apply gateway_buffer_reference_refl|apply gateway_native_reference_refl]]|exact LOAD]. }
  destruct(Z.eq_dec size 0)as[ZERO|POSITIVE].
  - subst size;destruct LOCALS as[STREAM[RECEIVE[CURSOR SIZE_LOOK]]].
    destruct(gateway_pure_path_ready_return backend ge(framed before world initial offset 0 prefix prefix)
      (framed_ambient before world initial offset 0 prefix prefix)
      (State f_host_transfer transfer_loop transfer_loop_cont empty_env temporaries before)(Vint Int.zero)
      world events(Vint Int.zero)after next(actual_zero_transfer_loop_path ge temporaries before SIZE_LOOK)FRAMED RUN)
      as[VALUE[FINAL QUIET]].
    destruct FINAL as[[FINAL_CONTEXT[BUFFER NATIVE]]FINAL_LOAD].
    exists[];split;[reflexivity|]. split;[apply gateway_quiet_received_empty;exact QUIET|]. split.
    + rewrite Z.add_0_r,app_nil_r;exact FINAL_LOAD.
    + split.
      * eapply gateway_transfer_state_from_context;[exact FINAL_CONTEXT| |apply gateway_transport_refl].
        intros object position HERE;left;exact HERE.
      * eapply gateway_transport_frame_buffers;[|exact BUFFER|exact NATIVE].
        intros object position HERE;left;exact HERE.
  - assert(POS:0<size<=Int64.max_unsigned)by lia.
    destruct LOCALS as[STREAM[RECEIVE[CURSOR SIZE_LOOK]]].
    destruct(actual_positive_loop_ready_execution backend ge temporaries size stream_block stream_offset
      before world events after next(framed before world initial offset size prefix prefix)
      (framed_ambient before world initial offset size prefix prefix)ready_symbol FRAMED POS SIZE_LOOK STREAM RECEIVE
      READY_SYMBOL READY_FUNCTION RUN)
      as(rprefix & readiness & caller & rm & rw & changed & changed_world & ER & QR & PR & CR & READINESS & RR).
    destruct CR as[[READY_CONTEXT[READY_BUFFER READY_NATIVE]]READY_LOAD].
    destruct READY_CONTEXT as[SIDE[STREAM_PRIVATE[DATA_PRIVATE[IMMUTABLE INPUT]]]].
    assert(F0:gateway_transport_frame native_private readonly stream_block stream_offset data_block base(written prefix+size)
      before world rm rw).
    { eapply gateway_transport_frame_buffers;[|exact READY_BUFFER|exact READY_NATIVE].
      intros object position HERE;left;exact HERE. }
    destruct(ready_source rm rw stream_block stream_offset initial data_block offset size(protected prefix)Int.one
      readiness changed changed_world SIDE STREAM_PRIVATE DATA_PRIVATE IMMUTABLE INPUT ltac:(left;reflexivity)READINESS)
      as(updated & UPDATED_INPUT & TRANSPORT & READY_FRAME & READY_BYTES & UPDATED_SIDE & UPDATED_STREAM & UPDATED_DATA &
        UPDATED_READONLY & STREAM_PERMISSIONS & NATIVE_ACCESS & STABLE_ACCESS).
    assert(UPDATED_CONTEXT:context updated offset size prefix changed changed_world).
    { split;[exact UPDATED_SIDE|]. split;[exact UPDATED_STREAM|]. split;[exact UPDATED_DATA|].
      split;[exact UPDATED_READONLY|exact UPDATED_INPUT]. }
    assert(FR:gateway_transport_frame native_private readonly stream_block stream_offset data_block base(written prefix+size)
      rm rw changed changed_world).
    { constructor.
      - eapply Mem.unchanged_on_implies;[exact READY_FRAME|]. intros object position HERE LIVE;left;left;exact HERE.
      - exact STREAM_PERMISSIONS.
      - eapply gateway_ready_total_data_permissions;[exact INPUT|unfold written;lia|exact OFFSET|exact READY_FRAME].
      - intros object LIVE PRIVATE;split.
        + eapply Mem.valid_block_unchanged_on;[exact READY_FRAME|exact LIVE].
        + apply NATIVE_ACCESS;assumption. }
    assert(UPDATED_LOAD:Mem.loadbytes changed data_block(Ptrofs.unsigned base)(written prefix)=Some(inj_bytes prefix)).
    { eapply Mem.loadbytes_unchanged_on;[exact READY_FRAME| |exact READY_LOAD].
      intros position RANGE;left;right;split;[reflexivity|exact RANGE]. }
    destruct(actual_receive_iteration_from_ready_readonly backend io native_private stable_readonly discipline thread_errno runtime ge
      stream_block data_block stream_offset offset updated size(protected prefix)save_symbol receive_symbol errno_symbol restore_symbol
      SAVE_SYMBOL SAVE_FUNCTION RECEIVE_SYMBOL RECEIVE_FUNCTION ERRNO_SYMBOL ERRNO_FUNCTION RESTORE_SYMBOL RESTORE_FUNCTION DESCRIPTOR
      temporaries changed changed_world caller after next POS SIZE_LOOK STREAM RECEIVE CURSOR UPDATED_CONTEXT RR)
      as(iprefix & isuffix & im & iw & saved & count & bytes & pointer & number & EI & PI & OBSERVED & COUNT & BYTES &
        ITER_CONTEXT & ITER_FRAME & ITER_PERMISSIONS & ITER_NATIVE & NUMBER_TYPE & RI).
    destruct ITER_CONTEXT as[ITER_CONTEXT INITIALIZED].
    assert(FI:gateway_transport_frame native_private readonly stream_block stream_offset data_block base(written prefix+size)
      changed changed_world im iw).
    { eapply gateway_transport_frame_buffers;[|split;[exact ITER_FRAME|exact ITER_PERMISSIONS]|exact ITER_NATIVE].
      intros object position HERE;left;exact HERE. }
    assert(PREFIX_RETAINED:Mem.loadbytes im data_block(Ptrofs.unsigned base)(written prefix)=Some(inj_bytes prefix)).
    { eapply Mem.loadbytes_unchanged_on;[exact ITER_FRAME| |exact UPDATED_LOAD].
      intros position RANGE;right;split;[reflexivity|exact RANGE]. }
    assert(COMBINED:Mem.loadbytes im data_block(Ptrofs.unsigned base)(written prefix+Z.max 0 count)=
      Some(inj_bytes(prefix++bytes))).
    { eapply gateway_loaded_prefix_append;[unfold written;lia|lia|exact OFFSET|exact PREFIX_RETAINED|exact INITIALIZED]. }
    assert(COMBINED_SIZE:written(prefix++bytes)=written prefix+Z.max 0 count).
    { unfold written;rewrite length_app,Nat2Z.inj_add,BYTES;reflexivity. }
    assert(AFTER_ITERATION:framed im iw updated offset size prefix(prefix++bytes)im iw).
    { split;[split;[exact ITER_CONTEXT|split;[apply gateway_buffer_reference_refl|apply gateway_native_reference_refl]]|].
      rewrite COMBINED_SIZE;exact COMBINED. }
    set(temps:=transfer_number_values temporaries size saved(stream_descriptor updated)(Int64.repr count)pointer number).
    assert(ITER_LOCALS:gateway_transfer_locals temps(Vptr stream_block stream_offset)(Vptr data_block offset)size).
    { apply gateway_transfer_number_locals;repeat split;assumption. }
    assert(COUNT_LOOK:temps!_count=Some(Vlong(Int64.repr count)))by(apply gateway_transfer_number_count).
    assert(NUMBER_LOOK:temps!_number=Some number)by(apply gateway_transfer_number_errno).
    assert(CHUNK_LOOK:temps!_amount=Some(Vlong(Int64.repr(transfer_chunk size))))by(apply gateway_transfer_number_chunk).
    pose proof(actual_successful_receive_iteration_classified backend ge temps count(transfer_chunk size)number im iw isuffix
      after next COUNT COUNT_LOOK NUMBER_LOOK NUMBER_TYPE RI)as CLASSIFIED.
    assert(NONEMPTY:(0<length iprefix)%nat)by(destruct iprefix;[inversion PI|cbn;lia]).
    assert(READY_PREFIX_BYTES:gateway_received_bytes io(stream_descriptor initial)rprefix=[])
      by(apply gateway_quiet_received_empty;exact QR).
    assert(ITER_BYTES:gateway_received_bytes io(stream_descriptor initial)iprefix=bytes).
    { rewrite <-(gateway_transport_descriptor initial updated TRANSPORT);exact OBSERVED. }
    destruct ITER_LOCALS as[ITER_STREAM[ITER_RECEIVE[ITER_CURSOR ITER_SIZE]]].
    destruct CLASSIFIED as[ADVANCE|[RETRY[integer[NUMBER RETRY_NUMBER]]]].
    + pose proof(transfer_chunk_bounds size ltac:(lia))as[CHUNK BELOW].
      destruct(Z.eq_dec count size)as[LAST|MORE].
      * destruct(gateway_pure_path_ready_return backend ge(framed im iw updated offset size prefix(prefix++bytes))
          (framed_ambient im iw updated offset size prefix(prefix++bytes))
          (State f_host_transfer transfer_after_restore transfer_iteration_cont empty_env temps im)(Vint Int.zero)
          iw isuffix(Vint Int.zero)after next
          (actual_positive_count_last_path ge temps size count data_block offset im POS ADVANCE ltac:(lia)
            COUNT_LOOK CHUNK_LOOK ITER_CURSOR ITER_SIZE)AFTER_ITERATION RI)
          as[VALUE[FINAL QUIET]].
        destruct FINAL as[[FINAL_CONTEXT[FINAL_BUFFER FINAL_NATIVE]]FINAL_LOAD].
        assert(FT:gateway_transport_frame native_private readonly stream_block stream_offset data_block base(written prefix+size)
          im iw after next).
        { eapply gateway_transport_frame_buffers;[|exact FINAL_BUFFER|exact FINAL_NATIVE].
          intros object position HERE;left;exact HERE. }
        exists bytes;split;[rewrite BYTES,Z.max_r by lia;exact LAST|]. split.
        -- rewrite ER,EI;repeat rewrite gateway_received_bytes_append.
           rewrite READY_PREFIX_BYTES,READY_BYTES,ITER_BYTES,(gateway_quiet_received_empty io(stream_descriptor initial)isuffix QUIET).
           cbn;apply app_nil_r.
        -- split.
           ++ replace(written prefix+size)with(written(prefix++bytes))by(rewrite COMBINED_SIZE,Z.max_r;lia).
              exact FINAL_LOAD.
           ++ split.
              ** eapply gateway_transfer_state_from_context;[exact FINAL_CONTEXT| |exact TRANSPORT].
                 intros object position HERE;left;exact HERE.
              ** eapply gateway_transport_frame_transitive;[exact F0|].
                 eapply gateway_transport_frame_transitive;[exact FR|].
                 eapply gateway_transport_frame_transitive;[exact FI|exact FT].
      * assert(PARTIAL:0<count<size)by lia.
        destruct(gateway_prefix_side_cut backend ge(framed im iw updated offset size prefix(prefix++bytes))
          (framed_ambient im iw updated offset size prefix(prefix++bytes))
          (State f_host_transfer transfer_loop transfer_loop_cont empty_env(transfer_advanced_values temps size count data_block offset)im)
          (State f_host_transfer transfer_after_restore transfer_iteration_cont empty_env temps im)
          (actual_positive_count_loop_prefix ge temps size count data_block offset im POS ADVANCE COUNT_LOOK CHUNK_LOOK ITER_CURSOR ITER_SIZE)
          im iw isuffix(Vint Int.zero)after next AFTER_ITERATION RI)
          as(aprefix & suffix & am & aw & EA & QA & PA & AC & RA).
        cbn[GatewayMachine.gateway_replace_memory]in PA,RA.
        destruct AC as[[AFTER_CONTEXT[ADVANCE_BUFFER ADVANCE_NATIVE]]ADVANCE_LOAD].
        assert(FA:gateway_transport_frame native_private readonly stream_block stream_offset data_block base(written prefix+size)
          im iw am aw).
        { eapply gateway_transport_frame_buffers;[|exact ADVANCE_BUFFER|exact ADVANCE_NATIVE].
          intros object position HERE;left;exact HERE. }
        assert(SMALLER:(length suffix<fuel)%nat).
        { rewrite ER,EI,EA in LIMIT;repeat rewrite length_app in LIMIT;lia. }
        assert(LENGTH_NEW:written(prefix++bytes)=written prefix+count)by(rewrite COMBINED_SIZE,Z.max_r;lia).
        assert(NEW_OFFSET:Ptrofs.unsigned(Ptrofs.add offset(Ptrofs.repr count))=Ptrofs.unsigned base+written(prefix++bytes)).
        { rewrite(gateway_read_advanced_offset offset size count SIZE ltac:(lia)
            (gateway_read_data_bounds _ _ _ _ _ _ _ _(proj2(proj2(proj2(proj2 AFTER_CONTEXT)))))),OFFSET,LENGTH_NEW;lia. }
        assert(NEW_WHOLE:gateway_whole_data_separate stream_block stream_offset data_block base
          (written(prefix++bytes)+(size-count))).
        { replace(written(prefix++bytes)+(size-count))with(written prefix+size)by(rewrite LENGTH_NEW;lia);exact WHOLE. }
        assert(NEW_CONTEXT:context updated(Ptrofs.add offset(Ptrofs.repr count))(size-count)(prefix++bytes)am aw).
        { eapply gateway_read_prefix_context with(backend:=backend)(io:=io)(thread_errno:=thread_errno);
            [exact runtime| |unfold written;lia|exact NEW_OFFSET|exact NEW_WHOLE|exact ADVANCE_LOAD].
          eapply gateway_read_restrict_context.
          - eapply gateway_read_advance_context;[exact AFTER_CONTEXT|exact PARTIAL].
          - intros object position HERE;left;exact HERE. }
        destruct(IH suffix SMALLER(transfer_advanced_values temps size count data_block offset)updated
          (Ptrofs.add offset(Ptrofs.repr count))(size-count)(prefix++bytes)am aw after next ltac:(lia)
          (gateway_transfer_advanced_locals temps size count data_block offset(Vptr stream_block stream_offset)
            ltac:(repeat split;assumption))NEW_CONTEXT NEW_OFFSET NEW_WHOLE ADVANCE_LOAD RA)
          as(tail & TAIL_LENGTH & TAIL_BYTES & TAIL_LOAD & TAIL_STATE & TAIL_FRAME).
        rewrite(gateway_transport_descriptor initial updated TRANSPORT)in TAIL_BYTES.
        replace(written(prefix++bytes)+(size-count))with(written prefix+size)in TAIL_FRAME,TAIL_LOAD
          by(rewrite LENGTH_NEW;lia).
        exists(bytes++tail);split.
        -- rewrite length_app,Nat2Z.inj_add,BYTES,TAIL_LENGTH,Z.max_r by lia;lia.
        -- split.
           ++ rewrite ER,EI,EA;repeat rewrite gateway_received_bytes_append.
              rewrite READY_PREFIX_BYTES,READY_BYTES,ITER_BYTES,
                (gateway_quiet_received_empty io(stream_descriptor initial)aprefix QA),TAIL_BYTES;reflexivity.
           ++ split.
              ** rewrite app_assoc;exact TAIL_LOAD.
              ** split;[eapply gateway_transfer_state_transport;[exact TRANSPORT|exact TAIL_STATE]|].
                 eapply gateway_transport_frame_transitive;[exact F0|].
                 eapply gateway_transport_frame_transitive;[exact FR|].
                 eapply gateway_transport_frame_transitive;[exact FI|].
                 eapply gateway_transport_frame_transitive;[exact FA|exact TAIL_FRAME].
    + subst count.
      assert(EMPTY:bytes=[]).
      { destruct bytes;[reflexivity|cbn in BYTES;lia]. }
      rewrite EMPTY,app_nil_r in AFTER_ITERATION.
      rewrite EMPTY in ITER_BYTES.
      destruct(gateway_prefix_side_cut backend ge(framed im iw updated offset size prefix prefix)
        (framed_ambient im iw updated offset size prefix prefix)
        (State f_host_transfer transfer_loop transfer_loop_cont empty_env(transfer_retry_values temps)im)
        (State f_host_transfer transfer_after_restore transfer_iteration_cont empty_env temps im)
        (actual_negative_retry_loop_prefix ge temps integer im COUNT_LOOK ltac:(rewrite NUMBER_LOOK,NUMBER;reflexivity)RETRY_NUMBER)
        im iw isuffix(Vint Int.zero)after next AFTER_ITERATION RI)
        as(aprefix & suffix & am & aw & EA & QA & PA & AC & RA).
      cbn[GatewayMachine.gateway_replace_memory]in PA,RA.
      destruct AC as[[AFTER_CONTEXT[ADVANCE_BUFFER ADVANCE_NATIVE]]ADVANCE_LOAD].
      assert(FA:gateway_transport_frame native_private readonly stream_block stream_offset data_block base(written prefix+size)
        im iw am aw).
      { eapply gateway_transport_frame_buffers;[|exact ADVANCE_BUFFER|exact ADVANCE_NATIVE].
        intros object position HERE;left;exact HERE. }
      assert(SMALLER:(length suffix<fuel)%nat).
      { rewrite ER,EI,EA in LIMIT;repeat rewrite length_app in LIMIT;lia. }
      destruct(IH suffix SMALLER(transfer_retry_values temps)updated offset size prefix am aw after next SIZE
        (gateway_transfer_retried_locals temps(Vptr stream_block stream_offset)(Vptr data_block offset)size
          ltac:(repeat split;assumption))AFTER_CONTEXT OFFSET WHOLE ADVANCE_LOAD RA)
        as(tail & TAIL_LENGTH & TAIL_BYTES & TAIL_LOAD & TAIL_STATE & TAIL_FRAME).
      rewrite(gateway_transport_descriptor initial updated TRANSPORT)in TAIL_BYTES.
      exists tail;split;[exact TAIL_LENGTH|]. split.
      * rewrite ER,EI,EA;repeat rewrite gateway_received_bytes_append.
        rewrite READY_PREFIX_BYTES,READY_BYTES,ITER_BYTES,
          (gateway_quiet_received_empty io(stream_descriptor initial)aprefix QA),TAIL_BYTES;reflexivity.
      * split;[exact TAIL_LOAD|]. split;[eapply gateway_transfer_state_transport;[exact TRANSPORT|exact TAIL_STATE]|].
        eapply gateway_transport_frame_transitive;[exact F0|].
        eapply gateway_transport_frame_transitive;[exact FR|].
        eapply gateway_transport_frame_transitive;[exact FI|].
        eapply gateway_transport_frame_transitive;[exact FA|exact TAIL_FRAME].
Qed.

Theorem actual_receive_loop_buffer events temporaries initial offset size prefix before world after next :
  0<=size<=Int64.max_unsigned ->
  gateway_transfer_locals temporaries(Vptr stream_block stream_offset)(Vptr data_block offset)size ->
  context initial offset size prefix before world ->
  Ptrofs.unsigned offset=Ptrofs.unsigned base+written prefix ->
  gateway_whole_data_separate stream_block stream_offset data_block base(written prefix+size) ->
  Mem.loadbytes before data_block(Ptrofs.unsigned base)(written prefix)=Some(inj_bytes prefix) ->
  gateway_steps backend ge
    (gateway_live(State f_host_transfer transfer_loop transfer_loop_cont empty_env temporaries before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next) ->
  gateway_buffer_result initial prefix size before world events after next.
Proof. eapply actual_receive_loop_buffer_bounded with(fuel:=S(length events));lia||eassumption. Qed.

Theorem actual_receive_transfer_buffer events initial size before world after next :
  gateway_read_context native_private stable_readonly discipline None stream_block stream_offset initial
    data_block base size readonly before world ->
  gateway_steps backend ge
    (gateway_live(Callstate(Internal f_host_transfer)
      [Vptr stream_block stream_offset;Vptr data_block base;Vlong(Int64.repr size);Vint Int.zero]Kstop before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next) ->
  exists bytes,Z.of_nat(length bytes)=size /\gateway_received_bytes io(stream_descriptor initial)events=bytes /\
    Mem.loadbytes after data_block(Ptrofs.unsigned base)size=Some(inj_bytes bytes) /\
    gateway_transfer_state native_private stable_readonly discipline stream_block stream_offset data_block readonly initial after next /\
    gateway_transport_frame native_private readonly stream_block stream_offset data_block base size before world after next.
Proof.
  intros CONTEXT RUN.
  pose proof(proj2(proj2(proj2(proj2 CONTEXT))))as INPUT.
  assert(WHOLE:gateway_whole_data_separate stream_block stream_offset data_block base size)
    by exact(gateway_read_data_separate _ _ _ _ _ _ _ _ INPUT).
  assert(EMPTY:Mem.loadbytes before data_block(Ptrofs.unsigned base)0=Some(inj_bytes[])).
  { apply Mem.loadbytes_empty;lia. }
  assert(EXTENDED:context initial base size[]before world).
  { eapply gateway_read_prefix_context with(backend:=backend)(io:=io)(thread_errno:=thread_errno);
      [exact runtime|exact CONTEXT|unfold written;cbn;lia|unfold written;cbn;lia|exact WHOLE|exact EMPTY]. }
  assert(FRAMED:framed before world initial base size[][]before world).
  { split;[split;[exact EXTENDED|split;[apply gateway_buffer_reference_refl|apply gateway_native_reference_refl]]|exact EMPTY]. }
  destruct(gateway_prefix_side_cut backend ge(framed before world initial base size[][])
    (framed_ambient before world initial base size[][])
    (State f_host_transfer transfer_loop transfer_loop_cont empty_env
      (transfer_loop_values(Vptr stream_block stream_offset)(Vptr data_block base)size)before)
    (Callstate(Internal f_host_transfer)
      [Vptr stream_block stream_offset;Vptr data_block base;Vlong(Int64.repr size);Vint Int.zero]Kstop before)
    (actual_receive_transfer_enters_loop ge(Vptr stream_block stream_offset)(Vptr data_block base)size before)
    before world events(Vint Int.zero)after next FRAMED RUN)
    as(prefix & suffix & memory & current & EVENTS & QUIET & PREFIX & CALLED & SUFFIX).
  cbn[GatewayMachine.gateway_replace_memory]in PREFIX,SUFFIX.
  destruct CALLED as[[CALLED[BUFFER NATIVE]]LOAD].
  assert(FIRST:gateway_transport_frame native_private readonly stream_block stream_offset data_block base size before world memory current).
  { eapply gateway_transport_frame_buffers;[|exact BUFFER|exact NATIVE]. intros object position HERE;left;exact HERE. }
  destruct(actual_receive_loop_buffer suffix
    (transfer_loop_values(Vptr stream_block stream_offset)(Vptr data_block base)size)initial base size[]memory current after next
    (gateway_read_amount _ _ _ _ _ _ _ _ INPUT)
    (gateway_transfer_initial_locals(Vptr stream_block stream_offset)(Vptr data_block base)size)
    CALLED ltac:(unfold written;cbn;lia)WHOLE LOAD SUFFIX)
    as(bytes & COUNT & OBSERVED & INITIALIZED & FINAL & FRAME).
  exists bytes;split;[exact COUNT|]. split.
  - rewrite EVENTS,gateway_received_bytes_append,(gateway_quiet_received_empty io(stream_descriptor initial)prefix QUIET);exact OBSERVED.
  - split;[exact INITIALIZED|]. split;[exact FINAL|].
    eapply gateway_transport_frame_transitive;[exact FIRST|exact FRAME].
Qed.
End LoopBuffer.
