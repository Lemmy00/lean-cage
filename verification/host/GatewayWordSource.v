(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The word reader consumes one actual read before decoding or storing. *)
From Stdlib Require Import ZArith Lia List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Globalenvs Ctypes Clight.
Require Import Machine.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayOperations GatewayReadonly
  GatewayCallPath GatewayReturns GatewayStreamInterface GatewayStreamWord GatewayReturnTypes
  GatewayWordContext GatewayWordInputs GatewayThreadRuntime.
From HostGateway Require Import GatewayWordReadReceipt GatewayWordRuntime GatewayFrames GatewayStreamMemory
  GatewayWordsMemory GatewayWordData GatewayWordReceipt GatewayImport GatewayPathEvents GatewayFramedRuntime.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Section WordSource.
Context {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
  (io:Event->option gateway_native_io)(native_private:World->block->Prop)
  (stable_readonly:World->block->Z->Prop)(discipline:option Values.val->Memory.mem->World->Prop)
  (thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).

Theorem gateway_word_actual_read_cut arguments before world events after next read_symbol
    stream_block stream_offset stream output output_offset readonly original :
  word_stream arguments=Vptr stream_block stream_offset ->
  word_output arguments=Vptr output output_offset ->
  Genv.find_symbol ge _host_read=Some read_symbol ->
  Genv.find_funct_ptr ge read_symbol=Some(Internal f_host_read) ->
  gateway_word_context native_private stable_readonly discipline
    stream_block stream_offset stream output output_offset readonly original before world ->
  gateway_steps backend ge
    (gateway_live(Callstate(Internal f_host_word)(gateway_word_values arguments)Kstop before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next) ->
  exists buffer prefix reading suffix read_before read_world read_after read_next,
    events=prefix++reading++suffix /\Int.unsigned(word_width arguments)<=8 /\
    gateway_steps backend ge
      (gateway_live(Callstate(Internal f_host_word)(gateway_word_values arguments)Kstop before)world)prefix
      (gateway_live(Callstate(Internal f_host_read)(gateway_word_read_arguments buffer arguments)
        (gateway_word_read_cont buffer arguments Kstop)read_before)read_world) /\
    gateway_word_scratch_context native_private stable_readonly discipline buffer
      stream_block stream_offset stream output output_offset readonly original read_before read_world /\
    gateway_steps backend ge
      (gateway_live(Callstate(Internal f_host_read)(gateway_word_read_arguments buffer arguments)Kstop read_before)read_world)
      reading(gateway_live(Returnstate(Vint Int.zero)Kstop read_after)read_next) /\
    gateway_steps backend ge
      (gateway_live(Returnstate(Vint Int.zero)(gateway_word_read_cont buffer arguments Kstop)read_after)read_next)
      suffix(gateway_live(Returnstate(Vint Int.zero)Kstop after)next) /\Forall gateway_quiet_event prefix.
Proof.
  intros STREAM OUTPUT SYMBOL FUNCTION INPUT RUN.
  pose proof(gateway_actual_word_width_bounded backend ge _ _ _ _ _ _ RUN)as WIDTH.
  destruct(gateway_actual_function_entry_side backend ge _
    (gateway_word_context_ambient backend io native_private stable_readonly discipline thread_errno runtime
      stream_block stream_offset stream output output_offset readonly original)
    f_host_word(gateway_word_values arguments)Kstop before world events(Vint Int.zero)Kstop after next INPUT RUN)
    as[entry_prefix[body_events[allocation_before[allocation_world[environment[temporaries[allocated
      [EVENTS[QUIET[PREFIX[ENTRY_SIDE[ENTRY BODY]]]]]]]]]]]].
  destruct(gateway_actual_word_entry ge allocation_before arguments environment temporaries allocated ENTRY)
    as[buffer[ENV[TEMPS[ALLOC[FRAME[FRESH FREEABLE]]]]]];subst environment temporaries.
  pose proof(gateway_word_context_alloc backend io native_private stable_readonly discipline thread_errno runtime
    allocation_before allocation_world allocated buffer stream_block stream_offset stream output output_offset readonly original
    ENTRY_SIDE ALLOC)as ALLOCATED_SIDE.
  destruct(gateway_retained_call_ready_cut backend ge _
    (gateway_word_scratch_context_ambient backend io native_private stable_readonly discipline thread_errno runtime
      buffer stream_block stream_offset stream output output_offset readonly original)
    (Internal f_host_read)(gateway_word_read_arguments buffer arguments)(gateway_word_read_cont buffer arguments Kstop)
    (State f_host_word(fn_body f_host_word)Kstop(gateway_word_environment buffer)
      (gateway_word_parameters arguments)allocated)allocation_world body_events(Vint Int.zero)after next
    (gateway_word_body_read_path_retained ge buffer arguments allocated Kstop read_symbol stream_block stream_offset
      WIDTH STREAM SYMBOL FUNCTION)ALLOCATED_SIDE BODY)
    as[body_prefix[read_tail[read_before[read_world[BODY_EVENTS[BODY_QUIET[CALL[READ_SIDE FROM_READ]]]]]]]].
  destruct(gateway_return_cut backend ge(Internal f_host_read)(gateway_word_read_arguments buffer arguments)
    (gateway_word_read_cont buffer arguments Kstop)read_before read_world read_tail
    (Returnstate(Vint Int.zero)Kstop after)next ltac:(cbn;exact I)ltac:(cbn;lia)FROM_READ)
    as[read_events[suffix[read_value[read_after[read_next[READ_EVENTS[READ_RUN READ_REST]]]]]]].
  pose proof(actual_host_read_return_type backend ge _ _ _ _ _ _ _ READ_RUN)as READ_TYPE.
  pose proof(gateway_word_successful_typed_read_result backend ge buffer arguments read_after read_next
    suffix read_value after next READ_TYPE READ_REST)as ZERO;subst read_value.
  exists buffer,(entry_prefix++gateway_source E0::body_prefix),read_events,suffix,
    read_before,read_world,read_after,read_next.
  split;[rewrite EVENTS,BODY_EVENTS,READ_EVENTS;repeat rewrite<-app_assoc;reflexivity|].
  split;[exact WIDTH|]. split.
  - eapply gateway_steps_append;[exact PREFIX|].
    econstructor;[apply gateway_internal;[exact I|apply step_internal_function;exact ENTRY]|exact CALL].
  - split;[exact READ_SIDE|]. split;[exact READ_RUN|]. split;[exact READ_REST|].
    apply Forall_app;split;[exact QUIET|]. constructor;[left;reflexivity|exact BODY_QUIET].
Qed.

Theorem gateway_word_actual_read_receipt
    (read_source:gateway_read_source_producer backend ge io native_private stable_readonly(discipline None))
    arguments before world events after next read_symbol stream_block stream_offset stream
    output output_offset readonly original :
  word_stream arguments=Vptr stream_block stream_offset ->
  word_output arguments=Vptr output output_offset ->
  Genv.find_symbol ge _host_read=Some read_symbol ->
  Genv.find_funct_ptr ge read_symbol=Some(Internal f_host_read) ->
  gateway_word_context native_private stable_readonly discipline
    stream_block stream_offset stream output output_offset readonly original before world ->
  gateway_steps backend ge
    (gateway_live(Callstate(Internal f_host_word)(gateway_word_values arguments)Kstop before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next) ->
  exists buffer prefix reading suffix read_before read_world read_after read_next bytes,
    events=prefix++reading++suffix /\Int.unsigned(word_width arguments)<=8 /\
    gateway_steps backend ge
      (gateway_live(Callstate(Internal f_host_word)(gateway_word_values arguments)Kstop before)world)prefix
      (gateway_live(Callstate(Internal f_host_read)(gateway_word_read_arguments buffer arguments)
        (gateway_word_read_cont buffer arguments Kstop)read_before)read_world) /\
    gateway_word_scratch_context native_private stable_readonly discipline buffer
      stream_block stream_offset stream output output_offset readonly original read_before read_world /\
    gateway_read_receipt io read_before stream_block stream_offset stream buffer Ptrofs.zero
      (Int.unsigned(word_width arguments))
      (gateway_word_scratch_readonly buffer(Int.unsigned(word_width arguments))output output_offset readonly)
      reading read_after bytes /\
    discipline None read_after read_next /\native_private read_next stream_block /\native_private read_next buffer /\
    (forall object position,
      gateway_word_scratch_readonly buffer(Int.unsigned(word_width arguments))output output_offset readonly object position ->
      stable_readonly read_next object position) /\
    gateway_access_retained native_private stable_readonly read_before read_world read_next /\
    gateway_steps backend ge
      (gateway_live(Returnstate(Vint Int.zero)(gateway_word_read_cont buffer arguments Kstop)read_after)read_next)
      suffix(gateway_live(Returnstate(Vint Int.zero)Kstop after)next) /\Forall gateway_quiet_event prefix.
Proof.
  intros STREAM OUTPUT SYMBOL FUNCTION INPUT RUN.
  destruct(gateway_word_actual_read_cut arguments before world events after next read_symbol
    stream_block stream_offset stream output output_offset readonly original STREAM OUTPUT SYMBOL FUNCTION INPUT RUN)
    as(buffer &prefix &reading &suffix &read_before &read_world &read_after &read_next &
      EVENTS &WIDTH &PREFIX &READ_SIDE &READ_RUN &REST &PREFIX_QUIET).
  pose proof READ_SIDE as READ_SIDE_COPY.
  destruct READ_SIDE_COPY as[CALL_SIDE[BUFFER_PRIVATE[FREEABLE[SEPARATE[OUTSIDE AVOIDS]]]]].
  destruct CALL_SIDE as[SIDE[STREAM_PRIVATE[OUTPUT_PRIVATE[READONLY[RAW INITIAL_FRAME]]]]].
  assert(READ_INPUT:gateway_read_inputs read_before stream_block stream_offset stream buffer Ptrofs.zero
    (Int.unsigned(word_width arguments))
    (gateway_word_scratch_readonly buffer(Int.unsigned(word_width arguments))output output_offset readonly)).
  { eapply gateway_word_scratch_read_inputs;try eassumption.
    split;[pose proof(Int.unsigned_range(word_width arguments));lia|exact WIDTH]. }
  assert(STABLE:forall object position,
    gateway_word_scratch_readonly buffer(Int.unsigned(word_width arguments))output output_offset readonly object position ->
    stable_readonly read_world object position).
  { eapply gateway_word_readonly_stable;[exact runtime|exact READ_SIDE]. }
  unfold gateway_word_read_arguments in READ_RUN;rewrite STREAM in READ_RUN.
  destruct(read_source read_before read_world stream_block stream_offset stream buffer Ptrofs.zero
    (Int.unsigned(word_width arguments))
    (gateway_word_scratch_readonly buffer(Int.unsigned(word_width arguments))output output_offset readonly)
    reading read_after read_next SIDE STREAM_PRIVATE BUFFER_PRIVATE STABLE READ_INPUT READ_RUN)
    as[bytes[RECEIPT[AFTER_SIDE[STREAM_AFTER[BUFFER_AFTER[STABLE_AFTER[RETAIN_NATIVE RETAIN_STABLE]]]]]]].
  exists buffer,prefix,reading,suffix,read_before,read_world,read_after,read_next,bytes.
  split;[exact EVENTS|]. split;[exact WIDTH|]. split;[exact PREFIX|]. split;[exact READ_SIDE|].
  split;[exact RECEIPT|]. split;[exact AFTER_SIDE|]. split;[exact STREAM_AFTER|]. split;[exact BUFFER_AFTER|].
  split;[exact STABLE_AFTER|]. split;[split;assumption|]. split;assumption.
Qed.

(* §FS-host-boundary.caller: Successful decoding uses the same bytes received by
   the actual nested read, and preserves the stream for subsequent parser calls. *)
Theorem gateway_word_actual_decode
    (read_source:gateway_read_source_producer backend ge io native_private stable_readonly(discipline None))
    arguments before world events after next read_symbol get_symbol stream_block stream_offset stream
    output output_offset readonly original :
  word_stream arguments=Vptr stream_block stream_offset ->word_output arguments=Vptr output output_offset ->
  Genv.find_symbol ge _host_read=Some read_symbol ->
  Genv.find_funct_ptr ge read_symbol=Some(Internal f_host_read) ->
  Genv.find_symbol ge _host_get64=Some get_symbol ->
  Genv.find_funct_ptr ge get_symbol=Some(Internal f_host_get64) ->
  gateway_word_context native_private stable_readonly discipline
    stream_block stream_offset stream output output_offset readonly original before world ->
  gateway_steps backend ge
    (gateway_live(Callstate(Internal f_host_word)(gateway_word_values arguments)Kstop before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next) ->
  exists prefix reading suffix bytes final_stream,
    events=prefix++reading++suffix /\Int.unsigned(word_width arguments)<=8 /\
    Z.of_nat(length bytes)=Int.unsigned(word_width arguments) /\
    gateway_received_bytes io(stream_descriptor stream)reading=bytes /\
    gateway_received_bytes io(stream_descriptor stream)events=bytes /\
    Mem.loadv Mint64 after(Vptr output output_offset)=Some
      (Vlong(Int64.repr(Z.of_nat(nat_of_Nat(LeanCage_Host_GatewayWords_decode
        (gateway_imported_nats(gateway_byte_naturals bytes))))))) /\
    gateway_stream_memory after stream_block stream_offset final_stream /\
    gateway_stream_read_after stream(Int.unsigned(word_width arguments))final_stream /\
    discipline None after next /\native_private next stream_block /\native_private next output /\
    Mem.unchanged_on readonly original after.
Proof.
  intros STREAM OUTPUT READ_SYMBOL READ_FUNCTION GET_SYMBOL GET_FUNCTION INPUT RUN.
  destruct(gateway_word_actual_read_receipt read_source arguments before world events after next read_symbol
    stream_block stream_offset stream output output_offset readonly original
    STREAM OUTPUT READ_SYMBOL READ_FUNCTION INPUT RUN)
    as(buffer &prefix &reading &suffix &read_before &read_world &read_after &read_next &bytes &
      EVENTS &WIDTH &PREFIX &READ_SIDE &RECEIPT &SIDE_AFTER &STREAM_AFTER &BUFFER_AFTER &STABLE_AFTER &RETAINED &REST &PREFIX_QUIET).
  assert(WIDTH_RANGE:0<=Int.unsigned(word_width arguments)<=8).
  { split;[pose proof(Int.unsigned_range(word_width arguments));lia|exact WIDTH]. }
  pose proof(gateway_word_after_read_ready io native_private stable_readonly discipline
    buffer stream_block stream_offset stream output output_offset readonly original read_before read_world
    (Int.unsigned(word_width arguments))reading read_after read_next bytes READ_SIDE WIDTH_RANGE RECEIPT
    SIDE_AFTER STREAM_AFTER BUFFER_AFTER STABLE_AFTER RETAINED)as READY.
  pose proof RECEIPT as RECEIPT_COPY.
  destruct RECEIPT_COPY as[COUNT FITS OBSERVED LOADED DATA_PERMS STREAM_PERMS[final_stream[FINAL_STREAM READ_AFTER]]FRAME].
  assert(BYTE_WIDTH:(length bytes<=8)%nat)by lia.
  assert(INITIALIZED:Mem.loadbytes read_after buffer 0(Z.of_nat(length bytes))=Some(inj_bytes bytes)).
  { rewrite COUNT;exact LOADED. }
  set(post_readonly:=gateway_word_post_readonly stream_block stream_offset readonly).
  set(post_side:=gateway_word_stage native_private stable_readonly discipline None buffer output[stream_block]
    post_readonly read_after(gateway_word_store_ready buffer output(Ptrofs.unsigned output_offset))).
  destruct(gateway_word_actual_get_from_read_bytes_coupled backend ge post_side buffer arguments
    read_after read_next suffix after next bytes get_symbol
    (gateway_word_stage_get_contract backend io native_private stable_readonly discipline thread_errno runtime
      stream_block stream_offset readonly read_after buffer output output_offset(length bytes))
    READY BYTE_WIDTH ltac:(symmetry;exact COUNT)INITIALIZED GET_SYMBOL GET_FUNCTION REST)
    as(middle &get_events &last &get_before &get_world &get_after &get_next &
      GET_EVENTS &TO_GET &GET_RUN &LAST &GET_BEFORE_SIDE &GET_AFTER_SIDE &MIDDLE_QUIET).
  destruct READ_SIDE as[CALL_SIDE[BUFFER[FREEABLE[SEPARATE[OUTSIDE AVOIDS]]]]].
  destruct CALL_SIDE as[CALL_READY[STREAM_PRIVATE[OUTPUT_PRIVATE[READONLY[RAW INITIAL_FRAME]]]]].
  destruct RAW as[RAW ALIGNED].
  destruct GET_AFTER_SIDE as[GET_RESOURCES GET_READY].
  pose proof(gateway_word_runtime_store_path backend ge io native_private stable_readonly discipline thread_errno runtime
    None buffer arguments output output_offset
    (Int64.repr(Z.of_nat(nat_of_Nat(LeanCage_Host_GatewayWords_decode
      (gateway_imported_nats(gateway_byte_naturals bytes))))))[stream_block]
    read_after post_readonly get_after OUTPUT ltac:(congruence)
    (gateway_read_data_bounds _ _ _ _ _ _ _ _ RAW)
    (gateway_word_post_readonly_output stream_block stream_offset output output_offset readonly read_before stream
      ltac:(split;assumption))
    (gateway_word_post_readonly_scratch buffer stream_block stream_offset readonly SEPARATE AVOIDS))as STORE_SCRIPT.
  pose proof(gateway_runtime_path_events backend ge post_side
    (Returnstate(Vlong(Int64.repr(Z.of_nat(nat_of_Nat(LeanCage_Host_GatewayWords_decode
      (gateway_imported_nats(gateway_byte_naturals bytes)))))))(gateway_word_get_cont buffer arguments)get_after)
    _ _ get_next last(Vint Int.zero)after next
    (conj GET_RESOURCES GET_READY)STORE_SCRIPT LAST)as LAST_QUIET.
  pose proof(gateway_readonly_run_events backend ge _ get_world get_events _ get_after get_next
    (gateway_actual_get64_readonly _ _)GET_RUN)as GET_QUIET.
  assert(SUFFIX_QUIET:Forall gateway_quiet_event suffix).
  { rewrite GET_EVENTS;apply Forall_app;split;[exact MIDDLE_QUIET|].
    apply Forall_app;split;assumption. }
  assert(WHOLE_RECEIVED:gateway_received_bytes io(stream_descriptor stream)events=bytes).
  { rewrite EVENTS,!gateway_received_append.
    rewrite(gateway_quiet_received io _ _ PREFIX_QUIET),(gateway_quiet_received io _ _ SUFFIX_QUIET).
    cbn;rewrite app_nil_r;exact OBSERVED. }
  destruct(gateway_actual_word_stores_decoder_runtime backend ge io native_private stable_readonly discipline
    thread_errno runtime None buffer arguments output output_offset
    (Int64.repr(Z.of_nat(nat_of_Nat(LeanCage_Host_GatewayWords_decode
      (gateway_imported_nats(gateway_byte_naturals bytes))))))[stream_block]
    read_after post_readonly get_after get_next last after next OUTPUT ltac:(congruence)
    (gateway_read_data_bounds _ _ _ _ _ _ _ _ RAW)
    (gateway_word_post_readonly_output stream_block stream_offset output output_offset readonly read_before stream
      ltac:(split;assumption))
    (gateway_word_post_readonly_scratch buffer stream_block stream_offset readonly SEPARATE AVOIDS)
    GET_RESOURCES GET_READY LAST)as[FINAL_RESOURCES VALUE].
  destruct FINAL_RESOURCES as[FINAL_SIDE[FINAL_BUFFER[FINAL_OUTPUT[BUFFER_LIVE[OUTPUT_LIVE[HELD[OWNED FINAL_FRAME]]]]]]].
  assert(FINAL_STREAM_MEMORY:gateway_stream_memory after stream_block stream_offset final_stream).
  { eapply gateway_stream_memory_closed;[exact(gateway_read_stream_bounds _ _ _ _ _ _ _ _ RAW)|exact FINAL_STREAM|].
    eapply Mem.unchanged_on_implies;[exact FINAL_FRAME|intros;left;assumption]. }
  exists prefix,reading,suffix,bytes,final_stream.
  split;[exact EVENTS|]. split;[exact WIDTH|]. split;[exact COUNT|]. split;[exact OBSERVED|].
  split;[exact WHOLE_RECEIVED|].
  split;[exact VALUE|]. split;[exact FINAL_STREAM_MEMORY|]. split;[exact READ_AFTER|].
  split;[exact FINAL_SIDE|]. split;[exact(proj2(HELD stream_block ltac:(left;reflexivity)))|].
  split;[exact FINAL_OUTPUT|].
  eapply Mem.unchanged_on_trans;[exact INITIAL_FRAME|].
  eapply Mem.unchanged_on_trans.
  - eapply Mem.unchanged_on_implies;[exact FRAME|intros;left;assumption].
  - eapply Mem.unchanged_on_implies;[exact FINAL_FRAME|intros;right;assumption].
Qed.

End WordSource.
