(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The real value call reaches its actual first successful byte reader. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayReadonly GatewayFunctionEntry
  GatewayValueEntry GatewayValueGuards GatewayValueNodes GatewayValueTag GatewayValueWord GatewayValueContext
  GatewayValueNodeMemory GatewayStreamInterface GatewayStreamLayout GatewayStreamWord GatewaySourcePaths
  GatewaySourceCuts GatewayThreadRuntime GatewayFramedRuntime GatewayFailurePaths.
Import ListNotations.
Open Scope Z_scope.

Section ValueFirstWord.
Context {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
  (io:Event->option gateway_native_io)(native:World->block->Prop)(stable:World->block->Z->Prop)
  (discipline:option val->mem->World->Prop)(thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native stable discipline thread_errno).

Theorem gateway_actual_value_first_word arguments before world events value after next
    stream_block stream_offset initial readonly original symbol :
  gateway_value_stream arguments=Vptr stream_block stream_offset ->stream_member_layout ge _nodes 32 ->
  Genv.find_symbol ge _host_word=Some symbol ->Genv.find_funct_ptr ge symbol=Some(Internal f_host_word) ->
  gateway_value_context native stable discipline stream_block stream_offset initial readonly original before world ->
  gateway_steps backend ge
    (gateway_live(Callstate(Internal f_host_value)(gateway_value_arguments_list arguments)Kstop before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->
  exists slots prefix reading suffix word_before word_world word_after word_next,
    events=prefix++reading++suffix /\gateway_value_depth arguments<>Int.zero /\stream_nodes initial<>Int64.zero /\
    Forall(fun event=>event=gateway_source E0 \/event=gateway_ambient)prefix /\
    gateway_steps backend ge
      (gateway_live(Callstate(Internal f_host_value)(gateway_value_arguments_list arguments)Kstop before)world)prefix
      (gateway_live(Callstate(Internal f_host_word)(gateway_word_values(gateway_value_tag_arguments slots arguments))
        (gateway_value_tag_cont slots arguments initial)word_before)word_world) /\
    gateway_value_allocated native stable discipline slots stream_block stream_offset
      (gateway_stream_node_debit initial)readonly original word_before word_world /\
    gateway_steps backend ge
      (gateway_live(Callstate(Internal f_host_word)(gateway_word_values(gateway_value_tag_arguments slots arguments))
        Kstop word_before)word_world)reading
      (gateway_live(Returnstate(Vint Int.zero)Kstop word_after)word_next) /\
    gateway_steps backend ge
      (gateway_live(Returnstate(Vint Int.zero)(gateway_value_tag_cont slots arguments initial)word_after)word_next)
      suffix(gateway_live(Returnstate value Kstop after)next).
Proof.
  intros STREAM LAYOUT SYMBOL FUNCTION INPUT RUN NONNULL.
  assert(DEPTH:gateway_value_depth arguments<>Int.zero).
  { pose proof(gateway_actual_value_success_depth backend ge _ _ _ _ _ _ _ RUN NONNULL)as POSITIVE.
    intro ZERO;rewrite ZERO,Int.unsigned_zero in POSITIVE;lia. }
  destruct(gateway_actual_function_entry_side backend ge _
    (gateway_value_context_ambient backend io native stable discipline thread_errno runtime
      stream_block stream_offset initial readonly original)
    f_host_value(gateway_value_arguments_list arguments)Kstop before world events value Kstop after next INPUT RUN)
    as(entry_prefix &body_events &entry_memory &entry_world &environment &temporaries &allocated &
      EVENTS &QUIET &PREFIX &ENTRY_SIDE &ENTRY &BODY).
  destruct(gateway_actual_value_entry ge entry_memory arguments environment temporaries allocated ENTRY)
    as(slots &ENV &TEMPS &ALLOC &FRAME &ENTRY_REST);subst environment temporaries.
  pose proof(gateway_value_context_allocated backend io native stable discipline thread_errno runtime
    entry_memory entry_world allocated slots stream_block stream_offset initial readonly original ENTRY_SIDE ALLOC)
    as BODY_READY.
  assert(NODES:stream_nodes initial<>Int64.zero).
  { intro ZERO;apply NONNULL.
    eapply(gateway_value_zero_nodes_fails backend ge
      (gateway_value_allocated native stable discipline slots stream_block stream_offset initial readonly original)
      slots arguments allocated stream_block stream_offset).
    - eapply gateway_value_allocated_ambient;exact runtime.
    - exact DEPTH.
    - exact STREAM.
    - exact LAYOUT.
    - intros memory current GOOD;rewrite<-ZERO;eapply gateway_value_allocated_nodes;exact GOOD.
    - exact BODY_READY.
    - exact BODY. }
  pose proof(gateway_value_body_tag_path backend ge io native stable discipline thread_errno runtime
    slots arguments allocated stream_block stream_offset initial readonly original symbol
    DEPTH NODES STREAM LAYOUT SYMBOL FUNCTION)as TAG_PATH.
  destruct(gateway_source_path_cut backend ge _ _ _ _ _ _ TAG_PATH allocated entry_world body_events value after next
    BODY_READY BODY)
    as(body_prefix &word_tail &word_before &word_world &BODY_EVENTS &BODY_QUIET &TO_WORD &WORD_READY &FROM_WORD).
  destruct(gateway_return_cut backend ge(Internal f_host_word)
    (gateway_word_values(gateway_value_tag_arguments slots arguments))(gateway_value_tag_cont slots arguments initial)
    word_before word_world word_tail(Returnstate value Kstop after)next
    ltac:(cbn;exact I)ltac:(cbn;lia)FROM_WORD)
    as(reading &suffix &word_value &word_after &word_next &WORD_EVENTS &WORD_RUN &REST).
  assert(ZERO:word_value=Vint Int.zero).
  { eapply gateway_value_successful_tag_result.
    - eapply gateway_actual_word_return_type;exact WORD_RUN.
    - exact NONNULL.
    - exact REST. }
  subst word_value.
  exists slots,(entry_prefix++gateway_source E0::body_prefix),reading,suffix,
    word_before,word_world,word_after,word_next.
  split;[rewrite EVENTS,BODY_EVENTS,WORD_EVENTS;repeat rewrite<-app_assoc;reflexivity|].
  split;[exact DEPTH|]. split;[exact NODES|]. split.
  - apply Forall_app;split;[exact QUIET|constructor;[left;reflexivity|exact BODY_QUIET]].
  - split.
    + eapply gateway_steps_append;[exact PREFIX|].
      econstructor;[apply gateway_internal;[exact I|apply step_internal_function;exact ENTRY]|exact TO_WORD].
    + split;[exact WORD_READY|]. split;assumption.
Qed.

End ValueFirstWord.
