(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Compose the actual control entry, send and every returning branch. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayCancellation GatewayCancellationRuntime
  GatewayCancellationMemory GatewayCancellationSuffix GatewayCancellationBuffers GatewayCancellationEntryBuffers
  GatewayCancellationPathBuffers GatewayCancellationSendBuffers GatewayCancellationReturnBuffers
  GatewayCancellationAfterSend GatewayThreadRuntime GatewayStreamInterface GatewayStreamLayout GatewayRuntimeABI
  GatewayOperations GatewayFrames GatewayPrimitiveCalls GatewayTransferMath GatewayContexts GatewayReturns
  GatewayGuardScope GatewayGuardFunction GatewayReadonly GatewayBufferReference.
Import ListNotations.

Lemma control_guard_terminal_view command stream source :
  gateway_guard_source _stream stream (Kseq control_after_guard Kstop) (control_environment command) source ->
  gateway_guard_function f_host_control source ->
  gateway_guard_terminal (Kseq control_after_guard Kstop) source ->
  (exists temporaries memory,
    source = State f_host_control Sskip (Kseq control_after_guard Kstop) (control_environment command) temporaries memory /\
      temporaries ! _stream = Some stream) \/
  (exists expression continuation temporaries memory,
    source = State f_host_control (Sreturn expression) continuation (control_environment command) temporaries memory /\
      call_cont continuation = Kstop) \/
  (exists value memory, source = Returnstate value Kstop memory).
Proof.
  destruct source as [function body continuation environment temporaries memory |
    definition arguments continuation memory | returned continuation memory]; intros PROFILE FUNCTION TERMINAL.
  - destruct PROFILE as [ENV [STREAM [BODY CONT]]]; cbn in FUNCTION; subst function environment.
    destruct TERMINAL as [BOUNDARY | RETURN].
    + destruct body; cbn in BOUNDARY; try contradiction. subst continuation.
      left; exists temporaries, memory; split; [reflexivity | exact STREAM].
    + destruct body; cbn in RETURN; try contradiction.
      right; left; eexists; exists continuation, temporaries, memory; split; [reflexivity |].
      exact (gateway_guard_call_cont _ _ _ CONT).
  - contradiction.
  - destruct continuation; cbn in PROFILE; try contradiction.
    right; right; exists returned, memory; reflexivity.
Qed.

Section CancellationComplete.
Context {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (io : Event -> option gateway_native_io)
    (native_private : World -> block -> Prop) (stable_readonly : World -> block -> BinNums.Z -> Prop)
    (discipline : option val -> mem -> World -> Prop) (thread_errno : World -> int).
Context (runtime : gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).
Context (stream_block : block) (stream_offset : ptrofs) (initial : gateway_stream_values)
    (data_block : block) (data_offset : ptrofs) (amount : BinNums.Z) (readonly : block -> BinNums.Z -> Prop).
Variables (reference : mem) (owner : World).
Variables send_symbol errno_symbol : block.
Hypotheses
  (CONTROL_LAYOUT : stream_member_layout ge _control 4)
  (CANCEL_LAYOUT : stream_member_layout ge _cancellation_sent 8)
  (SEND_SYMBOL : Genv.find_symbol ge _send = Some send_symbol)
  (SEND_FUNCTION : Genv.find_funct_ptr ge send_symbol = Some gateway_send_definition)
  (ERRNO_SYMBOL : Genv.find_symbol ge ___errno_location = Some errno_symbol)
  (ERRNO_FUNCTION : Genv.find_funct_ptr ge errno_symbol = Some gateway_errno_location_definition).
Local Definition entry_context := control_entry_buffer_context native_private stable_readonly discipline
  stream_block stream_offset initial data_block data_offset amount readonly reference owner.
Local Definition result_context := control_entry_read_context native_private stable_readonly discipline
  stream_block stream_offset initial data_block data_offset amount readonly reference owner.
Local Definition final_context := control_tail_result native_private stable_readonly discipline
  stream_block stream_offset initial data_block data_offset amount readonly.
Local Definition history := control_buffer_history native_private stream_block data_block readonly reference owner.

Theorem actual_control_boundary_complete command temporaries before world events returned after next :
  temporaries ! _stream = Some (Vptr stream_block stream_offset) -> entry_context command before world ->
  gateway_steps backend ge
    (gateway_live (State f_host_control Sskip (Kseq control_after_guard Kstop)
      (control_environment command) temporaries before) world) events
    (gateway_live (Returnstate returned Kstop after) next) ->
  final_context after next /\ history after next /\
    gateway_received_bytes io (stream_descriptor initial) events = [].
Proof.
  intros STREAM READY RUN.
  destruct (actual_control_stores_then_sends_buffers backend ge io native_private stable_readonly discipline thread_errno runtime
    stream_block stream_offset initial data_block data_offset amount readonly reference owner
    command temporaries before world events returned after next send_symbol STREAM CONTROL_LAYOUT SEND_SYMBOL SEND_FUNCTION READY RUN)
    as (prefix & rest & memory & current & EVENTS & EMPTY & SEND_READY & PREFIX & REST).
  destruct (gateway_return_cut backend ge gateway_send_definition
    [Vint (stream_control initial); Vptr command Ptrofs.zero; Vlong Int64.one; Vint (Int.repr 16384)]
    (control_send_cont command temporaries (stream_control initial)) memory current rest
    (Returnstate returned Kstop after) next ltac:(reflexivity)
    ltac:(cbn [control_send_cont gateway_continuation gateway_cont_weight]; lia) REST)
    as (send_events & caller_events & sent & changed & changed_world & REST_EVENTS & SEND & CALLER).
  destruct (actual_cancellation_send_buffers backend ge io native_private stable_readonly discipline thread_errno runtime
    stream_block stream_offset initial data_block data_offset amount readonly reference owner
    command memory current send_events sent changed changed_world SEND_READY SEND)
    as (count & COUNT & SENT & SENT_CONTEXT & SEND_EMPTY); subst sent.
  destruct (actual_control_after_send_buffers backend ge io native_private stable_readonly discipline thread_errno runtime
    stream_block stream_offset initial data_block data_offset amount readonly reference owner
    command temporaries (Int64.repr count) changed changed_world caller_events returned after next errno_symbol
    STREAM CANCEL_LAYOUT ERRNO_SYMBOL ERRNO_FUNCTION SENT_CONTEXT CALLER)
    as [FINAL [HISTORY CALLER_EMPTY]].
  split; [exact FINAL |]. split; [exact HISTORY |].
  rewrite EVENTS, REST_EVENTS, !gateway_received_bytes_append, EMPTY, SEND_EMPTY, CALLER_EMPTY; reflexivity.
Qed.

Theorem actual_control_complete before world events returned after next :
  result_context before world ->
  gateway_steps backend ge
    (gateway_live (Callstate (Internal f_host_control) [Vptr stream_block stream_offset] Kstop before) world)
    events (gateway_live (Returnstate returned Kstop after) next) ->
  final_context after next /\ history after next /\
    gateway_received_bytes io (stream_descriptor initial) events = [].
Proof.
  intros READY RUN.
  destruct (actual_control_guard_buffer_cut backend ge io native_private stable_readonly discipline thread_errno runtime
    stream_block stream_offset initial data_block data_offset amount readonly reference owner
    before world events returned after next READY RUN)
    as (prefix & suffix & command & reached & reached_world & EVENTS & EMPTY & CONTEXT & SCOPE & IDENTITY &
      TERMINAL & PREFIX & SUFFIX).
  destruct (control_guard_terminal_view command (Vptr stream_block stream_offset) reached SCOPE IDENTITY TERMINAL)
    as [(temporaries & memory & SOURCE & STREAM) |
      [(expression & continuation & temporaries & memory & SOURCE & STOP) | (value & memory & SOURCE)]];
      subst reached.
  - destruct (actual_control_boundary_complete command temporaries memory reached_world suffix returned after next
      STREAM CONTEXT SUFFIX) as [FINAL [HISTORY SUFFIX_EMPTY]].
    split; [exact FINAL |]. split; [exact HISTORY |].
    rewrite EVENTS, gateway_received_bytes_append, EMPTY, SUFFIX_EMPTY; reflexivity.
  - destruct (actual_control_return_buffers backend ge io native_private stable_readonly discipline thread_errno runtime
      stream_block stream_offset initial data_block data_offset amount readonly reference owner
      f_host_control expression continuation command temporaries memory reached_world suffix returned after next
      STOP CONTEXT SUFFIX) as [[INPUT HISTORY] SUFFIX_EMPTY].
    split.
    + exists initial; split; [exact INPUT | apply gateway_stream_transport_reflexive].
    + split; [exact HISTORY |].
      rewrite EVENTS, gateway_received_bytes_append, EMPTY, SUFFIX_EMPTY; reflexivity.
  - assert (INITIAL : result_context memory reached_world).
    { split; [exact (proj1 (proj1 CONTEXT)) | exact (proj2 CONTEXT)]. }
    assert (FINAL : result_context after next).
    { eapply gateway_readonly_run_side with (source := Returnstate value Kstop memory);
        [eapply control_entry_read_ambient; exact runtime | exact I | exact INITIAL | exact SUFFIX]. }
    destruct FINAL as [INPUT HISTORY]; split.
    + exists initial; split; [exact INPUT | apply gateway_stream_transport_reflexive].
    + split; [exact HISTORY |]. rewrite EVENTS, gateway_received_bytes_append, EMPTY; cbn [app].
      apply gateway_quiet_received_empty; eapply Forall_impl;
        [intros event SAME; right; exact SAME | eapply gateway_terminal_return_ambient; exact SUFFIX].
Qed.

End CancellationComplete.
