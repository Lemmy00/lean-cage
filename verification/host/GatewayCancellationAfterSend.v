(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual send result reaches the maintained control suffix. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine StoreSteps ClightSteps LocalAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayCancellation GatewayCancellationRuntime
  GatewayCancellationSuffix GatewayCancellationBuffers GatewayCancellationSendBuffers GatewayControlPaths
  GatewayCancellationMemory
  GatewayThreadRuntime GatewayStreamInterface GatewayStreamLayout GatewayRuntimeABI GatewayBufferReference
  GatewayOperations GatewayFrames GatewayPrimitiveCalls GatewayTransferMath.
Import ListNotations.

Definition control_sent_temporaries temporaries descriptor count :=
  set_opttemp (Some _t'5) (Vlong count) (control_descriptor_values temporaries descriptor).
Definition control_count_temporaries temporaries descriptor count :=
  PTree.set _count (Vlong count) (control_sent_temporaries temporaries descriptor count).

Lemma control_sent_stream_retained temporaries descriptor count stream :
  temporaries ! _stream = Some stream ->
  (control_count_temporaries temporaries descriptor count) ! _stream = Some stream.
Proof.
  unfold control_count_temporaries, control_sent_temporaries, control_descriptor_values; cbn [set_opttemp].
  intro STREAM; repeat rewrite PTree.gso by discriminate; exact STREAM.
Qed.

Lemma actual_control_sent_prefix ge command temporaries descriptor count memory :
  gateway_retained_prefix ge
    (State f_host_control control_after_send Kstop (control_environment command)
      (control_count_temporaries temporaries descriptor count) memory)
    (Returnstate (Vlong count) (control_send_cont command temporaries descriptor) memory).
Proof.
  eapply gateway_prefix_next with (next := State f_host_control Sskip
    (Kseq control_count_binding (Kseq control_after_send Kstop)) (control_environment command)
    (control_sent_temporaries temporaries descriptor count) memory);
    [cbn; tauto | intro another; apply unchanged_store_edge, edge_returnstate |].
  eapply gateway_prefix_next with (next := State f_host_control control_count_binding
    (Kseq control_after_send Kstop) (control_environment command)
    (control_sent_temporaries temporaries descriptor count) memory);
    [cbn; tauto | intro another; apply unchanged_store_edge, edge_skip_seq |].
  eapply gateway_prefix_next with (next := State f_host_control Sskip
    (Kseq control_after_send Kstop) (control_environment command)
    (control_count_temporaries temporaries descriptor count) memory).
  - cbn; tauto.
  - intro another; apply certified_set_edge.
    apply old_expression_value, value_temp; unfold control_sent_temporaries; cbn [set_opttemp]; apply PTree.gss.
  - eapply gateway_prefix_next with (next := State f_host_control control_after_send Kstop
      (control_environment command) (control_count_temporaries temporaries descriptor count) memory);
      [cbn; tauto | intro another; apply unchanged_store_edge, edge_skip_seq |].
    change (gateway_retained_prefix ge
      (State f_host_control control_after_send Kstop (control_environment command)
        (control_count_temporaries temporaries descriptor count) memory)
      (gateway_replace_memory (State f_host_control control_after_send Kstop (control_environment command)
        (control_count_temporaries temporaries descriptor count) memory) memory)); constructor.
Qed.

Section CancellationAfterSend.
Context {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (io : Event -> option gateway_native_io)
    (native_private : World -> block -> Prop) (stable_readonly : World -> block -> BinNums.Z -> Prop)
    (discipline : option val -> mem -> World -> Prop) (thread_errno : World -> int).
Context (runtime : gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).
Context (stream_block : block) (stream_offset : ptrofs) (initial : gateway_stream_values)
    (data_block : block) (data_offset : ptrofs) (amount : BinNums.Z) (readonly : block -> BinNums.Z -> Prop).
Variables (reference : mem) (owner : World).
Local Definition send_context := control_send_buffer_context native_private stable_readonly discipline
  stream_block stream_offset initial data_block data_offset amount readonly reference owner.

Theorem actual_control_after_send_buffers command temporaries count before world events returned after next symbol :
  temporaries ! _stream = Some (Vptr stream_block stream_offset) ->
  stream_member_layout ge _cancellation_sent 8 ->
  Genv.find_symbol ge ___errno_location = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some gateway_errno_location_definition ->
  send_context command before world ->
  gateway_steps backend ge
    (gateway_live (Returnstate (Vlong count) (control_send_cont command temporaries (stream_control initial)) before) world)
    events (gateway_live (Returnstate returned Kstop after) next) ->
  control_tail_result native_private stable_readonly discipline stream_block stream_offset initial
    data_block data_offset amount readonly after next /\
  control_buffer_history native_private stream_block data_block readonly reference owner after next /\
  gateway_received_bytes io (stream_descriptor initial) events = [].
Proof.
  intros STREAM LAYOUT SYMBOL FUNCTION READY RUN.
  destruct (gateway_prefix_side_cut backend ge (send_context command)
    (control_send_buffer_ambient _ _ _ _ _ _ runtime _ _ _ _ _ _ _ reference owner command)
    _ _ (actual_control_sent_prefix ge command temporaries (stream_control initial) count before)
    before world events returned after next READY RUN)
    as (prefix & suffix & memory & current & EVENTS & QUIET & PREFIX & CONTEXT & SUFFIX).
  assert (PROFILE : control_tail_runtime native_private stable_readonly discipline stream_block stream_offset initial
    data_block data_offset amount readonly command
    (gateway_live (State f_host_control control_after_send Kstop (control_environment command)
      (control_count_temporaries temporaries (stream_control initial) count) memory) current)).
  { split.
    - cbn; split; [reflexivity |]. split; [reflexivity |]. split.
      + apply control_sent_stream_retained; exact STREAM.
      + split; [exact actual_control_suffix_classification | exact I].
    - exists initial; split; [exact (proj1 (proj1 CONTEXT)) | apply gateway_stream_transport_reflexive]. }
  destruct (actual_control_tail_retains_buffers backend ge io native_private stable_readonly discipline thread_errno runtime
    stream_block stream_offset initial data_block data_offset amount readonly reference owner command
    (State f_host_control control_after_send Kstop (control_environment command)
      (control_count_temporaries temporaries (stream_control initial) count) memory) current
    suffix returned after next symbol LAYOUT SYMBOL FUNCTION PROFILE (proj2 CONTEXT) SUFFIX)
    as [RESULT [HISTORY EMPTY]].
  split; [exact RESULT |]. split; [exact HISTORY |].
  rewrite EVENTS, gateway_received_bytes_append,
    (gateway_quiet_received_empty io (stream_descriptor initial) prefix QUIET), EMPTY; reflexivity.
Qed.

End CancellationAfterSend.
