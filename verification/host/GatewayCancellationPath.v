(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Cancellation's actual guard reaches its own command and endpoint. *)
From Stdlib Require Import List ZArith.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine ClightSteps StoreSteps.
From HostGateway Require Import GatewaySource GatewayMachine GatewayCancellation GatewayCancellationRuntime
  GatewayCancellationSend GatewayGuardScope GatewayGuardFunction GatewayThreadRuntime GatewayStreamInterface
  GatewayRuntimeABI GatewayReadContext GatewayReadMemory GatewayMemoryCuts GatewayControlPaths GatewayGuardedCuts
  GatewayOperations GatewayStreamLayout GatewayFrames.
Import ListNotations.

Definition control_command_cont := Kseq control_after_command Kstop.

Lemma control_boundary_command_prefix ge command temporaries memory :
  gateway_retained_prefix ge
    (State f_host_control control_command_assignment control_command_cont
      (control_environment command) temporaries memory)
    (State f_host_control Sskip (Kseq control_after_guard Kstop)
      (control_environment command) temporaries memory).
Proof.
  eapply gateway_prefix_next with (next := State f_host_control control_after_guard Kstop
    (control_environment command) temporaries memory);
    [cbn; tauto | intro another; apply unchanged_store_edge, edge_skip_seq |].
  eapply gateway_prefix_next with (next := State f_host_control control_command_assignment control_command_cont
    (control_environment command) temporaries memory).
  - cbn; tauto.
  - intro another; apply unchanged_store_edge.
    change (edge ge (State f_host_control
      (Ssequence control_command_assignment control_after_command) Kstop
      (control_environment command) temporaries another)
      (State f_host_control control_command_assignment control_command_cont
      (control_environment command) temporaries another)); apply edge_seq.
  - change (gateway_retained_prefix ge
      (State f_host_control control_command_assignment control_command_cont
        (control_environment command) temporaries memory) (gateway_replace_memory
      (State f_host_control control_command_assignment control_command_cont
        (control_environment command) temporaries memory) memory)); constructor.
Qed.

Lemma control_command_send_path ge command temporaries stream_block stream_offset initial memory symbol :
  temporaries ! _stream = Some (Vptr stream_block stream_offset) ->
  stream_member_layout ge _control 4 ->
  Genv.find_symbol ge _send = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some gateway_send_definition ->
  gateway_guarded_retained_path ge
    (fun memory => gateway_stream_memory memory stream_block stream_offset initial)
    gateway_send_definition
    [Vint (stream_control initial); Vptr command Ptrofs.zero; Vlong Int64.one; Vint (Int.repr 16384)]
    (control_send_cont command temporaries (stream_control initial))
    (State f_host_control Sskip control_command_cont (control_environment command) temporaries memory).
Proof.
  intros STREAM LAYOUT SYMBOL FUNCTION.
  eapply gateway_guarded_next with (next := State f_host_control control_after_command Kstop
    (control_environment command) temporaries memory);
    [cbn; tauto | intros another CELLS; apply unchanged_store_edge, edge_skip_seq |].
  eapply gateway_guarded_next with (next := State f_host_control control_send_binding
    (Kseq control_after_send Kstop) (control_environment command) temporaries memory);
    [cbn; tauto | intros another CELLS; apply unchanged_store_edge, edge_seq |].
  eapply gateway_guarded_next with (next := State f_host_control control_send_prefix
    (Kseq control_count_binding (Kseq control_after_send Kstop)) (control_environment command) temporaries memory);
    [cbn; tauto | intros another CELLS; apply unchanged_store_edge, edge_seq |].
  eapply gateway_guarded_next with (next := State f_host_control control_descriptor_load
    (Kseq control_send_call (Kseq control_count_binding (Kseq control_after_send Kstop)))
    (control_environment command) temporaries memory);
    [cbn; tauto | intros another CELLS; apply unchanged_store_edge, edge_seq |].
  eapply actual_control_descriptor_send_path; eassumption.
Qed.

Section CancellationPath.
Context {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (io : Event -> option gateway_native_io)
    (native_private : World -> block -> Prop) (stable_readonly : World -> block -> Z -> Prop)
    (discipline : option val -> mem -> World -> Prop) (thread_errno : World -> int).
Context (runtime : gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).
Context (stream_block : block) (stream_offset : ptrofs) (initial : gateway_stream_values)
    (data_block : block) (data_offset : ptrofs) (amount : Z) (readonly : block -> Z -> Prop).
Local Definition command_context := control_context native_private stable_readonly discipline
  stream_block stream_offset initial data_block data_offset amount readonly.
Local Definition initialized_context := cancellation_command_context native_private stable_readonly discipline
  stream_block stream_offset initial data_block data_offset amount readonly.

Theorem actual_control_stores_then_sends command temporaries before world events returned after next symbol :
  temporaries ! _stream = Some (Vptr stream_block stream_offset) ->
  stream_member_layout ge _control 4 ->
  Genv.find_symbol ge _send = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some gateway_send_definition ->
  command_context command before world ->
  gateway_steps backend ge
    (gateway_live (State f_host_control Sskip (Kseq control_after_guard Kstop)
      (control_environment command) temporaries before) world) events
    (gateway_live (Returnstate returned Kstop after) next) ->
  exists prefix suffix memory current,
    events = prefix ++ suffix /\ initialized_context command memory current /\
    gateway_steps backend ge
      (gateway_live (State f_host_control Sskip (Kseq control_after_guard Kstop)
        (control_environment command) temporaries before) world) prefix
      (gateway_live (Callstate gateway_send_definition
        [Vint (stream_control initial); Vptr command Ptrofs.zero; Vlong Int64.one; Vint (Int.repr 16384)]
        (control_send_cont command temporaries (stream_control initial)) memory) current) /\
    gateway_steps backend ge
      (gateway_live (Callstate gateway_send_definition
        [Vint (stream_control initial); Vptr command Ptrofs.zero; Vlong Int64.one; Vint (Int.repr 16384)]
        (control_send_cont command temporaries (stream_control initial)) memory) current) suffix
      (gateway_live (Returnstate returned Kstop after) next).
Proof.
  intros STREAM LAYOUT SYMBOL FUNCTION READY RUN.
  destruct (gateway_prefix_side_cut backend ge (command_context command)
    (control_context_ambient _ _ _ _ _ _ runtime _ _ _ _ _ _ _ command)
    _ _ (control_boundary_command_prefix ge command temporaries before)
    before world events returned after next READY RUN)
    as (p0 & r0 & m0 & w0 & E0S & Q0 & P0 & C0 & R0).
  destruct (gateway_memory_edge_side_cut backend ge (command_context command) (initialized_context command)
    (control_context_ambient _ _ _ _ _ _ runtime _ _ _ _ _ _ _ command)
    (State f_host_control control_command_assignment control_command_cont (control_environment command) temporaries m0)
    (State f_host_control Sskip control_command_cont (control_environment command) temporaries m0)
    m0 w0 r0 returned after next ltac:(cbn; tauto)
    ltac:(intros memory current CONTEXT; eapply cancellation_command_store; exact runtime || exact CONTEXT)
    C0 R0)
    as (p1 & r1 & m1 & stored & w1 & E1 & Q1 & P1 & C1 & EDGE & S1 & R1).
  assert (CELLS : forall memory current, initialized_context command memory current ->
    gateway_stream_memory memory stream_block stream_offset initial).
  { intros memory current CONTEXT.
    destruct (proj1 (proj1 CONTEXT)) as [SIDE [NATIVE [DATA [STABLE RAW]]]].
    exact (gateway_read_stream_cells _ _ _ _ _ _ _ _ RAW). }
  destruct (gateway_guarded_ready_cut backend ge
    (fun memory => gateway_stream_memory memory stream_block stream_offset initial)
    gateway_send_definition
    [Vint (stream_control initial); Vptr command Ptrofs.zero; Vlong Int64.one; Vint (Int.repr 16384)]
    (control_send_cont command temporaries (stream_control initial)) (initialized_context command)
    (cancellation_command_ambient _ _ _ _ _ _ runtime _ _ _ _ _ _ _ command)
    CELLS
    (State f_host_control Sskip control_command_cont (control_environment command) temporaries stored)
    w1 r1 returned after next S1
    (control_command_send_path ge command temporaries stream_block stream_offset initial stored symbol
      STREAM LAYOUT SYMBOL FUNCTION) R1)
    as (p2 & suffix & memory & current & E2 & Q2 & P2 & C2 & SUFFIX).
  exists (p0 ++ p1 ++ gateway_source E0 :: p2), suffix, memory, current.
  split; [rewrite E0S, E1, E2; repeat rewrite <- app_assoc; cbn; reflexivity |].
  split; [exact C2 |]. split; [| exact SUFFIX].
  eapply gateway_steps_append; [exact P0 |].
  eapply gateway_steps_append; [exact P1 |].
  destruct EDGE as [IN [REAL UNIQUE]].
  econstructor; [apply gateway_internal; [exact IN | exact REAL] | exact P2].
Qed.

End CancellationPath.
