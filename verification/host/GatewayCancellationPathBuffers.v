(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual command store and endpoint load retain caller buffers. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine StoreSteps.
From HostGateway Require Import GatewaySource GatewayMachine GatewayCancellation GatewayCancellationRuntime
  GatewayCancellationPath GatewayCancellationSend GatewayCancellationBuffers GatewayCancellationEntryBuffers
  GatewayCancellationSendBuffers GatewayScopeBufferReference GatewayThreadRuntime GatewayStreamInterface
  GatewayStreamLayout GatewayRuntimeABI GatewayMemoryCuts GatewayControlPaths GatewayGuardedCuts
  GatewayOperations GatewayFrames GatewayPrimitiveCalls GatewayGuardObservation GatewayTransferMath
  GatewayBufferReference GatewayGuardScope.
Import ListNotations.
Open Scope Z_scope.

Section CancellationPathBuffers.
Context {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (io : Event -> option gateway_native_io)
    (native_private : World -> block -> Prop) (stable_readonly : World -> block -> Z -> Prop)
    (discipline : option val -> mem -> World -> Prop) (thread_errno : World -> int).
Context (runtime : gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).
Context (stream_block : block) (stream_offset : ptrofs) (initial : gateway_stream_values)
    (data_block : block) (data_offset : ptrofs) (amount : Z) (readonly : block -> Z -> Prop).
Variables (reference : mem) (owner : World).
Local Definition entry_context := control_entry_buffer_context native_private stable_readonly discipline
  stream_block stream_offset initial data_block data_offset amount readonly reference owner.
Local Definition send_context := control_send_buffer_context native_private stable_readonly discipline
  stream_block stream_offset initial data_block data_offset amount readonly reference owner.

Lemma control_command_store_buffers command temporaries continuation memory world :
  entry_context command memory world -> exists changed,
    store_edge ge
      (State f_host_control control_command_assignment continuation (control_environment command) temporaries memory)
      (State f_host_control Sskip continuation (control_environment command) temporaries changed) /\
    send_context command changed world.
Proof.
  intros [CONTEXT [BUFFER NATIVE]].
  assert (OWNED : Mem.valid_access memory Mint8unsigned command 0 Writable).
  { split.
    - intros position RANGE; eapply Mem.perm_implies;
        [apply (proj1 (proj2 (proj2 CONTEXT)) position); exact RANGE | constructor].
    - change (1 | 0); exists 0; reflexivity. }
  destruct (Mem.valid_access_store memory Mint8unsigned command 0 (Vint (Int.repr 67)) OWNED)
    as [changed STORE].
  exists changed; split; [apply actual_control_command_assignment; exact STORE |].
  destruct (control_store_context backend io native_private stable_readonly discipline thread_errno runtime
    stream_block stream_offset initial data_block data_offset amount readonly command memory world changed
    (Int.repr 67) CONTEXT STORE) as [AFTER FRAME].
  split.
  - split; [exact AFTER |]. apply actual_control_command_bytes with (before := memory); exact STORE.
  - destruct CONTEXT as [INPUT [PRIVATE [COMMAND [STREAM [DATA IMMUTABLE]]]]].
    destruct (gateway_scope_store_buffer native_private readonly stream_block data_block memory changed world
      Mint8unsigned command 0 (Vint (Int.repr 67)) STORE IMMUTABLE) as [STEP_BUFFER STEP_NATIVE].
    split.
    + eapply gateway_buffer_reference_transitive; eassumption.
    + eapply gateway_native_reference_transitive; eassumption.
Qed.

Theorem actual_control_stores_then_sends_buffers command temporaries before world events returned after next symbol :
  temporaries ! _stream = Some (Vptr stream_block stream_offset) ->
  stream_member_layout ge _control 4 ->
  Genv.find_symbol ge _send = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some gateway_send_definition ->
  entry_context command before world ->
  gateway_steps backend ge
    (gateway_live (State f_host_control Sskip (Kseq control_after_guard Kstop)
      (control_environment command) temporaries before) world) events
    (gateway_live (Returnstate returned Kstop after) next) ->
  exists prefix suffix memory current,
    events = prefix ++ suffix /\ gateway_received_bytes io (stream_descriptor initial) prefix = [] /\
    send_context command memory current /\
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
  destruct (gateway_prefix_side_cut backend ge (entry_context command)
    (control_entry_buffer_ambient _ _ _ _ _ _ runtime _ _ _ _ _ _ _ reference owner command)
    _ _ (control_boundary_command_prefix ge command temporaries before)
    before world events returned after next READY RUN)
    as (p0 & r0 & m0 & w0 & E0S & Q0 & P0 & C0 & R0).
  destruct (gateway_memory_edge_side_cut backend ge (entry_context command) (send_context command)
    (control_entry_buffer_ambient _ _ _ _ _ _ runtime _ _ _ _ _ _ _ reference owner command)
    (State f_host_control control_command_assignment control_command_cont (control_environment command) temporaries m0)
    (State f_host_control Sskip control_command_cont (control_environment command) temporaries m0)
    m0 w0 r0 returned after next ltac:(cbn; tauto)
    (control_command_store_buffers command temporaries control_command_cont) C0 R0)
    as (p1 & r1 & m1 & stored & w1 & E1 & Q1 & P1 & C1 & EDGE & S1 & R1).
  assert (CELLS : forall memory current, send_context command memory current ->
    gateway_stream_memory memory stream_block stream_offset initial).
  { intros memory current CONTEXT.
    destruct (proj1 (proj1 (proj1 CONTEXT))) as [SIDE [NATIVE [DATA [STABLE RAW]]]].
    exact (gateway_read_stream_cells _ _ _ _ _ _ _ _ RAW). }
  destruct (gateway_guarded_ready_cut backend ge
    (fun memory => gateway_stream_memory memory stream_block stream_offset initial)
    gateway_send_definition
    [Vint (stream_control initial); Vptr command Ptrofs.zero; Vlong Int64.one; Vint (Int.repr 16384)]
    (control_send_cont command temporaries (stream_control initial)) (send_context command)
    (control_send_buffer_ambient _ _ _ _ _ _ runtime _ _ _ _ _ _ _ reference owner command) CELLS
    (State f_host_control Sskip control_command_cont (control_environment command) temporaries stored)
    w1 r1 returned after next S1
    (control_command_send_path ge command temporaries stream_block stream_offset initial stored symbol
      STREAM LAYOUT SYMBOL FUNCTION) R1)
    as (p2 & suffix & memory & current & E2 & Q2 & P2 & C2 & SUFFIX).
  exists (p0 ++ p1 ++ gateway_source E0 :: p2), suffix, memory, current.
  split; [rewrite E0S, E1, E2; repeat rewrite <- app_assoc; cbn; reflexivity |].
  split.
  - repeat rewrite gateway_received_bytes_append; rewrite gateway_received_source_cons.
    rewrite (gateway_quiet_received_empty io (stream_descriptor initial) p0 Q0),
      (gateway_quiet_received_empty io (stream_descriptor initial) p2 Q2).
    assert (EMPTY : gateway_received_bytes io (stream_descriptor initial) p1 = []).
    { apply gateway_quiet_received_empty; eapply Forall_impl; [|exact Q1]. intros event SAME; right; exact SAME. }
    rewrite EMPTY; reflexivity.
  - split; [exact C2 |]. split; [|exact SUFFIX].
    eapply gateway_steps_append; [exact P0 |].
    eapply gateway_steps_append; [exact P1 |].
    destruct EDGE as [IN [REAL UNIQUE]].
    econstructor; [apply gateway_internal; [exact IN | exact REAL] | exact P2].
Qed.

End CancellationPathBuffers.
