(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The real cancellation send uses its actual stored command byte. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine StoreSteps.
From HostGateway Require Import GatewaySource GatewayMachine GatewayCancellation GatewayCancellationRuntime
  GatewayThreadRuntime GatewayStreamInterface GatewayMemoryCuts GatewayOperations GatewayPrimitiveCalls
  GatewayRuntime GatewayRuntimeABI GatewayReadonly.
Import ListNotations.
Open Scope Z_scope.

Section CancellationSend.
Context {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (io : Event -> option gateway_native_io)
    (native_private : World -> block -> Prop) (stable_readonly : World -> block -> Z -> Prop)
    (discipline : option val -> mem -> World -> Prop) (thread_errno : World -> int).
Context (runtime : gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).
Context (stream_block : block) (stream_offset : ptrofs) (initial : gateway_stream_values)
    (data_block : block) (data_offset : ptrofs) (amount : Z) (readonly : block -> Z -> Prop).

Definition cancellation_context := control_context native_private stable_readonly discipline
  stream_block stream_offset initial data_block data_offset amount readonly.
Definition cancellation_command_context command memory world : Prop :=
  cancellation_context command memory world /\
  Mem.loadbytes memory command 0 1 = Some [Byte (Byte.repr 67)].

Lemma cancellation_command_ambient command :
  gateway_runtime_discipline backend (cancellation_command_context command).
Proof.
  intros before world after next [CONTEXT BYTE] INTERFERENCE; split.
  - eapply control_context_ambient; [exact runtime | exact CONTEXT | exact INTERFERENCE].
  - destruct (gateway_thread_ambient _ _ _ _ _ _ runtime None _ _ _ _
      (proj1 (proj1 CONTEXT)) INTERFERENCE) as [SIDE [ACCESS FRAME]].
    eapply Mem.loadbytes_unchanged_on; [exact FRAME | | exact BYTE].
    intros position RANGE; split.
    + left; exact (proj1 (proj2 CONTEXT)).
    + unfold gateway_native_no_output; tauto.
Qed.

Lemma cancellation_command_store command temporaries continuation memory world :
  cancellation_context command memory world -> exists changed,
    store_edge ge
      (State f_host_control control_command_assignment continuation (control_environment command) temporaries memory)
      (State f_host_control Sskip continuation (control_environment command) temporaries changed) /\
    cancellation_command_context command changed world.
Proof.
  intro CONTEXT.
  assert (OWNED : Mem.valid_access memory Mint8unsigned command 0 Writable).
  { split.
    - intros position RANGE; eapply Mem.perm_implies;
        [apply (proj1 (proj2 (proj2 CONTEXT)) position); exact RANGE | constructor].
    - change (1 | 0); exists 0; reflexivity. }
  destruct (Mem.valid_access_store memory Mint8unsigned command 0 (Vint (Int.repr 67)) OWNED)
    as [changed STORE].
  exists changed; split; [apply actual_control_command_assignment; exact STORE |]. split.
  - eapply (proj1 (control_store_context _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ _ _ _ _ CONTEXT STORE)).
  - apply actual_control_command_bytes with (before := memory); exact STORE.
Qed.

Lemma cancellation_command_pointer command memory world :
  cancellation_command_context command memory world ->
  gateway_native_pointer memory command Ptrofs.zero 1 Readable.
Proof.
  intros [CONTEXT BYTE]; split; [lia |]. split; [change (1 <= 18446744073709551616); lia |]. split.
  - eapply control_context_command_live; exact CONTEXT.
  - intros position RANGE; eapply Mem.perm_implies;
      [apply (proj1 (proj2 (proj2 CONTEXT)) position); exact RANGE | constructor].
Qed.

Theorem actual_cancellation_send command before world events returned after next :
  cancellation_command_context command before world ->
  gateway_steps backend ge
    (gateway_live (Callstate gateway_send_definition
      [Vint (stream_control initial); Vptr command Ptrofs.zero; Vlong Int64.one;
        Vint (Int.repr 16384)] Kstop before) world) events
    (gateway_live (Returnstate returned Kstop after) next) ->
  exists count,
    -1 <= count <= 1 /\ returned = Vlong (Int64.repr count) /\
    cancellation_command_context command after next /\
    gateway_received_bytes io (stream_descriptor initial) events = [].
Proof.
  intros READY RUN.
  destruct (gateway_external_operation_of_run backend ge _ _ _ _ _
    before world events returned after next RUN)
    as [prefix [suffix [called [called_world [changed [changed_world [observed
      [EVENTS [PENDING [PREFIX [OPERATION SUFFIX]]]]]]]]]]].
  assert (CALLED : cancellation_command_context command called called_world).
  { eapply gateway_pending_run_ready with (source := Callstate gateway_send_definition
      [Vint (stream_control initial); Vptr command Ptrofs.zero; Vlong Int64.one;
        Vint (Int.repr 16384)] Kstop before);
      [apply cancellation_command_ambient | exact READY | exact PENDING | exact PREFIX]. }
  destruct (gateway_send_operation _ _ _ _ _ _ runtime None called called_world
    (stream_control initial) command Ptrofs.zero 1 returned changed changed_world observed
    (proj1 (proj1 (proj1 CALLED)))
    (or_introl (proj1 (proj2 (proj1 CALLED)))) ltac:(lia)
    (cancellation_command_pointer command called called_world CALLED) OPERATION)
    as [count [bytes [COUNT [RETURNED [LENGTH [LOAD [IO [SIDE [ACCESS FRAME]]]]]]]]].
  assert (CHANGED : cancellation_command_context command changed changed_world).
  { split.
    - eapply control_context_preserved; [exact (proj1 CALLED) | exact SIDE | exact ACCESS | exact FRAME].
    - eapply Mem.loadbytes_unchanged_on; [exact FRAME | | exact (proj2 CALLED)].
      intros position RANGE; split.
      + left; exact (proj1 (proj2 (proj1 CALLED))).
      + unfold gateway_native_no_output; tauto. }
  assert (FINAL : cancellation_command_context command after next).
  { eapply gateway_readonly_run_side with (source := Returnstate returned Kstop changed);
      [apply cancellation_command_ambient | exact I | exact CHANGED | exact SUFFIX]. }
  exists count; split; [exact COUNT |]. split; [exact RETURNED |]. split; [exact FINAL |].
  rewrite (gateway_external_received_projection backend ge io events returned after next
    prefix suffix changed changed_world observed (stream_descriptor initial) EVENTS PENDING SUFFIX).
  unfold gateway_received_event; rewrite IO; reflexivity.
Qed.

End CancellationSend.
