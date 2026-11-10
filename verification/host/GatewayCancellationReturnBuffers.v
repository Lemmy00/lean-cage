(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: An actual control return frees only its own local byte. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewayCancellation GatewayCancellationRuntime
  GatewayCancellationMemory GatewayCancellationSuffix GatewayCancellationBuffers GatewayCancellationEntryBuffers
  GatewayThreadRuntime GatewayStreamInterface GatewayReadContext GatewayInstructions GatewayReadonly
  GatewayCalls GatewayOperations GatewayPrimitiveCalls GatewayFrames GatewayGuardObservation GatewayTransferMath.
Import ListNotations.

Section CancellationReturnBuffers.
Context {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (io : Event -> option gateway_native_io)
    (native_private : World -> block -> Prop) (stable_readonly : World -> block -> BinNums.Z -> Prop)
    (discipline : option val -> mem -> World -> Prop) (thread_errno : World -> Integers.int).
Context (runtime : gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).
Context (stream_block : block) (stream_offset : Integers.ptrofs) (initial : gateway_stream_values)
    (data_block : block) (data_offset : Integers.ptrofs) (amount : BinNums.Z) (readonly : block -> BinNums.Z -> Prop).
Variables (reference : mem) (owner : World).
Local Definition entry_context := control_entry_buffer_context native_private stable_readonly discipline
  stream_block stream_offset initial data_block data_offset amount readonly reference owner.
Local Definition result_context := control_entry_read_context native_private stable_readonly discipline
  stream_block stream_offset initial data_block data_offset amount readonly reference owner.

Lemma control_return_scope command before world after :
  entry_context command before world ->
  Mem.free_list before (blocks_of_env ge (control_environment command)) = Some after ->
  result_context after world.
Proof.
  intros [CONTEXT HISTORY] FREE; split.
  - exact (proj1 (control_scope_free backend ge io native_private stable_readonly discipline thread_errno runtime
      stream_block stream_offset initial data_block data_offset amount readonly command before world after CONTEXT FREE)).
  - eapply control_buffer_history_free; [|exact HISTORY|exact FREE].
    exists initial; split; [exact CONTEXT | apply gateway_stream_transport_reflexive].
Qed.

Theorem actual_control_return_buffers function expression continuation command temporaries
    before world events returned after next :
  call_cont continuation = Kstop -> entry_context command before world ->
  gateway_steps backend ge
    (gateway_live (State function (Sreturn expression) continuation (control_environment command) temporaries before) world)
    events (gateway_live (Returnstate returned Kstop after) next) ->
  result_context after next /\ gateway_received_bytes io (stream_descriptor initial) events = [].
Proof.
  intros STOP READY RUN.
  destruct (gateway_source_instruction_occurrence backend ge function (Sreturn expression) continuation
    (control_environment command) temporaries before world events returned after next ltac:(cbn; tauto) RUN)
    as (prefix & suffix & memory & current & trace & target & EVENTS & AMBIENT & PREFIX & REAL & SUFFIX).
  assert (CALLED : entry_context command memory current).
  { eapply gateway_ambient_run_ready with
      (source := State function (Sreturn expression) continuation (control_environment command) temporaries before);
      [eapply control_entry_buffer_ambient; exact runtime | exact READY | exact AMBIENT | exact PREFIX]. }
  inversion REAL; subst;
    try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
  all: rewrite STOP in SUFFIX.
  all: match goal with FREE : Mem.free_list ?called_memory (blocks_of_env ge (control_environment ?actual_command)) = Some ?freed |- _ =>
    pose proof (control_return_scope actual_command called_memory current freed CALLED FREE) as FREED end.
  all: assert (FINAL : result_context after next) by
    (match type of SUFFIX with gateway_steps _ _ (gateway_live ?actual_source ?actual_world) _ _ =>
      eapply gateway_readonly_run_side with (source := actual_source) (world := actual_world);
        [eapply control_entry_read_ambient; exact runtime | exact I | exact FREED | exact SUFFIX] end).
  all: split; [exact FINAL |].
  all: rewrite gateway_received_bytes_append, gateway_received_source_cons.
  all: assert (PREFIX_EMPTY : gateway_received_bytes io (stream_descriptor initial) prefix = []) by
    (apply gateway_quiet_received_empty; eapply Forall_impl; [|exact AMBIENT]; intros event SAME; right; exact SAME).
  all: rewrite PREFIX_EMPTY; cbn [app].
  all: apply gateway_quiet_received_empty; eapply Forall_impl;
    [intros event SAME; right; exact SAME | eapply gateway_terminal_return_ambient; exact SUFFIX].
Qed.

End CancellationReturnBuffers.
