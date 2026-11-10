(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Concrete source stores and frees retain caller buffer ownership. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayCancellation GatewayCancellationRuntime
  GatewayCancellationMemory GatewayCancellationSuffix GatewayCancellationFrames GatewayThreadRuntime
  GatewayStreamInterface GatewayReadContext GatewayReadMemory GatewayRuntime GatewayRuntimeABI
  GatewayBufferReference GatewayReadonlyOperations GatewayStreamLayout.
Import ListNotations.
Open Scope Z_scope.

Section CancellationBuffers.
Context {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (io : Event -> option gateway_native_io)
    (native_private : World -> block -> Prop) (stable_readonly : World -> block -> Z -> Prop)
    (discipline : option val -> mem -> World -> Prop) (thread_errno : World -> int).
Context (runtime : gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).
Context (stream_block : block) (stream_offset : ptrofs) (initial : gateway_stream_values)
    (data_block : block) (data_offset : ptrofs) (amount : Z) (readonly : block -> Z -> Prop).
Variables (reference : mem) (owner : World).

Definition control_buffer_history memory world : Prop :=
  gateway_buffer_reference readonly stream_block data_block reference memory /\
  gateway_native_reference native_private reference owner memory world.

Lemma control_buffer_history_operation current before world after next :
  gateway_read_context native_private stable_readonly discipline None stream_block stream_offset current
    data_block data_offset amount readonly before world ->
  gateway_access_retained native_private stable_readonly before world next ->
  gateway_native_frame native_private stable_readonly gateway_native_no_output world before after ->
  control_buffer_history before world -> control_buffer_history after next.
Proof.
  intros CONTEXT ACCESS FRAME [BUFFER NATIVE]; split.
  - eapply gateway_buffer_reference_transitive; [exact BUFFER |]. split.
    + eapply gateway_read_context_readonly_frame; eassumption.
    + eapply gateway_context_buffer_permissions; eassumption.
  - eapply gateway_native_reference_transitive; [exact NATIVE |].
    eapply gateway_native_reference_operation; eassumption.
Qed.

Lemma control_buffer_history_mark command before world after :
  control_tail_active native_private stable_readonly discipline stream_block stream_offset initial
    data_block data_offset amount readonly command before world ->
  control_buffer_history before world ->
  Mem.store Mint32 before stream_block (Ptrofs.unsigned stream_offset + 8) (Vint Int.one) = Some after ->
  control_buffer_history after world.
Proof.
  intros [current [CONTEXT TRANSPORT]] [BUFFER NATIVE] STORE.
  pose proof (proj2 (proj2 (proj2 (proj2 (proj1 CONTEXT))))) as RAW.
  destruct (gateway_mark_cancel_read_inputs _ _ _ _ _ _ _ _ _ RAW STORE) as [MARKED [FRAME PERMISSIONS]].
  split.
  - eapply gateway_buffer_reference_transitive; [exact BUFFER |]. split.
    + eapply Mem.unchanged_on_implies; [exact FRAME |]. intros object position HERE; left; exact HERE.
    + intros object HERE position kind permission; apply PERMISSIONS.
  - eapply gateway_native_reference_transitive; [exact NATIVE |].
    intros object LIVE PRIVATE; split; [eapply Mem.store_valid_block_1; eassumption | exact PRIVATE].
Qed.

Lemma control_buffer_history_free command before world after :
  control_tail_active native_private stable_readonly discipline stream_block stream_offset initial
    data_block data_offset amount readonly command before world ->
  control_buffer_history before world ->
  Mem.free_list before (blocks_of_env ge (control_environment command)) = Some after ->
  control_buffer_history after world.
Proof.
  intros [current [CONTEXT TRANSPORT]] [BUFFER NATIVE] FREE.
  destruct CONTEXT as [INPUT [PRIVATE [COMMAND [STREAM [DATA READONLY]]]]].
  pose proof (proj2 (proj2 (proj2 (proj2 INPUT)))) as RAW.
  change (Mem.free_list before [(command, 0, 1)] = Some after) in FREE.
  cbn in FREE; destruct (Mem.free before command 0 1) as [changed |] eqn:ACTUAL; [|discriminate].
  inversion FREE; subst changed.
  assert (FRAME : Mem.unchanged_on (fun object _ => object <> command) before after).
  { eapply Mem.free_unchanged_on; [exact ACTUAL |]. intros position RANGE DIFFERENT; contradiction. }
  split.
  - eapply gateway_buffer_reference_transitive; [exact BUFFER |]. split.
    + eapply Mem.unchanged_on_implies; [exact FRAME |].
      intros object position HERE LIVE SAME; subst object; exact (READONLY position HERE).
    + intros object [SAME | SAME] position kind permission; subst object.
      * apply (Mem.unchanged_on_perm _ _ _ FRAME stream_block position kind permission).
        -- congruence.
        -- eapply gateway_read_stream_live; exact RAW.
      * apply (Mem.unchanged_on_perm _ _ _ FRAME data_block position kind permission).
        -- congruence.
        -- exact (gateway_read_data_live _ _ _ _ _ _ _ _ RAW).
  - eapply gateway_native_reference_transitive; [exact NATIVE |].
    intros object LIVE OWNED; split; [eapply Mem.valid_block_free_1; eassumption | exact OWNED].
Qed.

Theorem control_buffer_history_rules command :
  control_tail_extra_contract backend ge native_private stable_readonly discipline
    stream_block stream_offset initial data_block data_offset amount readonly command control_buffer_history.
Proof.
  constructor.
  - intros; eapply control_buffer_history_mark; eassumption.
  - intros; eapply control_buffer_history_free; eassumption.
  - intros current before world after next INPUT HISTORY INTERFERENCE.
    destruct (gateway_thread_ambient _ _ _ _ _ _ runtime None _ _ _ _ (proj1 INPUT) INTERFERENCE)
      as [SIDE [ACCESS FRAME]].
    eapply control_buffer_history_operation; eassumption.
  - intros before world returned after next observed [current [CONTEXT TRANSPORT]] HISTORY OPERATION.
    destruct (gateway_errno_location_operation _ _ _ _ _ _ runtime None before world returned after next observed
      (proj1 (proj1 CONTEXT)) OPERATION)
      as (object & offset & POINTER & GEOMETRY & VALUE & FOREIGN & MUTABLE & SIDE & ACCESS & FRAME & IO).
    eapply control_buffer_history_operation; [exact (proj1 CONTEXT) | exact ACCESS | exact FRAME | exact HISTORY].
Qed.

Theorem actual_control_tail_retains_buffers command source world events returned after next symbol :
  stream_member_layout ge _cancellation_sent 8 ->
  Genv.find_symbol ge ___errno_location = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some gateway_errno_location_definition ->
  control_tail_runtime native_private stable_readonly discipline stream_block stream_offset initial
    data_block data_offset amount readonly command (gateway_live source world) ->
  control_buffer_history (memory_of source) world ->
  gateway_steps backend ge (gateway_live source world) events
    (gateway_live (Returnstate returned Kstop after) next) ->
  control_tail_result native_private stable_readonly discipline stream_block stream_offset initial
    data_block data_offset amount readonly after next /\
  control_buffer_history after next /\ gateway_received_bytes io (stream_descriptor initial) events = [].
Proof.
  intros LAYOUT SYMBOL FUNCTION READY HISTORY RUN.
  pose proof (actual_control_tail_extra_prefix backend ge io native_private stable_readonly discipline thread_errno runtime
    stream_block stream_offset initial data_block data_offset amount readonly command control_buffer_history
    (control_buffer_history_rules command) source world events (gateway_live (Returnstate returned Kstop after) next)
    symbol LAYOUT SYMBOL FUNCTION (conj READY HISTORY) RUN) as FINAL.
  destruct FINAL as [[PROFILE RESULT] RETAINED].
  split; [exact RESULT |]. split; [exact RETAINED |].
  exact (proj2 (actual_control_tail_prefix backend ge io native_private stable_readonly discipline thread_errno runtime
    stream_block stream_offset initial data_block data_offset amount readonly command source world events
    (gateway_live (Returnstate returned Kstop after) next) symbol LAYOUT SYMBOL FUNCTION READY RUN)).
Qed.

End CancellationBuffers.
