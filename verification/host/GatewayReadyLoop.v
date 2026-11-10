(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: The actual readiness loop retains retries on the same finite trace. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewayMachine GatewaySource GatewayReadySource GatewayReadyBindings GatewayReadyControl
  GatewayReadyClock GatewayReadySetup GatewayReadyIteration GatewayReadyTail GatewayReadyReturn GatewayReadyContext
  GatewayReadyCalls GatewayReadySetupPaths GatewayThreadRuntime GatewayRuntimeABI GatewayBindings GatewayReadContext
  GatewayStreamInterface GatewayBufferReference GatewayTransferMath.
Import ListNotations.

Section ReadyLoop.
Context {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (io : Event -> option gateway_native_io)
    (native_private : World -> block -> Prop) (stable_readonly : World -> block -> Z -> Prop)
    (discipline : option val -> mem -> World -> Prop) (thread_errno : World -> int).
Context (runtime : gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).
Context (bindings : gateway_ready_bindings ge).
Context (stream_block : block) (stream_offset : ptrofs) (initial : gateway_stream_values)
    (data_block : block) (data_offset : ptrofs) (amount : Z) (readonly : block -> Z -> Prop).
Variables (reference : mem) (owner : World).
Local Definition slice := gateway_ready_slice native_private stable_readonly discipline
  stream_block stream_offset initial data_block data_offset amount readonly reference owner.
Local Definition result current := gateway_owned_buffer_context native_private stable_readonly discipline
  stream_block data_block stream_offset data_offset current amount readonly reference owner None.

Theorem actual_ready_loop_bounded fuel :
  forall events, (length events < fuel)%nat ->
  forall item current temporaries before world after next,
    temporaries ! _stream = Some (Vptr stream_block stream_offset) -> slice item None current before world ->
    gateway_steps backend ge
      (gateway_live (State f_host_ready (fn_body f_host_ready) Kstop (ready_environment item) temporaries before) world)
      events (gateway_live (Returnstate (Vint Int.zero) Kstop after) next) ->
    exists final, gateway_stream_transport_after initial final /\ result final after next /\
      gateway_received_bytes io (stream_descriptor initial) events = [].
Proof.
  induction fuel as [|fuel IH]; intros events LIMIT item current temporaries before world after next STREAM READY RUN; [lia |].
  destruct bindings as (ITEM_SIZE & CLOCK_SIZE & CONTROL & CANCEL & FD & EVENTS_FIELD & REVENTS & FUNCTIONS).
  pose proof (proj1 (Forall_forall _ _) FUNCTIONS) as TABLE.
  destruct (TABLE (_host_control, Internal f_host_control) ltac:(cbn; tauto)) as (control_symbol & CONTROL_SYMBOL & CONTROL_FUNCTION).
  destruct (TABLE (_host_now, Internal f_host_now) ltac:(cbn; tauto)) as (now_symbol & NOW_SYMBOL & NOW_FUNCTION).
  destruct (TABLE (_send, gateway_send_definition) ltac:(cbn; tauto)) as (send_symbol & SEND_SYMBOL & SEND_FUNCTION).
  destruct (TABLE (___errno_location, gateway_errno_location_definition) ltac:(cbn; tauto)) as (errno_symbol & ERRNO_SYMBOL & ERRNO_FUNCTION).
  destruct (TABLE (_PyEval_SaveThread, gateway_save_thread_definition) ltac:(cbn; tauto)) as (save_symbol & SAVE_SYMBOL & SAVE_FUNCTION).
  destruct (TABLE (_poll, gateway_poll_definition) ltac:(cbn; tauto)) as (poll_symbol & POLL_SYMBOL & POLL_FUNCTION).
  destruct (TABLE (_PyEval_RestoreThread, gateway_restore_thread_definition) ltac:(cbn; tauto)) as (restore_symbol & RESTORE_SYMBOL & RESTORE_FUNCTION).
  destruct (TABLE (_PyErr_CheckSignals, gateway_check_signals_definition) ltac:(cbn; tauto)) as (signals_symbol & SIGNALS_SYMBOL & SIGNALS_FUNCTION).
  destruct (TABLE (_clock_gettime, gateway_clock_gettime_definition) ltac:(cbn; tauto)) as (clock_symbol & CLOCK_SYMBOL & CLOCK_FUNCTION).
  destruct (actual_ready_control_before_clock backend ge io native_private stable_readonly discipline thread_errno runtime
    stream_block stream_offset initial data_block data_offset amount readonly reference owner
    control_symbol send_symbol errno_symbol now_symbol CONTROL_SYMBOL CONTROL_FUNCTION CONTROL CANCEL SEND_SYMBOL SEND_FUNCTION
    ERRNO_SYMBOL ERRNO_FUNCTION NOW_SYMBOL NOW_FUNCTION item current temporaries before world events after next STREAM READY RUN)
    as (p0 & rest0 & updated & m0 & w0 & E0S & P0 & C0 & B0 & R0).
  assert (CONTROL_STREAM : (PTree.set _t'1 (Vint Int.zero) temporaries) ! _stream = Some (Vptr stream_block stream_offset)).
  { rewrite PTree.gso by discriminate; exact STREAM. }
  destruct (actual_ready_clock_before_item backend ge io native_private stable_readonly discipline thread_errno runtime
    stream_block stream_offset initial data_block data_offset amount readonly reference owner
    item updated (PTree.set _t'1 (Vint Int.zero) temporaries) m0 w0 rest0 after next clock_symbol
    CLOCK_SIZE CLOCK_SYMBOL CLOCK_FUNCTION CONTROL_STREAM C0 R0)
    as (p1 & rest1 & temps1 & m1 & w1 & E1S & B1 & STREAM1 & C1 & P1 & R1).
  destruct (actual_ready_item_before_save backend ge io native_private stable_readonly discipline thread_errno runtime
    stream_block stream_offset initial data_block data_offset amount readonly reference owner
    item updated temps1 m1 w1 rest1 after next save_symbol FD EVENTS_FIELD REVENTS SAVE_SYMBOL SAVE_FUNCTION STREAM1 C1 R1)
    as (p2 & rest2 & temps2 & m2 & w2 & E2S & B2 & STREAM2 & C2 & P2 & R2).
  destruct (actual_ready_poll_iteration backend ge io native_private stable_readonly discipline thread_errno runtime
    stream_block stream_offset initial data_block data_offset amount readonly reference owner
    poll_symbol errno_symbol restore_symbol signals_symbol POLL_SYMBOL POLL_FUNCTION ERRNO_SYMBOL ERRNO_FUNCTION
    RESTORE_SYMBOL RESTORE_FUNCTION SIGNALS_SYMBOL SIGNALS_FUNCTION item updated temps2 m2 w2 rest2 after next STREAM2 C2 R2)
    as (p3 & rest3 & m3 & w3 & saved & status & pointer & number & E3S & MORE & B3 & C3 & STREAM3 & P3 & R3).
  assert (AMBIENT : GatewayOperations.gateway_runtime_discipline backend (slice item None updated)).
  { apply gateway_ready_slice_ambient with (io := io) (thread_errno := thread_errno); exact runtime. }
  destruct (actual_ready_tail_destination backend ge io (stream_descriptor initial) (slice item None updated) AMBIENT
    item (ready_iteration_values temps2 saved status pointer number) (Vptr stream_block stream_offset) m3 w3 rest3 after next
    STREAM3 C3 R3)
    as (p4 & suffix & temps4 & m4 & w4 & returning & E4S & B4 & STREAM4 & C4 & P4 & REST).
  assert (EMPTY_RESULT : exists final, gateway_stream_transport_after initial final /\ result final after next /\
    gateway_received_bytes io (stream_descriptor initial) suffix = []).
  { destruct returning.
    - destruct (actual_ready_return_buffers backend ge io native_private stable_readonly discipline thread_errno runtime
        stream_block stream_offset initial data_block data_offset amount readonly reference owner
        (Some (Econst_int Int.zero tint)) ready_iteration_cont item updated temps4 m4 w4 suffix (Vint Int.zero) after next
        ITEM_SIZE ltac:(reflexivity) C4 REST) as [OUTPUT EMPTY].
      exists updated; split; [exact (proj1 (proj2 C4)) |]. split; assumption.
    - assert (SMALL : (length suffix < fuel)%nat).
      { rewrite E0S, E1S, E2S, E3S, E4S in LIMIT; repeat rewrite length_app in LIMIT; lia. }
      exact (IH suffix SMALL item updated temps4 m4 w4 after next STREAM4 C4 REST). }
  destruct EMPTY_RESULT as (final & CHANGE & OUTPUT & EMPTY).
  exists final; split; [exact CHANGE |]. split; [exact OUTPUT |].
  rewrite E0S, E1S, E2S, E3S, E4S; repeat rewrite gateway_received_bytes_append.
  rewrite B0, B1, B2, B3, B4, EMPTY; reflexivity.
Qed.

Theorem actual_ready_loop_complete item current temporaries before world events after next :
  temporaries ! _stream = Some (Vptr stream_block stream_offset) -> slice item None current before world ->
  gateway_steps backend ge
    (gateway_live (State f_host_ready (fn_body f_host_ready) Kstop (ready_environment item) temporaries before) world)
    events (gateway_live (Returnstate (Vint Int.zero) Kstop after) next) ->
  exists final, gateway_stream_transport_after initial final /\ result final after next /\
    gateway_received_bytes io (stream_descriptor initial) events = [].
Proof.
  intros STREAM READY RUN; eapply actual_ready_loop_bounded with (fuel := S (length events));
    [lia |exact STREAM |exact READY |exact RUN].
Qed.

End ReadyLoop.
