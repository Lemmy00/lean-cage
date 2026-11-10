(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: One actual poll iteration saves, polls, captures errno, restores and checks signals. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewaySource GatewayReadySource GatewayReadyPhases GatewayReadySetupPaths
  GatewayReadyPollCalls GatewayReadyErrnoCalls GatewayReadyCapture GatewayReadyRestoreCalls GatewayReadyContext
  GatewayReadyOperations GatewayReadyNoOutput GatewayReadySignals GatewayPollStorePath GatewayReadonly GatewayContexts
  GatewayTransferCalls GatewayThreadRuntime GatewayRuntimeABI GatewayReadContext GatewayStreamInterface
  GatewayOperations GatewayPrimitiveCalls GatewayTransferMath.
Import ListNotations.

Definition ready_iteration_values temporaries saved status pointer number :=
  PTree.set _t'7 (Vint Int.zero)
    (ready_number_values (ready_polled_values (ready_saved_values temporaries saved) status) pointer number).

Lemma gateway_call_body_then {World Event} (backend : gateway_backend World Event) ge source world
    prefix definition arguments continuation called called_world operation result changed changed_world caller target :
  gateway_steps backend ge (gateway_live source world) prefix
    (gateway_live (Callstate definition arguments continuation called) called_world) ->
  gateway_steps backend ge (gateway_live (Callstate definition arguments Kstop called) called_world) operation
    (gateway_live (Returnstate result Kstop changed) changed_world) ->
  is_call_cont continuation ->
  gateway_steps backend ge (gateway_live (Returnstate result continuation changed) changed_world) caller target ->
  gateway_steps backend ge (gateway_live source world) (prefix ++ operation ++ caller) target.
Proof.
  intros PREFIX OPERATION CALL CALLER.
  eapply gateway_steps_append; [exact PREFIX |].
  eapply gateway_steps_append; [|exact CALLER].
  exact (gateway_plug_steps backend ge (gateway_live (Callstate definition arguments Kstop called) called_world)
    operation (gateway_live (Returnstate result Kstop changed) changed_world) continuation CALL OPERATION).
Qed.

Section ReadyIteration.
Context {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (io : Event -> option gateway_native_io)
    (native_private : World -> block -> Prop) (stable_readonly : World -> block -> Z -> Prop)
    (discipline : option val -> mem -> World -> Prop) (thread_errno : World -> int).
Context (runtime : gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).
Context (stream_block : block) (stream_offset : ptrofs) (initial : gateway_stream_values)
    (data_block : block) (data_offset : ptrofs) (amount : Z) (readonly : block -> Z -> Prop).
Variables (reference : mem) (owner : World).
Local Definition slice := gateway_ready_slice native_private stable_readonly discipline
  stream_block stream_offset initial data_block data_offset amount readonly reference owner.
Local Lemma ambient item mode current : gateway_runtime_discipline backend (slice item mode current).
Proof. apply gateway_ready_slice_ambient with (io := io) (thread_errno := thread_errno); exact runtime. Qed.
Variables poll_symbol errno_symbol restore_symbol signals_symbol : block.
Hypotheses
  (POLL_SYMBOL : Genv.find_symbol ge _poll = Some poll_symbol)
  (POLL_FUNCTION : Genv.find_funct_ptr ge poll_symbol = Some gateway_poll_definition)
  (ERRNO_SYMBOL : Genv.find_symbol ge ___errno_location = Some errno_symbol)
  (ERRNO_FUNCTION : Genv.find_funct_ptr ge errno_symbol = Some gateway_errno_location_definition)
  (RESTORE_SYMBOL : Genv.find_symbol ge _PyEval_RestoreThread = Some restore_symbol)
  (RESTORE_FUNCTION : Genv.find_funct_ptr ge restore_symbol = Some gateway_restore_thread_definition)
  (SIGNALS_SYMBOL : Genv.find_symbol ge _PyErr_CheckSignals = Some signals_symbol)
  (SIGNALS_FUNCTION : Genv.find_funct_ptr ge signals_symbol = Some gateway_check_signals_definition).

Theorem actual_ready_poll_iteration item current temporaries before world events after next :
  temporaries ! _stream = Some (Vptr stream_block stream_offset) -> slice item None current before world ->
  gateway_steps backend ge
    (gateway_live (Callstate gateway_save_thread_definition [] (ready_save_cont item temporaries) before) world)
    events (gateway_live (Returnstate (Vint Int.zero) Kstop after) next) ->
  exists prefix suffix memory called_world saved status pointer number,
    events = prefix ++ suffix /\ (0 < length prefix)%nat /\
    gateway_received_bytes io (stream_descriptor initial) prefix = [] /\
    slice item None current memory called_world /\
    (ready_iteration_values temporaries saved status pointer number) ! _stream = Some (Vptr stream_block stream_offset) /\
    gateway_steps backend ge
      (gateway_live (Callstate gateway_save_thread_definition [] (ready_save_cont item temporaries) before) world)
      prefix (gateway_live (State f_host_ready ready_after_signals ready_iteration_cont (ready_environment item)
        (ready_iteration_values temporaries saved status pointer number) memory) called_world) /\
    gateway_steps backend ge
      (gateway_live (State f_host_ready ready_after_signals ready_iteration_cont (ready_environment item)
        (ready_iteration_values temporaries saved status pointer number) memory) called_world)
      suffix (gateway_live (Returnstate (Vint Int.zero) Kstop after) next).
Proof.
  intros STREAM READY RUN.
  destruct (gateway_return_cut backend ge gateway_save_thread_definition [] (ready_save_cont item temporaries)
    before world events (Returnstate (Vint Int.zero) Kstop after) next ltac:(reflexivity)
    ltac:(cbn [ready_save_cont gateway_continuation gateway_cont_weight]; lia) RUN)
    as (save_events & save_rest & saved & m1 & w1 & E0S & SAVE & R0).
  destruct (actual_ready_save_operation backend ge io native_private stable_readonly discipline thread_errno runtime
    stream_block stream_offset initial data_block data_offset amount readonly reference owner
    item current before world save_events saved m1 w1 READY SAVE) as (SAVED_POINTER & C1 & B0).
  destruct (gateway_retained_callback_execution backend ge (slice item (Some saved) current) (ambient item (Some saved) current)
    (Returnstate saved (ready_save_cont item temporaries) m1) w1 save_rest (Vint Int.zero) after next
    gateway_poll_definition [Vptr item Ptrofs.zero; Vlong Int64.one; Vint (Int.repr 100)]
    (ready_poll_cont item (ready_saved_values temporaries saved)) ltac:(reflexivity)
    ltac:(cbn [ready_poll_cont gateway_cont_weight]; lia) C1
    (actual_ready_saved_poll_path ge item temporaries saved m1 poll_symbol POLL_SYMBOL POLL_FUNCTION) R0)
    as (p1 & poll_events & poll_rest & m2 & w2 & polled & m3 & w3 & E1S & Q1 & P1 & C2 & POLL & R1).
  destruct (actual_ready_poll_operation backend ge io native_private stable_readonly discipline thread_errno runtime
    stream_block stream_offset initial data_block data_offset amount readonly reference owner
    item current saved m2 w2 poll_events polled m3 w3 C2 POLL) as ((status & POLLED) & C3 & B1); subst polled.
  destruct (gateway_retained_callback_execution backend ge (slice item (Some saved) current) (ambient item (Some saved) current)
    (Returnstate (Vint status) (ready_poll_cont item (ready_saved_values temporaries saved)) m3) w3 poll_rest
    (Vint Int.zero) after next gateway_errno_location_definition []
    (ready_errno_cont item (ready_polled_values (ready_saved_values temporaries saved) status)) ltac:(reflexivity)
    ltac:(cbn [ready_errno_cont gateway_cont_weight]; lia) C3
    (actual_ready_polled_errno_path ge item (ready_saved_values temporaries saved) status m3 errno_symbol
      ERRNO_SYMBOL ERRNO_FUNCTION) R1)
    as (p2 & errno_events & errno_rest & m4 & w4 & pointer & m5 & w5 & E2S & Q2 & P2 & C4 & ERRNO & R2).
  destruct (actual_ready_errno_operation backend ge io native_private stable_readonly discipline thread_errno runtime
    stream_block stream_offset initial data_block data_offset amount readonly reference owner
    item current (Some saved) m4 w4 errno_events pointer m5 w5 C4 ERRNO) as (ERRNO_POINTER & C5 & B2).
  destruct (actual_ready_captures_errno backend ge io (stream_descriptor initial) (slice item (Some saved) current)
    (ambient item (Some saved) current) item (ready_polled_values (ready_saved_values temporaries saved) status) pointer
    m5 w5 errno_rest (Vint Int.zero) after next C5 R2)
    as (capture & captured_rest & m6 & w6 & number & E3S & B3 & C6 & NUMBER & PC & R3).
  set (temps := ready_number_values (ready_polled_values (ready_saved_values temporaries saved) status) pointer number).
  assert (SAVED : temps ! _saved = Some saved).
  { unfold temps, ready_number_values, ready_errno_values, ready_polled_values, ready_saved_values.
    rewrite !PTree.gso by discriminate; apply PTree.gss. }
  destruct (gateway_retained_callback_execution backend ge (slice item (Some saved) current) (ambient item (Some saved) current)
    (State f_host_ready Sskip (Kseq ready_after_errno ready_iteration_cont) (ready_environment item) temps m6) w6
    captured_rest (Vint Int.zero) after next gateway_restore_thread_definition [saved] (ready_restore_cont item temps)
    ltac:(reflexivity) ltac:(cbn [ready_restore_cont gateway_cont_weight]; lia) C6
    (actual_ready_captured_restore_path ge item temps saved m6 restore_symbol SAVED_POINTER SAVED
      RESTORE_SYMBOL RESTORE_FUNCTION) R3)
    as (p3 & restore_events & restore_rest & m7 & w7 & ignored & m8 & w8 & E4S & Q3 & P3 & C7 & RESTORE & R4).
  destruct (actual_ready_restore_operation backend ge io native_private stable_readonly discipline thread_errno runtime
    stream_block stream_offset initial data_block data_offset amount readonly reference owner
    item current saved m7 w7 restore_events ignored m8 w8 C7 RESTORE) as (C8 & B4).
  destruct (gateway_retained_callback_execution backend ge (slice item None current) (ambient item None current)
    (Returnstate ignored (ready_restore_cont item temps) m8) w8 restore_rest (Vint Int.zero) after next
    gateway_check_signals_definition [] (ready_signals_cont item temps) ltac:(reflexivity)
    ltac:(cbn [ready_signals_cont gateway_cont_weight]; lia) C8
    (actual_ready_restored_signals_path ge item temps ignored m8 signals_symbol SIGNALS_SYMBOL SIGNALS_FUNCTION) R4)
    as (p4 & signals_events & signals_rest & m9 & w9 & signal_result & m10 & w10 & E5S & Q4 & P4 & C9 & SIGNALS & R5).
  destruct (actual_ready_signals_operation backend ge io native_private stable_readonly discipline thread_errno runtime
    stream_block stream_offset initial data_block data_offset amount readonly reference owner
    item current m9 w9 signals_events signal_result m10 w10 C9 SIGNALS)
    as ((signal_status & SIGNAL_RESULT) & NORMAL & B5); subst signal_result.
  pose proof (actual_ready_checked_signals_zero backend ge item temps signal_status m10 w10 signals_rest after next R5) as ZERO.
  subst signal_status; specialize (NORMAL eq_refl).
  destruct (gateway_quiet_prefix_cut backend ge io (stream_descriptor initial) (slice item None current) (ambient item None current)
    _ _ m10 w10 signals_rest (Vint Int.zero) after next (actual_ready_zero_signals_prefix ge item temps m10) NORMAL R5)
    as (p5 & suffix & memory & called_world & E6S & B6 & P5 & FINAL_READY & REST).
  set (prefix := save_events ++ p1 ++ poll_events ++ p2 ++ errno_events ++ capture ++ p3 ++ restore_events ++
    p4 ++ signals_events ++ p5).
  exists prefix, suffix, memory, called_world, saved, status, pointer, number.
  split; [unfold prefix; rewrite E0S, E1S, E2S, E3S, E4S, E5S, E6S;
    repeat rewrite <- app_assoc; reflexivity |].
  split.
  - assert (NONEMPTY : (0 < length save_events)%nat) by
      (destruct save_events; [inversion SAVE | cbn; lia]).
    unfold prefix; repeat rewrite length_app; lia.
  - split.
    + unfold prefix; repeat rewrite gateway_received_bytes_append.
      rewrite B0, B1, B2, B3, B4, B5, B6,
        (gateway_quiet_received_empty io (stream_descriptor initial) p1 Q1),
        (gateway_quiet_received_empty io (stream_descriptor initial) p2 Q2),
        (gateway_quiet_received_empty io (stream_descriptor initial) p3 Q3),
        (gateway_quiet_received_empty io (stream_descriptor initial) p4 Q4); reflexivity.
    + split; [exact FINAL_READY |]. split.
      * unfold ready_iteration_values, ready_number_values, ready_errno_values, ready_polled_values, ready_saved_values.
        rewrite !PTree.gso by discriminate; exact STREAM.
      * split; [|exact REST]. unfold prefix.
        eapply gateway_steps_append.
        -- exact (gateway_plug_steps backend ge
             (gateway_live (Callstate gateway_save_thread_definition [] Kstop before) world) save_events
             (gateway_live (Returnstate saved Kstop m1) w1) (ready_save_cont item temporaries) ltac:(reflexivity) SAVE).
        -- eapply gateway_call_body_then; [exact P1 | exact POLL |reflexivity |].
           eapply gateway_call_body_then; [exact P2 | exact ERRNO |reflexivity |].
           eapply gateway_steps_append; [exact PC |].
           eapply gateway_call_body_then; [exact P3 | exact RESTORE |reflexivity |].
           eapply gateway_call_body_then; [exact P4 | exact SIGNALS |reflexivity |exact P5].
Qed.

End ReadyIteration.
