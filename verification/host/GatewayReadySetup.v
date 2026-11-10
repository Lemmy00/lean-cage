(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: The real caller initializes all three owned poll fields before detaching. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewaySource GatewayReadySource GatewayReadyPhases GatewayReadyTimeout
  GatewayReadySetupPaths GatewayReadyContext GatewayPollStorePath GatewayPollLayout GatewayInertCuts
  GatewayInertEffects GatewayReadonly GatewayOperations GatewayThreadRuntime GatewayRuntimeABI
  GatewayReadContext GatewayStreamInterface GatewayPrimitiveCalls GatewayTransferMath.
Import ListNotations.

Section ReadySetup.
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

Theorem actual_ready_item_before_save item current temporaries before world events after next save_symbol :
  poll_member_layout ge _fd 0 -> poll_member_layout ge _events 4 -> poll_member_layout ge _revents 6 ->
  Genv.find_symbol ge _PyEval_SaveThread = Some save_symbol ->
  Genv.find_funct_ptr ge save_symbol = Some gateway_save_thread_definition ->
  temporaries ! _stream = Some (Vptr stream_block stream_offset) ->
  slice item None current before world ->
  gateway_steps backend ge
    (gateway_live (State f_host_ready Sskip ready_after_timeout_cont (ready_environment item) temporaries before) world)
    events (gateway_live (Returnstate (Vint Int.zero) Kstop after) next) ->
  exists prefix suffix final_temporaries memory called_world,
    events = prefix ++ suffix /\ gateway_received_bytes io (stream_descriptor initial) prefix = [] /\
    final_temporaries ! _stream = Some (Vptr stream_block stream_offset) /\
    slice item None current memory called_world /\
    gateway_steps backend ge
      (gateway_live (State f_host_ready Sskip ready_after_timeout_cont (ready_environment item) temporaries before) world)
      prefix (gateway_live (Callstate gateway_save_thread_definition []
        (ready_save_cont item final_temporaries) memory) called_world) /\
    gateway_steps backend ge
      (gateway_live (Callstate gateway_save_thread_definition []
        (ready_save_cont item final_temporaries) memory) called_world)
      suffix (gateway_live (Returnstate (Vint Int.zero) Kstop after) next).
Proof.
  intros FD EVENTS_FIELD REVENTS SAVE_SYMBOL SAVE_FUNCTION STREAM READY RUN.
  assert (AMBIENT : gateway_runtime_discipline backend (slice item None current)).
  { apply gateway_ready_slice_ambient with (io := io) (thread_errno := thread_errno); exact runtime. }
  destruct (gateway_quiet_prefix_cut backend ge io (stream_descriptor initial) (slice item None current) AMBIENT _ _
    before world events (Vint Int.zero) after next (actual_ready_descriptor_prefix ge item temporaries before) READY RUN)
    as (p0 & rest0 & m0 & w0 & E0S & B0 & P0 & C0 & R0).
  assert (PROFILE : gateway_inert_source _stream (Vptr stream_block stream_offset)
    (Kseq ready_descriptor_store ready_descriptor_cont) f_host_ready (ready_environment item)
    (State f_host_ready ready_descriptor_load (Kseq ready_descriptor_store ready_descriptor_cont)
      (ready_environment item) temporaries m0)).
  { cbn [gateway_inert_source]; split; [reflexivity |]. split; [reflexivity |]. split; [exact STREAM |].
    split; [cbn; discriminate | constructor]. }
  destruct (gateway_inert_effect_cut backend ge io (stream_descriptor initial) (slice item None current) AMBIENT
    _stream (Vptr stream_block stream_offset) ready_descriptor_store ready_descriptor_cont f_host_ready (ready_environment item)
    (State f_host_ready ready_descriptor_load (Kseq ready_descriptor_store ready_descriptor_cont)
      (ready_environment item) temporaries m0) w0 rest0 (Vint Int.zero) after next
    ltac:(cbn; tauto) PROFILE C0 R0)
    as (p1 & rest1 & temps & m1 & w1 & E1S & B1 & PARAMETER & C1 & P1 & R1).
  destruct (actual_poll_store_prefix backend ge io native_private stable_readonly discipline thread_errno runtime
    stream_block stream_offset initial data_block data_offset amount readonly reference owner
    item None current _fd tint 0 Mint32 (Etempvar _t'11 tint) ready_descriptor_cont temps
    m1 w1 rest1 (Vint Int.zero) after next FD ltac:(reflexivity) C1 R1)
    as (p2 & rest2 & m2 & w2 & E2S & B2 & P2 & C2 & R2).
  destruct (gateway_quiet_prefix_cut backend ge io (stream_descriptor initial) (slice item None current) AMBIENT _ _
    m2 w2 rest2 (Vint Int.zero) after next (actual_ready_events_prefix ge item temps m2) C2 R2)
    as (p3 & rest3 & m3 & w3 & E3S & B3 & P3 & C3 & R3).
  destruct (actual_poll_store_prefix backend ge io native_private stable_readonly discipline thread_errno runtime
    stream_block stream_offset initial data_block data_offset amount readonly reference owner
    item None current _events tshort 4 Mint16signed (Etempvar _events tshort) ready_events_cont temps
    m3 w3 rest3 (Vint Int.zero) after next EVENTS_FIELD ltac:(reflexivity) C3 R3)
    as (p4 & rest4 & m4 & w4 & E4S & B4 & P4 & C4 & R4).
  destruct (gateway_quiet_prefix_cut backend ge io (stream_descriptor initial) (slice item None current) AMBIENT _ _
    m4 w4 rest4 (Vint Int.zero) after next (actual_ready_revents_prefix ge item temps m4) C4 R4)
    as (p5 & rest5 & m5 & w5 & E5S & B5 & P5 & C5 & R5).
  destruct (actual_poll_store_prefix backend ge io native_private stable_readonly discipline thread_errno runtime
    stream_block stream_offset initial data_block data_offset amount readonly reference owner
    item None current _revents tshort 6 Mint16signed (Econst_int Int.zero tint) ready_revents_cont temps
    m5 w5 rest5 (Vint Int.zero) after next REVENTS ltac:(reflexivity) C5 R5)
    as (p6 & rest6 & m6 & w6 & E6S & B6 & P6 & C6 & R6).
  destruct (gateway_retained_call_ready_cut backend ge (slice item None current) AMBIENT
    gateway_save_thread_definition [] (ready_save_cont item temps)
    (State f_host_ready Sskip ready_revents_cont (ready_environment item) temps m6) w6 rest6
    (Vint Int.zero) after next (actual_ready_save_path ge item temps m6 save_symbol SAVE_SYMBOL SAVE_FUNCTION) C6 R6)
    as (p7 & suffix & memory & called_world & E7S & QUIET & P7 & FINAL_READY & REST).
  exists (p0 ++ p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6 ++ p7), suffix, temps, memory, called_world.
  split.
  - rewrite E0S, E1S, E2S, E3S, E4S, E5S, E6S, E7S; repeat rewrite <- app_assoc; reflexivity.
  - split.
    + repeat rewrite gateway_received_bytes_append; rewrite B0, B1, B2, B3, B4, B5, B6,
        (gateway_quiet_received_empty io (stream_descriptor initial) p7 QUIET); reflexivity.
    + split; [exact PARAMETER |]. split; [exact FINAL_READY |]. split; [|exact REST].
      eapply gateway_steps_append; [exact P0 |].
      eapply gateway_steps_append; [exact P1 |].
      eapply gateway_steps_append; [exact P2 |].
      eapply gateway_steps_append; [exact P3 |].
      eapply gateway_steps_append; [exact P4 |].
      eapply gateway_steps_append; [exact P5 |].
      eapply gateway_steps_append; [exact P6 | exact P7].
Qed.

End ReadySetup.
