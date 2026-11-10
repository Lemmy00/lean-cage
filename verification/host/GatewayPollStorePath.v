(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Owned poll stores and pure source paths compose with their actual traces. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewaySource GatewayReadySource GatewayPollLayout GatewayPollStore
  GatewayReadyContext GatewayReadContext GatewayStreamInterface GatewayThreadRuntime GatewayOperations
  GatewayControlPaths GatewayReadonly GatewayPrimitiveCalls GatewayGuardObservation GatewayTransferMath.
Import ListNotations.

Theorem gateway_quiet_prefix_cut {World Event} (backend : gateway_backend World Event) ge
    (io : Event -> option gateway_native_io) descriptor ready (discipline : gateway_runtime_discipline backend ready)
    target source before world events returned after next :
  gateway_retained_prefix ge target source -> ready before world ->
  gateway_steps backend ge (gateway_live (gateway_replace_memory source before) world) events
    (gateway_live (Returnstate returned Kstop after) next) ->
  exists prefix suffix memory current,
    events = prefix ++ suffix /\ gateway_received_bytes io descriptor prefix = [] /\
    gateway_steps backend ge (gateway_live (gateway_replace_memory source before) world) prefix
      (gateway_live (gateway_replace_memory target memory) current) /\ ready memory current /\
    gateway_steps backend ge (gateway_live (gateway_replace_memory target memory) current) suffix
      (gateway_live (Returnstate returned Kstop after) next).
Proof.
  intros SCRIPT READY RUN.
  destruct (gateway_prefix_side_cut backend ge ready discipline target source SCRIPT
    before world events returned after next READY RUN)
    as (prefix & suffix & memory & current & EVENTS & QUIET & PREFIX & CALLED & REST).
  exists prefix, suffix, memory, current; split; [exact EVENTS |].
  split; [apply gateway_quiet_received_empty; exact QUIET |]. split; [exact PREFIX |]. split; assumption.
Qed.

Section PollStorePath.
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

Theorem actual_poll_store_prefix item mode current member ty delta chunk expression continuation temporaries
    before world events returned after next :
  poll_member_layout ge member delta -> access_mode ty = By_value chunk ->
  slice item mode current before world ->
  gateway_steps backend ge
    (gateway_live (State f_host_ready (Sassign (poll_member member ty) expression) continuation
      (ready_environment item) temporaries before) world) events
    (gateway_live (Returnstate returned Kstop after) next) ->
  exists prefix suffix changed called_world,
    events = prefix ++ suffix /\ gateway_received_bytes io (stream_descriptor initial) prefix = [] /\
    gateway_steps backend ge
      (gateway_live (State f_host_ready (Sassign (poll_member member ty) expression) continuation
        (ready_environment item) temporaries before) world) prefix
      (gateway_live (State f_host_ready Sskip continuation (ready_environment item) temporaries changed) called_world) /\
    slice item mode current changed called_world /\
    gateway_steps backend ge
      (gateway_live (State f_host_ready Sskip continuation (ready_environment item) temporaries changed) called_world)
      suffix (gateway_live (Returnstate returned Kstop after) next).
Proof.
  intros LAYOUT ACCESS READY RUN.
  destruct (actual_poll_store_retained backend ge io native_private stable_readonly discipline thread_errno runtime
    stream_block stream_offset initial data_block data_offset amount readonly reference owner
    item mode current member ty delta chunk expression continuation temporaries before world events returned after next
    LAYOUT ACCESS READY RUN)
    as (pending & suffix & memory & changed & called_world & value & EVENTS & AMBIENT & PREFIX & REAL & STORE &
      UPDATED & SUFFIX).
  exists (pending ++ [gateway_source E0]), suffix, changed, called_world.
  split; [rewrite EVENTS; rewrite <- app_assoc; reflexivity |]. split.
  - rewrite gateway_received_bytes_append.
    rewrite (gateway_pending_received_empty io (stream_descriptor initial) pending
      ltac:(eapply Forall_impl; [|exact AMBIENT]; intros event SAME; left; exact SAME)); reflexivity.
  - split.
    + eapply gateway_steps_append; [exact PREFIX |].
      econstructor; [apply gateway_internal; [cbn; tauto | exact REAL] | constructor].
    + split; assumption.
Qed.

End PollStorePath.
