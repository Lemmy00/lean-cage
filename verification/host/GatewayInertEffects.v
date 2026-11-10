(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: A pure actual prefix reaches its next effect on the same run. *)
From Stdlib Require Import List.
From compcert Require Import Maps AST Values Memory Events Clight.
Require Import Machine StoreSteps ClightSteps.
From HostGateway Require Import GatewayMachine GatewayOperations GatewayFrames GatewayInertCuts
  GatewayRuntimeCuts GatewayStreamInterface GatewayPrimitiveCalls GatewayTransferMath GatewayGuardObservation.
Import ListNotations.

Theorem gateway_inert_effect_cut {World Event} (backend : gateway_backend World Event) ge
    (io : Event -> option gateway_native_io) descriptor ready (discipline : gateway_runtime_discipline backend ready)
    parameter value tail outer function environment source world events returned after next :
  ~ gateway_inert_statement parameter tail ->
  gateway_inert_source parameter value (Kseq tail outer) function environment source ->
  ready (memory_of source) world ->
  gateway_steps backend ge (gateway_live source world) events
    (gateway_live (Returnstate returned Kstop after) next) ->
  exists prefix suffix temporaries memory current,
    events = prefix ++ suffix /\ gateway_received_bytes io descriptor prefix = [] /\
    temporaries ! parameter = Some value /\ ready memory current /\
    gateway_steps backend ge (gateway_live source world) prefix
      (gateway_live (State function tail outer environment temporaries memory) current) /\
    gateway_steps backend ge (gateway_live (State function tail outer environment temporaries memory) current)
      suffix (gateway_live (Returnstate returned Kstop after) next).
Proof.
  intros OPAQUE PROFILE READY RUN.
  destruct (gateway_inert_boundary_cut backend ge io descriptor ready discipline parameter value tail outer
    function environment source world events returned after next OPAQUE PROFILE READY RUN)
    as (p & rest & temporaries & boundary_memory & boundary_world & EVENTS & EMPTY & PARAMETER &
      REACHED & PREFIX & SUFFIX).
  destruct (gateway_uniform_edge_side_cut backend ge ready discipline
    (State function Sskip (Kseq tail outer) environment temporaries boundary_memory)
    (State function tail outer environment temporaries boundary_memory)
    boundary_memory boundary_world rest returned after next ltac:(cbn; tauto)
    ltac:(intro another; apply unchanged_store_edge, edge_skip_seq) REACHED SUFFIX)
    as (pending & suffix & memory & current & REST & AMBIENT & PENDING & FINAL_READY & FOLLOWING).
  exists (p ++ pending ++ [gateway_source E0]), suffix, temporaries, memory, current.
  split.
  - rewrite EVENTS, REST; repeat rewrite <- app_assoc; reflexivity.
  - split.
    + repeat rewrite gateway_received_bytes_append; rewrite EMPTY.
      assert (PENDING_EMPTY : gateway_received_bytes io descriptor pending = []).
      { apply gateway_quiet_received_empty; eapply Forall_impl; [|exact AMBIENT].
        intros event SAME; right; exact SAME. }
      rewrite PENDING_EMPTY; reflexivity.
    + split; [exact PARAMETER |]. split; [exact FINAL_READY |]. split; [|exact FOLLOWING].
      eapply gateway_steps_append; [exact PREFIX |].
      eapply gateway_steps_append; [exact PENDING |].
      econstructor; [apply gateway_internal; [cbn; tauto | apply edge_skip_seq] | constructor].
Qed.
