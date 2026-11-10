(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Successful actual readiness passes its timeout rejection. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine StoreSteps ClightSteps.
From HostGateway Require Import GatewayMachine GatewaySource GatewayReadySource GatewayReadyCalls
  GatewayInertCuts GatewayRuntimeCuts GatewayBranches GatewayCalls GatewayOperations GatewayFrames
  GatewayTransferMath GatewayPrimitiveCalls GatewayStreamInterface GatewayGuardObservation.
Import ListNotations.

Definition ready_clock_condition := match ready_clock_test with Sifthenelse condition _ _ => condition
  | _ => Econst_int Int.zero tint end.
Definition ready_clock_failure := match ready_clock_test with Sifthenelse _ failure _ => failure | _ => Sskip end.
Definition ready_after_timeout_cont := Kseq ready_after_clock_guard ready_iteration_cont.

Theorem actual_ready_timeout_passed {World Event} (backend : gateway_backend World Event) ge
    (io : Event -> option gateway_native_io) descriptor ready
    (discipline : gateway_runtime_discipline backend ready)
    item temporaries stream before world events after next :
  temporaries ! _stream = Some stream -> ready before world ->
  gateway_steps backend ge
    (gateway_live (State f_host_ready ready_clock_boolean ready_clock_guard_cont
      (ready_environment item) temporaries before) world)
    events (gateway_live (Returnstate (Vint Int.zero) Kstop after) next) ->
  exists prefix suffix final_temporaries memory current,
    events = prefix ++ suffix /\ gateway_received_bytes io descriptor prefix = [] /\
    final_temporaries ! _stream = Some stream /\ ready memory current /\
    gateway_steps backend ge
      (gateway_live (State f_host_ready ready_clock_boolean ready_clock_guard_cont
        (ready_environment item) temporaries before) world) prefix
      (gateway_live (State f_host_ready Sskip ready_after_timeout_cont
        (ready_environment item) final_temporaries memory) current) /\
    gateway_steps backend ge
      (gateway_live (State f_host_ready Sskip ready_after_timeout_cont
        (ready_environment item) final_temporaries memory) current)
      suffix (gateway_live (Returnstate (Vint Int.zero) Kstop after) next).
Proof.
  intros STREAM READY RUN.
  assert (PROFILE : gateway_inert_source _stream stream ready_clock_guard_cont f_host_ready
    (ready_environment item)
    (State f_host_ready ready_clock_boolean ready_clock_guard_cont (ready_environment item) temporaries before)).
  { cbn [gateway_inert_source]; split; [reflexivity |]. split; [reflexivity |].
    split; [exact STREAM |]. split; [cbn; intuition discriminate | constructor]. }
  destruct (gateway_inert_boundary_cut backend ge io descriptor ready discipline _stream stream
    ready_clock_test ready_after_timeout_cont f_host_ready (ready_environment item)
    (State f_host_ready ready_clock_boolean ready_clock_guard_cont (ready_environment item) temporaries before)
    world events (Vint Int.zero) after next ltac:(cbn; tauto) PROFILE READY RUN)
    as (p & rest & temps & m & w & EVENTS & EMPTY & PARAMETER & REACHED & PREFIX & SUFFIX).
  destruct (gateway_uniform_edge_side_cut backend ge ready discipline
    (State f_host_ready Sskip ready_clock_guard_cont (ready_environment item) temps m)
    (State f_host_ready ready_clock_test ready_after_timeout_cont (ready_environment item) temps m)
    m w rest (Vint Int.zero) after next ltac:(cbn; tauto)
    ltac:(intro another; apply unchanged_store_edge, edge_skip_seq) REACHED SUFFIX)
    as (pending & tail & tested & test_world & REST_EVENTS & AMBIENT & PENDING & TEST_READY & TEST_RUN).
  destruct (gateway_actual_branch backend ge ready discipline f_host_ready ready_clock_condition
    ready_clock_failure Sskip ready_after_timeout_cont (ready_environment item) temps tested test_world
    tail (Vint Int.zero) after next TEST_READY TEST_RUN)
    as (waiting & suffix & memory & current & value & branch & TAIL_EVENTS & WAITING & FINAL_READY &
      VALUE & BRANCH & BRANCH_PREFIX & FOLLOWING).
  destruct branch.
  - pose proof (gateway_error_sequence_returns_failure backend ge f_host_ready _ _ _ _
      ready_after_timeout_cont (ready_environment item) temps memory current suffix (Vint Int.zero) after next
      ltac:(reflexivity) ltac:(reflexivity) FOLLOWING) as BAD; discriminate BAD.
  - exists (p ++ pending ++ gateway_source E0 :: waiting ++ [gateway_source E0]), suffix, temps, memory, current.
    split.
    + rewrite EVENTS, REST_EVENTS, TAIL_EVENTS; repeat rewrite <- app_assoc; cbn [app].
      repeat rewrite <- app_assoc; cbn [app]; reflexivity.
    + split.
      * repeat rewrite gateway_received_bytes_append; rewrite EMPTY.
        assert (PENDING_EMPTY : gateway_received_bytes io descriptor pending = []).
        { apply gateway_quiet_received_empty; eapply Forall_impl; [|exact AMBIENT].
          intros event SAME; right; exact SAME. }
        assert (WAITING_EMPTY : gateway_received_bytes io descriptor waiting = []).
        { apply gateway_quiet_received_empty; eapply Forall_impl; [|exact WAITING].
          intros event SAME; right; exact SAME. }
        rewrite PENDING_EMPTY; cbn [app]. rewrite gateway_received_source_cons, gateway_received_bytes_append,
          WAITING_EMPTY; reflexivity.
      * split; [exact PARAMETER |]. split; [exact FINAL_READY |]. split; [|exact FOLLOWING].
        eapply gateway_steps_append; [exact PREFIX |].
        eapply gateway_steps_append; [exact PENDING |].
        econstructor.
        -- apply gateway_internal; [cbn; tauto | apply edge_skip_seq].
        -- eapply gateway_steps_append; [exact BRANCH_PREFIX |].
           econstructor; [|constructor].
           apply gateway_internal; [cbn; tauto |].
           apply step_ifthenelse with (v1 := value) (b := false); assumption.
Qed.
