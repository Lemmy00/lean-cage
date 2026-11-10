(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: The actual source captures errno before restoring its saved token. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps.
From HostGateway Require Import GatewayMachine GatewaySource GatewayReadySource GatewayReadyPhases GatewayReadyErrnoCalls
  GatewayControlPaths GatewayPollStorePath GatewayInstructions GatewayCalls GatewayOperations GatewayReadonly
  GatewayPrimitiveCalls GatewayTransferMath GatewayGuardObservation GatewayStreamInterface.
Import ListNotations.

Definition ready_errno_values (temporaries : temp_env) (pointer : val) := PTree.set _t'6 pointer temporaries.
Definition ready_number_values (temporaries : temp_env) (pointer number : val) :=
  PTree.set _number number (ready_errno_values temporaries pointer).

Lemma actual_ready_errno_bind_prefix ge item temporaries pointer memory :
  gateway_retained_prefix ge
    (State f_host_ready ready_errno_bind (Kseq ready_after_errno ready_iteration_cont)
      (ready_environment item) (ready_errno_values temporaries pointer) memory)
    (Returnstate pointer (ready_errno_cont item temporaries) memory).
Proof.
  eapply gateway_prefix_next with (next := State f_host_ready Sskip
    (Kseq ready_errno_bind (Kseq ready_after_errno ready_iteration_cont))
    (ready_environment item) (ready_errno_values temporaries pointer) memory);
    [cbn; tauto | intro another; apply unchanged_store_edge, edge_returnstate |].
  eapply gateway_prefix_next with (next := State f_host_ready ready_errno_bind
    (Kseq ready_after_errno ready_iteration_cont) (ready_environment item) (ready_errno_values temporaries pointer) memory);
    [cbn; tauto | intro another; apply unchanged_store_edge, edge_skip_seq |].
  exact (gateway_prefix_reached ge _ memory).
Qed.

Theorem actual_ready_captures_errno {World Event} (backend : gateway_backend World Event) ge
    (io : Event -> option gateway_native_io) descriptor ready (discipline : gateway_runtime_discipline backend ready)
    item temporaries pointer before world events returned after next :
  ready before world ->
  gateway_steps backend ge
    (gateway_live (Returnstate pointer (ready_errno_cont item temporaries) before) world) events
    (gateway_live (Returnstate returned Kstop after) next) ->
  exists prefix suffix memory current number,
    events = prefix ++ suffix /\ gateway_received_bytes io descriptor prefix = [] /\ ready memory current /\
    eval_expr ge (ready_environment item) (ready_errno_values temporaries pointer) memory
      (Ederef (Etempvar _t'6 (tptr tint)) tint) number /\
    gateway_steps backend ge
      (gateway_live (Returnstate pointer (ready_errno_cont item temporaries) before) world) prefix
      (gateway_live (State f_host_ready Sskip (Kseq ready_after_errno ready_iteration_cont)
        (ready_environment item) (ready_number_values temporaries pointer number) memory) current) /\
    gateway_steps backend ge
      (gateway_live (State f_host_ready Sskip (Kseq ready_after_errno ready_iteration_cont)
        (ready_environment item) (ready_number_values temporaries pointer number) memory) current)
      suffix (gateway_live (Returnstate returned Kstop after) next).
Proof.
  intros READY RUN.
  destruct (gateway_quiet_prefix_cut backend ge io descriptor ready discipline _ _ before world events returned after next
    (actual_ready_errno_bind_prefix ge item temporaries pointer before) READY RUN)
    as (p & rest & m & w & EVENTS & EMPTY & PREFIX & REACHED & REST).
  destruct (gateway_set_result_cut backend ge f_host_ready _number
    (Ederef (Etempvar _t'6 (tptr tint)) tint) (Kseq ready_after_errno ready_iteration_cont)
    (ready_environment item) (ready_errno_values temporaries pointer) m w rest returned after next REST)
    as (pending & suffix & memory & current & number & REST_EVENTS & AMBIENT & PENDING & VALUE & SUFFIX).
  assert (FINAL_READY : ready memory current).
  { eapply gateway_ambient_run_ready with (source := State f_host_ready ready_errno_bind
      (Kseq ready_after_errno ready_iteration_cont) (ready_environment item) (ready_errno_values temporaries pointer) m);
      [exact discipline | exact REACHED | exact AMBIENT | exact PENDING]. }
  exists (p ++ pending ++ [gateway_source E0]), suffix, memory, current, number.
  split; [rewrite EVENTS, REST_EVENTS; repeat rewrite <- app_assoc; reflexivity |]. split.
  - repeat rewrite gateway_received_bytes_append; rewrite EMPTY.
    rewrite (gateway_pending_received_empty io descriptor pending
      ltac:(eapply Forall_impl; [|exact AMBIENT]; intros event SAME; left; exact SAME)); reflexivity.
  - split; [exact FINAL_READY |]. split; [exact VALUE |]. split; [|exact SUFFIX].
    eapply gateway_steps_append; [exact PREFIX |].
    eapply gateway_steps_append; [exact PENDING |].
    econstructor; [apply gateway_internal; [cbn; tauto | apply step_set; exact VALUE] | constructor].
Qed.
