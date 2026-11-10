(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: An actual final caller return retains rooted runtime state through local cleanup. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Ctypes Clight.
Require Import Machine ClightSteps StoreSteps.
From HostGateway Require Import GatewayMachine GatewayContexts GatewayRuntimeCuts GatewayReturnRuntime GatewayThreadRuntime
  GatewayLocalRuntime GatewayReadonly GatewayStreamInterface.
Import ListNotations.

Theorem gateway_actual_caller_return_side {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    io native stable discipline thread_errno
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    mode function destination environment temporaries expression following before world events returned value after next :
  call_cont following=Kstop ->
  gateway_return_environment native discipline mode environment before world ->
  gateway_steps backend ge
    (gateway_live(Returnstate returned(Kcall destination function environment temporaries
      (Kseq(Sreturn expression)following))before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->
  discipline mode after next /\Forall gateway_quiet_event events.
Proof.
  intros STOP READY RUN.
  pose proof(gateway_return_environment_ambient backend io native stable discipline thread_errno runtime mode environment)as CLOSED.
  destruct(gateway_uniform_edge_side_cut backend ge _ CLOSED
    (Returnstate returned(Kcall destination function environment temporaries(Kseq(Sreturn expression)following))before)
    (State function Sskip(Kseq(Sreturn expression)following)environment(set_opttemp destination returned temporaries)before)
    before world events value after next ltac:(cbn;tauto)
    ltac:(intros;apply unchanged_store_edge,edge_returnstate)READY RUN)
    as(prefix &rest &middle &current &EVENTS &AMBIENT &PREFIX &MIDDLE_READY &REST).
  destruct(gateway_uniform_edge_side_cut backend ge _ CLOSED
    (State function Sskip(Kseq(Sreturn expression)following)environment(set_opttemp destination returned temporaries)middle)
    (State function(Sreturn expression)following environment(set_opttemp destination returned temporaries)middle)
    middle current rest value after next ltac:(cbn;tauto)
    ltac:(intros;apply unchanged_store_edge,edge_skip_seq)MIDDLE_READY REST)
    as(pending &suffix &return_memory &return_world &REST_EVENTS &WAITING &TO_RETURN &RETURN_READY &FROM_RETURN).
  destruct(gateway_actual_return_side backend ge io native stable discipline thread_errno runtime mode function expression following
    environment(set_opttemp destination returned temporaries)return_memory return_world suffix value after next
    STOP RETURN_READY FROM_RETURN)as[FINAL_SIDE QUIET].
  split;[exact FINAL_SIDE|]. rewrite EVENTS,REST_EVENTS.
  apply Forall_app;split.
  - eapply Forall_impl;[|exact AMBIENT];intros event SAME;right;exact SAME.
  - constructor;[left;reflexivity|]. apply Forall_app;split.
    + eapply Forall_impl;[|exact WAITING];intros event SAME;right;exact SAME.
    + constructor;[left;reflexivity|exact QUIET].
Qed.
