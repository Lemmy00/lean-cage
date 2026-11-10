(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: A real source assignment changes memory without changing caller temporaries. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewayCalls GatewayFrames GatewayMemoryPrefixes.
Import ListNotations.

Theorem gateway_actual_assignment_cut {World Event} (backend : gateway_backend World Event) ge
    function left right continuation environment parameters before world events value after next :
  gateway_steps backend ge
    (gateway_live (State function (Sassign left right) continuation environment parameters before) world) events
    (gateway_live (Returnstate value Kstop after) next) ->
  exists prefix suffix memory owner trace changed,
    events = prefix ++ gateway_source trace :: suffix /\
    Forall (fun event => event = gateway_ambient) prefix /\
    gateway_steps backend ge
      (gateway_live (State function (Sassign left right) continuation environment parameters before) world) prefix
      (gateway_live (State function (Sassign left right) continuation environment parameters memory) owner) /\
    gateway_steps backend ge
      (gateway_live (State function Sskip continuation environment parameters changed) owner) suffix
      (gateway_live (Returnstate value Kstop after) next).
Proof.
  intro RUN.
  destruct (gateway_source_instruction_before_boundary backend ge function (Sassign left right) continuation
    environment parameters before world events (Returnstate value Kstop after) next I ltac:(cbn; tauto) RUN)
    as (prefix & suffix & memory & owner & trace & target & EVENTS & QUIET & PREFIX & REAL & REST).
  inversion REAL; subst;
    try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
  do 6 eexists; repeat split; eassumption.
Qed.
