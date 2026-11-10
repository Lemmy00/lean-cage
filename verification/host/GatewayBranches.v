(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Select a branch from the actual evaluated source condition. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Ctypes Cop Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewayInstructions GatewayCalls GatewayOperations.
Import ListNotations.

Theorem gateway_actual_branch {World Event} (backend : gateway_backend World Event) ge
    ready (discipline : gateway_runtime_discipline backend ready) function condition yes no continuation
    environment temporaries before world events returned after next :
  ready before world ->
  gateway_steps backend ge
    (gateway_live (State function (Sifthenelse condition yes no) continuation environment temporaries before) world)
    events (gateway_live (Returnstate returned Kstop after) next) ->
  exists prefix suffix memory current value branch,
    events = prefix ++ gateway_source E0 :: suffix /\
    Forall (fun event => event = gateway_ambient) prefix /\ ready memory current /\
    eval_expr ge environment temporaries memory condition value /\ bool_val value (typeof condition) memory = Some branch /\
    gateway_steps backend ge
      (gateway_live (State function (Sifthenelse condition yes no) continuation environment temporaries before) world)
      prefix (gateway_live (State function (Sifthenelse condition yes no) continuation environment temporaries memory) current) /\
    gateway_steps backend ge
      (gateway_live (State function (if branch then yes else no) continuation environment temporaries memory) current)
      suffix (gateway_live (Returnstate returned Kstop after) next).
Proof.
  intros READY RUN.
  destruct (gateway_source_instruction_occurrence backend ge function (Sifthenelse condition yes no) continuation
    environment temporaries before world events returned after next ltac:(cbn; tauto) RUN)
    as (prefix & suffix & memory & current & trace & target & EVENTS & AMBIENT & PREFIX & REAL & SUFFIX).
  assert (CALLED : ready memory current).
  { eapply gateway_ambient_run_ready with
      (source := State function (Sifthenelse condition yes no) continuation environment temporaries before);
      [exact discipline | exact READY | exact AMBIENT | exact PREFIX]. }
  inversion REAL; subst;
    try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
  exists prefix, suffix, memory, current, v1, b.
  split; [reflexivity |]. split; [exact AMBIENT |]. split; [exact CALLED |].
  split; [assumption |]. split; [assumption |]. split; assumption.
Qed.
