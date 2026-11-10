(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Header helpers return before the caller's later transfer. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Ctypes Clight.
Require Import Machine CallContexts.
From HostGateway Require Import GatewaySource GatewayMachine GatewayClosedCalls
  GatewayReturnBarrier GatewayContexts.
Import ListNotations.

Inductive gateway_header_writer:=gateway_header32|gateway_header64.
Definition gateway_header_function writer:=match writer with
  gateway_header32=>f_host_put32|gateway_header64=>f_host_put64 end.

Lemma gateway_header_helper_closed writer:
  gateway_closed_statement(fun _=>false)(fn_body(gateway_header_function writer))=true.
Proof. destruct writer;reflexivity. Qed.

Theorem gateway_header_helper_return_cut {World Event}(backend:gateway_backend World Event)ge
    writer arguments continuation before world events target arguments_after target_cont after next:
  is_call_cont continuation->target<>Internal(gateway_header_function writer)->
  gateway_steps backend ge
    (gateway_live(Callstate(Internal(gateway_header_function writer))arguments continuation before)world)events
    (gateway_live(Callstate target arguments_after target_cont after)next)->
  exists prefix suffix value memory current,
    events=prefix++suffix /\
    gateway_steps backend ge
      (gateway_live(Callstate(Internal(gateway_header_function writer))arguments Kstop before)world)prefix
      (gateway_live(Returnstate value Kstop memory)current) /\
    gateway_steps backend ge
      (gateway_live(Returnstate value continuation memory)current)suffix
      (gateway_live(Callstate target arguments_after target_cont after)next).
Proof.
  intros CALL DIFFERENT RUN.
  destruct(gateway_caller_run_decomposition backend ge continuation
    (Callstate(Internal(gateway_header_function writer))arguments Kstop before)world events
    (gateway_live(Callstate target arguments_after target_cont after)next)CALL RUN)
    as[[local[LOCAL SAME]]|[prefix[suffix[value[memory[current[EVENTS[CALLEE CALLER]]]]]]]].
  - destruct local as[source current|memory current];[|discriminate SAME].
    destruct source;cbn[gateway_plug plug_state]in SAME;inversion SAME;subst.
    exfalso;eapply gateway_actual_closed_helper with(allowed:=fun _=>false);
      [intros identifier IMPOSSIBLE;discriminate|apply gateway_header_helper_closed
      |intros identifier IMPOSSIBLE;discriminate|exact DIFFERENT|exact LOCAL].
  - exists prefix,suffix,value,memory,current;split;[exact EVENTS|]. split;assumption.
Qed.
