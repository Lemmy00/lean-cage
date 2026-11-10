(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A later source frontier cannot retain an earlier callee's marker. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Clight.
Require Import Machine CallContexts.
From HostGateway Require Import GatewayMachine GatewayContexts.
Import ListNotations.

Fixpoint gateway_return_marker(destination:option ident)(continuation:cont):Prop:=
  match continuation with
  |Kstop=>False
  |Kseq _ rest|Kloop1 _ _ rest|Kloop2 _ _ rest|Kswitch rest=>gateway_return_marker destination rest
  |Kcall selected _ _ _ rest=>selected=destination\/gateway_return_marker destination rest
  end.

Lemma gateway_plug_retains_marker destination local suffix:
  gateway_return_marker destination suffix->gateway_return_marker destination(plug_cont local suffix).
Proof. induction local;cbn;intuition. Qed.

Theorem gateway_marked_return_cut {World Event}(backend:gateway_backend World Event)ge
    definition arguments suffix destination before world events target next:
  is_call_cont suffix->gateway_return_marker destination suffix->
  ~gateway_return_marker destination(gateway_continuation target)->
  gateway_steps backend ge(gateway_live(Callstate definition arguments suffix before)world)events
    (gateway_live target next)->
  exists prefix rest returned memory current,
    events=prefix++rest /\
    gateway_steps backend ge(gateway_live(Callstate definition arguments Kstop before)world)prefix
      (gateway_live(Returnstate returned Kstop memory)current) /\
    gateway_steps backend ge(gateway_live(Returnstate returned suffix memory)current)rest
      (gateway_live target next).
Proof.
  intros CALL MARKER ABSENT RUN.
  destruct(gateway_caller_run_decomposition backend ge suffix
    (Callstate definition arguments Kstop before)world events(gateway_live target next)CALL RUN)
    as[[local[LOCAL SAME]]|[prefix[rest[returned[memory[current[EVENTS[BODY SUFFIX]]]]]]]].
  - exfalso;destruct local as[source owner|memory owner];cbn in SAME;try discriminate.
    inversion SAME;subst target next.
    apply ABSENT;rewrite gateway_continuation_plug;apply gateway_plug_retains_marker;exact MARKER.
  - exists prefix,rest,returned,memory,current;auto.
Qed.
