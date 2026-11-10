(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Compose a source-proved callee with its actual retained continuation. *)
From Stdlib Require Import List Lia.
From compcert Require Import Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayContexts GatewayEffectRuntime.
Import ListNotations.

Theorem gateway_callee_return_composition {World Event}(backend:gateway_backend World Event)ge
    definition arguments continuation(initial:mem->World->Prop)(returned_context:val->mem->World->Prop)
    value(result:mem->World->Prop)before world events actual after next:
  is_call_cont continuation->(0<gateway_cont_weight continuation)%nat->
  (forall before world events returned after next,
    initial before world->
    gateway_steps backend ge(gateway_live(Callstate definition arguments Kstop before)world)events
      (gateway_live(Returnstate returned Kstop after)next)->returned_context returned after next)->
  (forall returned memory,gateway_effect_path backend ge(returned_context returned)
    (Returnstate returned continuation memory)value result)->
  initial before world->
  gateway_steps backend ge(gateway_live(Callstate definition arguments continuation before)world)events
    (gateway_live(Returnstate actual Kstop after)next)->
  exists callee_events caller_events returned returned_memory returned_world,
    events=callee_events++caller_events /\
    gateway_steps backend ge(gateway_live(Callstate definition arguments Kstop before)world)callee_events
      (gateway_live(Returnstate returned Kstop returned_memory)returned_world) /\
    returned_context returned returned_memory returned_world /\
    gateway_steps backend ge(gateway_live(Returnstate returned continuation returned_memory)returned_world)caller_events
      (gateway_live(Returnstate actual Kstop after)next) /\actual=value /\result after next.
Proof.
  intros CALL WEIGHT CALLEE CONTINUATION INITIAL RUN.
  destruct(gateway_return_cut backend ge definition arguments continuation before world events
    (Returnstate actual Kstop after)next CALL ltac:(cbn;exact WEIGHT)RUN)
    as[callee_events[caller_events[returned[returned_memory[returned_world[EVENTS[CALLEE_RUN CALLER_RUN]]]]]]].
  pose proof(CALLEE before world callee_events returned returned_memory returned_world INITIAL CALLEE_RUN)as RETURNED.
  destruct(gateway_effect_return_exact backend ge(returned_context returned)
    (Returnstate returned continuation returned_memory)value result returned_memory returned_world caller_events
    actual after next RETURNED(CONTINUATION returned returned_memory)CALLER_RUN)as[VALUE FINAL].
  exists callee_events,caller_events,returned,returned_memory,returned_world.
  split;[exact EVENTS|]. split;[exact CALLEE_RUN|]. split;[exact RETURNED|].
  split;[exact CALLER_RUN|]. split;assumption.
Qed.
