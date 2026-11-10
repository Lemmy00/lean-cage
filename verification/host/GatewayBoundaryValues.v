(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Guard values come from the same run before its actual call. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Ctypes Cop Clight Maps.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewayMemoryPrefixes GatewayOperations GatewayFrames GatewayReadonly
  GatewayFramedRuntime GatewayCallPath GatewayCalls.
Import ListNotations.

Theorem gateway_boundary_set_cut {World Event}(backend:gateway_backend World Event)ge
    (property:mem->World->Prop)(CLOSED:gateway_ambient_closed backend property)
    function identifier expression continuation environment temporaries before world events terminal next:
  gateway_instruction_boundary terminal->property before world->
  gateway_steps backend ge
    (gateway_live(State function(Sset identifier expression)continuation environment temporaries before)world)events
    (gateway_live terminal next)->
  exists prefix suffix memory current value,
    events=prefix++gateway_source E0::suffix /\Forall(fun event=>event=gateway_ambient)prefix /\
    gateway_steps backend ge
      (gateway_live(State function(Sset identifier expression)continuation environment temporaries before)world)prefix
      (gateway_live(State function(Sset identifier expression)continuation environment temporaries memory)current) /\
    eval_expr ge environment temporaries memory expression value /\property memory current /\
    gateway_steps backend ge
      (gateway_live(State function Sskip continuation environment(PTree.set identifier value temporaries)memory)current)
      suffix(gateway_live terminal next).
Proof.
  intros BOUNDARY READY RUN.
  destruct(gateway_source_instruction_before_boundary backend ge function(Sset identifier expression)continuation
    environment temporaries before world events terminal next BOUNDARY ltac:(cbn;tauto)RUN)
    as(prefix & suffix & memory & current & trace & target & EVENTS & AMBIENT & PREFIX & REAL & SUFFIX).
  assert(CALLED:property memory current).
  { eapply gateway_ambient_run_ready with(source:=State function(Sset identifier expression)continuation environment temporaries before);
      [exact CLOSED|exact READY|exact AMBIENT|exact PREFIX]. }
  inversion REAL;subst;try match goal with BAD:_=_\/_=_|-_=>destruct BAD;discriminate end.
  match goal with VALUE:eval_expr _ _ _ _ expression ?value|-_=>exists prefix,suffix,memory,current,value end.
  repeat split;assumption.
Qed.

Theorem gateway_boundary_if_cut {World Event}(backend:gateway_backend World Event)ge
    (property:mem->World->Prop)(CLOSED:gateway_ambient_closed backend property)
    function expression yes no continuation environment temporaries before world events terminal next:
  gateway_instruction_boundary terminal->property before world->
  gateway_steps backend ge
    (gateway_live(State function(Sifthenelse expression yes no)continuation environment temporaries before)world)events
    (gateway_live terminal next)->
  exists prefix suffix memory current value branch,
    events=prefix++gateway_source E0::suffix /\Forall(fun event=>event=gateway_ambient)prefix /\
    gateway_steps backend ge
      (gateway_live(State function(Sifthenelse expression yes no)continuation environment temporaries before)world)prefix
      (gateway_live(State function(Sifthenelse expression yes no)continuation environment temporaries memory)current) /\
    eval_expr ge environment temporaries memory expression value /\bool_val value(typeof expression)memory=Some branch /\
    property memory current /\gateway_steps backend ge
      (gateway_live(State function(if branch then yes else no)continuation environment temporaries memory)current)suffix
      (gateway_live terminal next).
Proof.
  intros BOUNDARY READY RUN.
  destruct(gateway_source_instruction_before_boundary backend ge function(Sifthenelse expression yes no)continuation
    environment temporaries before world events terminal next BOUNDARY ltac:(cbn;tauto)RUN)
    as(prefix & suffix & memory & current & trace & target & EVENTS & AMBIENT & PREFIX & REAL & SUFFIX).
  assert(CALLED:property memory current).
  { eapply gateway_ambient_run_ready with(source:=State function(Sifthenelse expression yes no)continuation environment temporaries before);
      [exact CLOSED|exact READY|exact AMBIENT|exact PREFIX]. }
  inversion REAL;subst;try match goal with BAD:_=_\/_=_|-_=>destruct BAD;discriminate end.
  match goal with VALUE:eval_expr _ _ _ _ expression ?value,BOOL:bool_val ?value _ _=Some ?branch|-_=>
    exists prefix,suffix,memory,current,value,branch end.
  repeat split;assumption.
Qed.
