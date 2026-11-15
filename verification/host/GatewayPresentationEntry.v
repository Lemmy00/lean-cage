(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The real callback helper entry binds the source callable and
   one-element array. *)
From Stdlib Require Import List.
From compcert Require Import Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayFunctionEntry GatewayNoLocalEntry GatewayFramedRuntime GatewayContexts GatewayCalls.
Import ListNotations.

Lemma gateway_presentation_entry_parameters ge callable array before environment parameters allocated:
  function_entry2 ge f_host_call_objects[callable;array;Vint Int.one]before environment parameters allocated ->
  parameters!_callable=Some callable /\parameters!_values=Some array /\parameters!_count=Some(Vint Int.one).
Proof.
  intro ENTRY;inversion ENTRY;subst.
  match goal with BIND:bind_parameter_temps _ _ _=Some _|-_=>
    let initial:=constr:(create_undef_temps(fn_temps f_host_call_objects))in
    change(Some(PTree.set _count(Vint Int.one)(PTree.set _values array(PTree.set _callable callable initial)))=Some parameters)in BIND;
    inversion BIND;subst parameters end.
  split;[repeat rewrite PTree.gso by discriminate;apply PTree.gss|]. split;[rewrite PTree.gso by discriminate;apply PTree.gss|apply PTree.gss].
Qed.

Theorem gateway_actual_presentation_entry {World Event}(backend:gateway_backend World Event)ge
    (property:mem->World->Prop)callable array before world events value after next:
  gateway_ambient_closed backend property ->property before world ->
  gateway_steps backend ge(gateway_live(Callstate(Internal f_host_call_objects)[callable;array;Vint Int.one]Kstop before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->
  exists prefix suffix memory current parameters,
    events=prefix++suffix /\
    gateway_steps backend ge(gateway_live(Callstate(Internal f_host_call_objects)[callable;array;Vint Int.one]Kstop before)world)prefix
      (gateway_live(State f_host_call_objects(fn_body f_host_call_objects)Kstop empty_env parameters memory)current) /\
    property memory current /\parameters!_callable=Some callable /\parameters!_values=Some array /\parameters!_count=Some(Vint Int.one) /\
    gateway_steps backend ge(gateway_live(State f_host_call_objects(fn_body f_host_call_objects)Kstop empty_env parameters memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros CLOSED INPUT RUN.
  destruct(actual_gateway_function_entry_ambient backend ge f_host_call_objects[callable;array;Vint Int.one]Kstop
    before world events value Kstop after next RUN)
    as(pending &suffix &memory &current &environment &parameters &allocated &EVENTS &AMBIENT &PREFIX &ENTRY &REST).
  destruct(gateway_presentation_entry_parameters _ _ _ _ _ _ _ ENTRY)as[CALLABLE[ARRAY COUNT]].
  destruct(gateway_no_local_entry ge f_host_call_objects[callable;array;Vint Int.one]memory environment parameters allocated eq_refl ENTRY)
    as[ENV SAME];subst environment allocated.
  assert(READY:property memory current).
  { exact(gateway_ambient_run_ready backend ge property CLOSED
      (Callstate(Internal f_host_call_objects)[callable;array;Vint Int.one]Kstop before)
      before world pending memory current INPUT AMBIENT PREFIX). }
  exists(pending++[gateway_source E0]),suffix,memory,current,parameters.
  split;[rewrite EVENTS,<-app_assoc;reflexivity|]. split.
  - eapply gateway_steps_append;[exact PREFIX|]. econstructor;[apply gateway_internal;[exact I|apply step_internal_function;exact ENTRY]|constructor].
  - exact(conj READY(conj CALLABLE(conj ARRAY(conj COUNT REST)))).
Qed.
