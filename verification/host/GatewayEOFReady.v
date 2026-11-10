(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: The same EOF source prefix contains a real successful readiness
   call. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewayContexts GatewayReadonly GatewayFramedRuntime
  GatewaySourcePaths GatewayReturnTypes GatewayExchangeTransport GatewayEOFSource GatewayEOFReadyReturn.
Import ListNotations.
Open Scope Z_scope.

Theorem actual_eof_first_ready {World Event}(backend:gateway_backend World Event)ge property
    (CLOSED:gateway_ambient_closed backend property)environment temporaries stream object offset before world events value after next:
  environment!_stream=Some(stream,Tstruct _host_stream noattr)->environment!_host_ready=None->
  gateway_function_binding ge _host_ready(Internal f_host_ready)->temporaries!_result=Some(Vptr object offset)->
  (forall memory current,property memory current->Mem.weak_valid_pointer memory object(Ptrofs.unsigned offset)=true)->
  property before world->value<>Vnullptr->
  gateway_steps backend ge
    (gateway_live(State f_host_exchange(exchange_transport_after 7)Kstop environment temporaries before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists prefix body suffix called called_world memory current,
    events=prefix++body++suffix /\Forall gateway_quiet_event prefix /\
    gateway_steps backend ge
      (gateway_live(State f_host_exchange(exchange_transport_after 7)Kstop environment temporaries before)world)prefix
      (gateway_live(Callstate(Internal f_host_ready)(exchange_eof_ready_arguments stream)
        (exchange_eof_ready_cont environment temporaries)called)called_world) /\
    property called called_world /\
    gateway_steps backend ge
      (gateway_live(Callstate(Internal f_host_ready)(exchange_eof_ready_arguments stream)Kstop called)called_world)body
      (gateway_live(Returnstate(Vint Int.zero)Kstop memory)current) /\
    gateway_steps backend ge
      (gateway_live(Returnstate(Vint Int.zero)(exchange_eof_ready_cont environment temporaries)memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros STREAM LOCAL FUNCTION RESULT POINTER READY NONNULL RUN.
  destruct(gateway_source_path_cut backend ge(Internal f_host_ready)(exchange_eof_ready_arguments stream)
    (exchange_eof_ready_cont environment temporaries)property _ property
    (actual_eof_enter_ready_path backend ge property CLOSED environment temporaries before stream object offset
      STREAM LOCAL FUNCTION RESULT POINTER)before world events value after next READY RUN)
    as(prefix&rest&called&called_world&EVENTS&QUIET&PREFIX&CALLED&REST).
  destruct(gateway_return_cut backend ge(Internal f_host_ready)(exchange_eof_ready_arguments stream)
    (exchange_eof_ready_cont environment temporaries)called called_world rest(Returnstate value Kstop after)next I ltac:(cbn;lia)REST)
    as(body&suffix&returned&memory&current&TAIL&BODY&SUFFIX).
  pose proof(gateway_actual_int_return backend ge f_host_ready(exchange_eof_ready_arguments stream)called called_world body
    returned memory current actual_host_ready_return_profile BODY)as TYPE.
  pose proof(actual_successful_eof_ready_return backend ge environment temporaries memory current suffix returned value after next
    TYPE NONNULL SUFFIX)as ZERO;subst returned.
  exists prefix,body,suffix,called,called_world,memory,current.
  split;[rewrite EVENTS,TAIL;reflexivity|]. split;[exact QUIET|]. split;[exact PREFIX|].
  split;[exact CALLED|]. split;assumption.
Qed.
