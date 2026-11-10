(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual reserved header word is decoded only after the preceding source guards. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewayContexts GatewayReadonly GatewaySourcePaths
  GatewayFramedRuntime GatewayReadContext GatewayThreadRuntime GatewayStreamInterface GatewayExchangeSetup GatewayResponseReturn
  GatewayResponseWord GatewayResponseStatusSource GatewayResponseLengthSource GatewayResponseCompareSource GatewayResponseReservedSource.
Import ListNotations.

Theorem actual_response_reserved_from_compare {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    allocation_before allocated environment temporaries status stream response initial readonly bytes before world events value after next:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  environment!_response=Some(response,tarray tuchar 24)->Z.of_nat(length bytes)=24->
  temporaries!_status=Some(Vlong status)->Int64.unsigned status<=3->
  gateway_response_context native stable discipline stream response readonly initial bytes before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate(Vint Int.zero)(response_compare_cont environment temporaries)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists prefix body suffix called called_world memory current,
    events=prefix++body++suffix /\Forall gateway_quiet_event(prefix++body) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate(Vint Int.zero)(response_compare_cont environment temporaries)before)world)prefix
      (gateway_live(Callstate(Internal f_host_get64)(response_reserved_arguments response)
        (response_reserved_cont environment(response_reserved_temps temporaries))called)called_world) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal f_host_get64)(response_reserved_arguments response)Kstop called)called_world)body
      (gateway_live(Returnstate(gateway_response_word_value bytes 12 4)Kstop memory)current) /\
    gateway_response_context native stable discipline stream response readonly initial bytes memory current /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate(gateway_response_word_value bytes 12 4)
        (response_reserved_cont environment(response_reserved_temps temporaries))memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros ALLOC RESPONSE LENGTH STATUS SMALL READY RUN.
  set(context:=gateway_response_context native stable discipline stream response readonly initial bytes).
  assert(CLOSED:gateway_ambient_closed backend context).
  { exact(gateway_response_context_ambient backend io native stable discipline thread_errno runtime stream response readonly initial bytes). }
  assert(LOCAL:environment!_host_get64=None).
  { eapply actual_exchange_setup_unshadowed;[exact ALLOC|cbn;intuition discriminate]. }
  assert(FUNCTION:gateway_function_binding(Clight.globalenv prog)_host_get64(Internal f_host_get64)).
  { apply gateway_actual_function_binding;vm_compute;reflexivity. }
  destruct(gateway_source_path_cut backend(Clight.globalenv prog)(Internal f_host_get64)(response_reserved_arguments response)
    (response_reserved_cont environment(response_reserved_temps temporaries))context
    (Returnstate(Vint Int.zero)(response_compare_cont environment temporaries)before)context
    (actual_response_reserved_path backend(Clight.globalenv prog)context CLOSED environment temporaries before response status RESPONSE LOCAL FUNCTION STATUS SMALL)
    before world events value after next READY RUN)
    as(prefix&remaining&called&called_world&E1&QUIET&PREFIX&CALLED&REST).
  cbn[gateway_replace_memory]in PREFIX.
  destruct(gateway_return_cut backend(Clight.globalenv prog)(Internal f_host_get64)(response_reserved_arguments response)
    (response_reserved_cont environment(response_reserved_temps temporaries))called called_world remaining(Returnstate value Kstop after)next
    I ltac:(cbn;lia)REST)as(body&suffix&returned&memory&current&E2&BODY&SUFFIX).
  destruct(gateway_actual_response_word backend io native stable discipline thread_errno runtime stream response readonly initial bytes
    12 4 called called_world body returned memory current LENGTH ltac:(lia)ltac:(lia)CALLED BODY)
    as[RETURNED[FINAL BODY_QUIET]];subst returned.
  exists prefix,body,suffix,called,called_world,memory,current.
  split;[rewrite E1,E2;reflexivity|]. split;[apply Forall_app;split;assumption|].
  split;[exact PREFIX|]. split;[exact BODY|]. split;assumption.
Qed.
