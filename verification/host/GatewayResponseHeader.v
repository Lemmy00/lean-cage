(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Source selection and the reply bytes belong to one original exchange. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewayContexts GatewayReadonly
  GatewayMemoryPrefixes GatewayFramedRuntime GatewayThreadRuntime GatewayStreamInterface GatewayReadContext
  GatewayTransportFrame GatewayTransferMath GatewayPrimitiveCalls GatewayExchangeSetup GatewayExchangeTransport GatewayResponseReturn GatewayResponseTransfer.
Import ListNotations.
Open Scope Z_scope.

Theorem actual_exchange_response_header {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    allocation_before allocated environment temporaries stream response initial readonly before world events value after next:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  environment!_stream=Some(stream,Tstruct _host_stream noattr)->environment!_response=Some(response,tarray tuchar 24)->
  temporaries!_failed=Some(Vint Int.zero)->
  gateway_read_context native stable discipline None stream Ptrofs.zero initial response Ptrofs.zero 24 readonly before world->
  value<>Vnullptr->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_exchange(exchange_transport_after 2)Kstop environment temporaries before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists prefix body suffix called called_world memory current bytes,
    events=prefix++body++suffix /\Forall gateway_quiet_event prefix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(exchange_transport_after 2)Kstop environment temporaries before)world)prefix
      (gateway_live(Callstate(Internal f_host_transfer)(response_transfer_arguments stream response)
        (response_transfer_cont environment temporaries)called)called_world) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal f_host_transfer)(response_transfer_arguments stream response)Kstop called)called_world)body
      (gateway_live(Returnstate(Vint Int.zero)Kstop memory)current) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate(Vint Int.zero)(response_transfer_cont environment temporaries)memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next) /\
    Z.of_nat(length bytes)=24 /\gateway_received_bytes io(stream_descriptor initial)(prefix++body)=bytes /\
    Mem.loadbytes memory response 0 24=Some(inj_bytes bytes) /\
    (exists final,gateway_read_context native stable discipline None stream Ptrofs.zero final response Ptrofs.zero 24 readonly memory current /\
      gateway_stream_transport_after initial final) /\
    gateway_transport_frame native readonly stream Ptrofs.zero response Ptrofs.zero 24 called called_world memory current.
Proof.
  intros ALLOC STREAM RESPONSE FAILED READY NONNULL RUN.
  set(context:=gateway_read_context native stable discipline None stream Ptrofs.zero initial response Ptrofs.zero 24 readonly).
  assert(CLOSED:gateway_ambient_closed backend context).
  { exact(gateway_read_context_ambient backend io native stable discipline thread_errno runtime None stream Ptrofs.zero initial
      response Ptrofs.zero 24 readonly). }
  assert(LOCAL:environment!_host_transfer=None).
  { eapply actual_exchange_setup_unshadowed;[exact ALLOC|cbn;intuition discriminate]. }
  assert(FUNCTION:gateway_function_binding(Clight.globalenv prog)_host_transfer(Internal f_host_transfer)).
  { apply gateway_actual_function_binding;vm_compute;reflexivity. }
  destruct(gateway_memory_prefix_cut backend(Clight.globalenv prog)_ _ _ _ before world events(Returnstate value Kstop after)next
    (actual_response_transfer_prefix backend(Clight.globalenv prog)context CLOSED environment temporaries before stream response
      FAILED STREAM RESPONSE LOCAL FUNCTION)I READY RUN)
    as(prefix&remaining&called&called_world&E1&QUIET&PREFIX&CALLED&REST).
  cbn[gateway_replace_memory]in PREFIX,REST.
  destruct(actual_successful_response_receives backend io native stable discipline thread_errno runtime environment temporaries stream response
    initial readonly called called_world remaining value after next CALLED NONNULL REST)
    as(body&suffix&memory&current&bytes&E2&BODY&SUFFIX&LENGTH&OBSERVED&LOADED&FINAL&FRAME).
  exists prefix,body,suffix,called,called_world,memory,current,bytes.
  split;[rewrite E1,E2;reflexivity|]. split;[exact QUIET|]. split;[exact PREFIX|]. split;[exact BODY|].
  split;[exact SUFFIX|]. split;[exact LENGTH|]. split.
  - rewrite gateway_received_bytes_append,(gateway_quiet_received_empty io(stream_descriptor initial)prefix QUIET);exact OBSERVED.
  - split;[exact LOADED|]. split;assumption.
Qed.
