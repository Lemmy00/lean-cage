(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The selected original spawn exposes this exchange's real stack
   allocation. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayThreadRuntime GatewayStreamInterface GatewayCalls
  GatewayFunctionFrontier GatewayExchangeEntry GatewaySpawnABI GatewayLocalRuntime GatewayFramedRuntime GatewayContexts.
Import ListNotations.

Theorem actual_exchange_selected_allocates {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
    (native:World->block->Prop)(stable:World->block->BinNums.Z->Prop)(discipline:option val->mem->World->Prop)
    thread_errno(thread:gateway_thread_runtime backend io native stable discipline thread_errno)
    fields command fault cancellation cli before world events arguments continuation after next:
  discipline None before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_exchange)[fields;Vint command;Vint fault;cancellation;Vint cli]Kstop before)world)events
    (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next)->
  exists prefix suffix called current environment allocated,
    events=prefix++gateway_source E0::suffix /\Forall(fun event=>event=gateway_ambient)prefix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal f_host_exchange)[fields;Vint command;Vint fault;cancellation;Vint cli]Kstop before)world)prefix
      (gateway_live(Callstate(Internal f_host_exchange)[fields;Vint command;Vint fault;cancellation;Vint cli]Kstop called)current) /\
    function_entry2(Clight.globalenv prog)f_host_exchange[fields;Vint command;Vint fault;cancellation;Vint cli]called
      environment(exchange_parameters fields command fault cancellation cli)allocated /\
    alloc_variables(Clight.globalenv prog)empty_env called(fn_vars f_host_exchange)environment allocated /\
    exchange_stack_buffers(Clight.globalenv prog)called environment allocated /\
    discipline None allocated current /\gateway_native_environment native current allocated environment /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(fn_body f_host_exchange)Kstop environment
        (exchange_parameters fields command fault cancellation cli)allocated)current)suffix
      (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next).
Proof.
  intros SIDE RUN.
  destruct(gateway_actual_function_entry_before_call backend(Clight.globalenv prog)f_host_exchange
    [fields;Vint command;Vint fault;cancellation;Vint cli]Kstop before world events
    (gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after next ltac:(discriminate)RUN)
    as(prefix&suffix&called&current&environment&temporaries&allocated&EVENTS&AMBIENT&PREFIX&ENTRY&REST).
  assert(CALLED:discipline None called current).
  { eapply gateway_ambient_run_ready with(source:=Callstate(Internal f_host_exchange)
      [fields;Vint command;Vint fault;cancellation;Vint cli]Kstop before);
      [|exact SIDE|exact AMBIENT|exact PREFIX].
    intros original owner changed target READY INTERFERENCE.
    exact(proj1(gateway_thread_ambient _ _ _ _ _ _ thread None _ _ _ _ READY INTERFERENCE)). }
  destruct(actual_exchange_entry_canonical(Clight.globalenv prog)fields command fault cancellation cli called environment
    temporaries allocated ENTRY)as[TEMPS ALLOC];subst temporaries.
  destruct(gateway_native_alloc_variables backend io native stable discipline thread_errno thread(Clight.globalenv prog)None
    empty_env called(fn_vars f_host_exchange)environment allocated current ALLOC CALLED
    (gateway_native_environment_empty native current called))as[ALLOCATED NATIVE].
  exists prefix,suffix,called,current,environment,allocated.
  split;[exact EVENTS|]. split;[exact AMBIENT|]. split;[exact PREFIX|]. split;[exact ENTRY|].
  split;[exact ALLOC|]. split;[apply actual_exchange_allocations;exact ALLOC|].
  split;[exact ALLOCATED|]. split;[exact NATIVE|exact REST].
Qed.
