(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The original launch consumes the actual clock and retained caller state. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayBindings GatewayRuntimeABI
  GatewayThreadRuntime GatewayStreamInterface GatewayFramedRuntime GatewayReadonly GatewaySpawnABI
  GatewaySpawnRuntime GatewaySpawnResources GatewayPassiveResources GatewayExchangeSetup GatewayExchangeClockPaths
  GatewayExchangeContext GatewayLaunchHelpers GatewayLaunchQuiet GatewayCallerClockResources GatewayPrimitiveCalls GatewayTransferMath.
Import ListNotations.

Section ExchangeClock.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
    (native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
    (discipline:option val->mem->World->Prop)(thread_errno:World->int)
    (resources:World->gateway_resource_state)(ipc:nat->Prop).
Context(thread:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno)
    (descriptors:gateway_spawn_descriptor_runtime backend io native_private stable_readonly discipline resources ipc)
    (passive:gateway_passive_resource_runtime backend resources).
Variables(readonly:block->Z->Prop)(selected:block->Prop)(reference:mem)(owner:World)(original:gateway_resource_state).
Local Definition context:=gateway_exchange_context native_private stable_readonly discipline resources
  readonly selected reference owner original.
Local Lemma context_closed:gateway_ambient_closed backend context.
Proof. apply gateway_exchange_context_ambient with(io:=io)(thread_errno:=thread_errno)(ipc:=ipc);assumption. Qed.

Theorem actual_exchange_clock_before_data_pair allocation_before allocated environment temporaries data
    before world events arguments continuation after next descriptor:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  environment!_pair=Some(data,tarray tint 2)->(exists object,selected object)->context before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_exchange(exchange_setup_after 0)Kstop environment temporaries before)world)events
    (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next)->
  exists prefix clock_events between suffix called clock_world value clock_after returned_world pair_before pair_world,
    events=prefix++clock_events++between++suffix /\
    Forall gateway_quiet_event prefix /\Forall gateway_quiet_event between /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(exchange_setup_after 0)Kstop environment temporaries before)world)prefix
      (gateway_live(Callstate(Internal f_host_now)[](exchange_clock_cont environment temporaries)called)clock_world) /\
    context called clock_world /\
    gateway_steps backend(Clight.globalenv prog)(gateway_live(Callstate(Internal f_host_now)[]Kstop called)clock_world)
      clock_events(gateway_live(Returnstate value Kstop clock_after)returned_world) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate value(exchange_clock_cont environment temporaries)clock_after)returned_world)between
      (gateway_live(Callstate(Internal f_host_private_pair)[Vptr data Ptrofs.zero]
        (exchange_first_pair_cont environment(exchange_clock_temps value temporaries))pair_before)pair_world) /\
    exchange_clock_truth value=Some true /\context pair_before pair_world /\
    gateway_received_bytes io descriptor(prefix++clock_events++between)=[] /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal f_host_private_pair)[Vptr data Ptrofs.zero]
        (exchange_first_pair_cont environment(exchange_clock_temps value temporaries))pair_before)pair_world)suffix
      (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next).
Proof.
  intros ALLOC ARRAY NONEMPTY INITIAL RUN.
  destruct(gateway_actual_function_binding _host_now(Internal f_host_now)ltac:(vm_compute;reflexivity))
    as[symbol[SYMBOL FUNCTION]].
  assert(UNSHADOWED:environment!_host_now=None).
  { eapply actual_exchange_setup_unshadowed;[exact ALLOC|cbn;intuition discriminate]. }
  pose proof(actual_exchange_clock_call_script backend context context_closed environment temporaries before
    symbol UNSHADOWED SYMBOL FUNCTION)as FIRST.
  destruct(gateway_quiet_launch_cut backend(exchange_clock_point context environment temporaries)context
    (State f_host_exchange(exchange_setup_after 0)Kstop environment temporaries before)before world events
    arguments continuation after next FIRST INITIAL RUN)
    as(prefix&rest&clock_source&clock_world&EVENTS&QUIET_PREFIX&PREFIX&POINT&REST).
  destruct POINT as[called[SOURCE CALLED]];subst clock_source.
  destruct(actual_launch_helper_return_cut backend gateway_launch_clock[](exchange_clock_cont environment temporaries)
    called clock_world rest arguments continuation after next ltac:(exact I)REST)
    as(clock_events&following&value&clock_after&returned_world&REST_EVENTS&CLOCK&CALLER).
  destruct(actual_exchange_clock_context backend io native_private stable_readonly discipline thread_errno resources ipc
    thread descriptors passive readonly selected reference owner original called clock_world clock_events value
    clock_after returned_world descriptor NONEMPTY CALLED CLOCK)as[RETURNED EMPTY_CLOCK].
  pose proof(actual_exchange_clock_return_script backend context context_closed environment temporaries clock_after
    allocation_before allocated data value ALLOC ARRAY)as GUARD.
  destruct(gateway_quiet_launch_cut backend(exchange_first_pair_point context environment temporaries data value)context
    (Returnstate value(exchange_clock_cont environment temporaries)clock_after)clock_after returned_world following
    arguments continuation after next GUARD RETURNED CALLER)
    as(between&suffix&pair_source&pair_world&FOLLOWING&QUIET_BETWEEN&BETWEEN&PAIR_POINT&SUFFIX).
  destruct PAIR_POINT as[pair_before[SOURCE[NONZERO PAIR_CONTEXT]]];subst pair_source.
  exists prefix,clock_events,between,suffix,called,clock_world,value,clock_after,returned_world,pair_before,pair_world.
  split;[rewrite EVENTS,REST_EVENTS,FOLLOWING;repeat rewrite <-app_assoc;reflexivity|].
  split;[exact QUIET_PREFIX|]. split;[exact QUIET_BETWEEN|]. split;[exact PREFIX|].
  split;[exact CALLED|]. split;[exact CLOCK|]. split;[exact BETWEEN|]. split;[exact NONZERO|].
  split;[exact PAIR_CONTEXT|]. split;[|exact SUFFIX].
  repeat rewrite gateway_received_bytes_append.
  rewrite(gateway_quiet_received_empty io descriptor prefix QUIET_PREFIX),EMPTY_CLOCK,
    (gateway_quiet_received_empty io descriptor between QUIET_BETWEEN);reflexivity.
Qed.
End ExchangeClock.
