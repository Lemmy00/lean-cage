(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A later selected spawn forces both actual pair return guards to pass. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayFramedRuntime GatewayPure
  GatewaySpawnABI GatewayLaunchHelpers GatewayLaunchQuiet GatewayExchangePairPaths GatewayReturnTypes.
Import ListNotations.

Theorem actual_exchange_pair_returns_zero_before_spawn {World Event}(backend:gateway_backend World Event)
    stage environment temporaries object allocation_before allocated before world events arguments continuation after next:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_private_pair)[Vptr object Ptrofs.zero]
      (exchange_pair_cont stage environment temporaries)before)world)events
    (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next)->
  exists pair_events caller_events returned_memory returned_world,
    events=pair_events++caller_events /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal f_host_private_pair)[Vptr object Ptrofs.zero]Kstop before)world)pair_events
      (gateway_live(Returnstate(Vint Int.zero)Kstop returned_memory)returned_world) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate(Vint Int.zero)(exchange_pair_cont stage environment temporaries)returned_memory)returned_world)
      caller_events(gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next).
Proof.
  intros ALLOC RUN.
  destruct(actual_launch_helper_return_cut backend gateway_launch_pair[Vptr object Ptrofs.zero]
    (exchange_pair_cont stage environment temporaries)before world events arguments continuation after next ltac:(exact I)RUN)
    as(pair_events&caller_events&returned&returned_memory&returned_world&EVENTS&PAIR&CALLER).
  pose proof(gateway_actual_int_return backend(Clight.globalenv prog)f_host_private_pair[Vptr object Ptrofs.zero]
    before world pair_events returned returned_memory returned_world actual_exchange_pair_return_profile PAIR)as TYPE.
  set(target:=fun(source:Clight.state)(current:World)=>returned=Vint Int.zero).
  assert(SCRIPT:gateway_quiet_launch_path backend target(fun _ _=>True)
    (Returnstate returned(exchange_pair_cont stage environment temporaries)returned_memory)).
  { eapply actual_exchange_pair_return_script;[unfold gateway_ambient_closed;intros;exact I|exact ALLOC|exact TYPE|].
    intros ZERO;apply gateway_quiet_launch_reached;intros;exact ZERO. }
  destruct(gateway_quiet_launch_cut backend target(fun _ _=>True)
    (Returnstate returned(exchange_pair_cont stage environment temporaries)returned_memory)
    returned_memory returned_world caller_events arguments continuation after next SCRIPT I CALLER)
    as(prefix&suffix&selected&current&TAIL_EVENTS&QUIET&PREFIX&ZERO&SUFFIX).
  change(returned=Vint Int.zero)in ZERO;subst returned.
  exists pair_events,caller_events,returned_memory,returned_world;split;[exact EVENTS|]. split;assumption.
Qed.
