(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Actual clock/pair helpers cannot contain the caller's later spawn. *)
From Stdlib Require Import ZArith List Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Clight.
Require Import Machine CallContexts.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewayRuntimeABI GatewaySpawnABI
  GatewayClosedCalls GatewayReturnBarrier GatewayContexts.
Import ListNotations.

Inductive gateway_launch_helper:=gateway_launch_clock|gateway_launch_pair.
Definition gateway_launch_function helper:=match helper with
  gateway_launch_clock=>f_host_now|gateway_launch_pair=>f_host_private_pair end.
Definition gateway_launch_calls:list(ident*Ctypes.fundef Clight.function):=
  [(_clock_gettime,gateway_clock_gettime_definition);
   (_socketpair,gateway_spawn_signature gateway_socketpair_api);
   (_leancage_host_fcntl,gateway_spawn_signature gateway_fcntl_api);
   (_close,gateway_spawn_signature gateway_close_api);
   (___errno_location,gateway_errno_location_definition)].
Definition gateway_launch_allowed identifier:=existsb(fun entry=>Pos.eqb identifier(fst entry))gateway_launch_calls.

Theorem actual_launch_helper_declarations:
  Forall(fun entry=>gateway_function_binding(Clight.globalenv prog)(fst entry)(snd entry))gateway_launch_calls.
Proof. repeat constructor;apply gateway_actual_function_binding;vm_compute;reflexivity. Qed.

Theorem actual_launch_helper_external:
  Forall(fun entry=>gateway_barrier_external(gateway_spawn_signature gateway_posix_spawn_api)(snd entry))gateway_launch_calls.
Proof.
  repeat constructor;cbn[gateway_barrier_external gateway_spawn_signature];
    try solve[repeat eexists;reflexivity];discriminate.
Qed.

Theorem actual_launch_helper_globals:
  gateway_closed_globals(Clight.globalenv prog)gateway_launch_allowed(gateway_spawn_signature gateway_posix_spawn_api).
Proof.
  intros identifier ALLOWED;unfold gateway_launch_allowed in ALLOWED;rewrite existsb_exists in ALLOWED.
  destruct ALLOWED as[entry[MEMBER EQUAL]];apply Pos.eqb_eq in EQUAL;subst identifier.
  destruct((proj1(Forall_forall _ _))actual_launch_helper_declarations entry MEMBER)as[symbol[SYMBOL FUNCTION]].
  pose proof((proj1(Forall_forall _ _))actual_launch_helper_external entry MEMBER)as OTHER.
  exists symbol,(snd entry);split;[exact SYMBOL|]. split;assumption.
Qed.

Theorem actual_launch_helper_body helper:
  gateway_closed_statement gateway_launch_allowed(fn_body(gateway_launch_function helper))=true.
Proof. destruct helper;reflexivity. Qed.

Theorem actual_launch_helper_not_local helper identifier:
  gateway_launch_allowed identifier=true->~In identifier(map fst(fn_vars(gateway_launch_function helper))).
Proof.
  unfold gateway_launch_allowed;rewrite existsb_exists.
  intros[entry[MEMBER EQUAL]];apply Pos.eqb_eq in EQUAL;subst identifier.
  cbn[gateway_launch_calls]in MEMBER.
  repeat destruct MEMBER as[SAME|MEMBER];try contradiction;subst entry;destruct helper;cbn;intuition discriminate.
Qed.

Theorem actual_launch_helper_excludes_spawn {World Event}(backend:gateway_backend World Event)
    helper arguments before world events actual_arguments actual_cont after next:
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal(gateway_launch_function helper))arguments Kstop before)world)events
    (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)actual_arguments actual_cont after)next)->False.
Proof.
  intro RUN;eapply gateway_actual_closed_helper;
    [exact actual_launch_helper_globals|apply actual_launch_helper_body|apply actual_launch_helper_not_local|
     discriminate|exact RUN].
Qed.

Theorem actual_launch_helper_return_cut {World Event}(backend:gateway_backend World Event)
    helper arguments continuation before world events actual_arguments actual_cont after next:
  is_call_cont continuation->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal(gateway_launch_function helper))arguments continuation before)world)events
    (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)actual_arguments actual_cont after)next)->
  exists prefix suffix value memory current,
    events=prefix++suffix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal(gateway_launch_function helper))arguments Kstop before)world)prefix
      (gateway_live(Returnstate value Kstop memory)current) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate value continuation memory)current)suffix
      (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)actual_arguments actual_cont after)next).
Proof.
  intros CALL RUN.
  destruct(gateway_caller_run_decomposition backend(Clight.globalenv prog)continuation
    (Callstate(Internal(gateway_launch_function helper))arguments Kstop before)world events
    (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)actual_arguments actual_cont after)next)CALL RUN)
    as[[local[LOCAL SAME]]|[prefix[suffix[value[memory[current[EVENTS[CALLEE CALLER]]]]]]]].
  - destruct local as[source current|memory current];[|discriminate SAME].
    destruct source;cbn[gateway_plug plug_state]in SAME;inversion SAME;subst.
    exfalso;eapply actual_launch_helper_excludes_spawn;exact LOCAL.
  - exists prefix,suffix,value,memory,current;split;[exact EVENTS|]. split;assumption.
Qed.
