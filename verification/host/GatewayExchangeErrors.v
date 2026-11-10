(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Real setup-error branches return before the same exchange can spawn. *)
From Stdlib Require Import ZArith List Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewayRuntimeABI GatewaySpawnABI
  GatewayExchangeSetup GatewayReturnBarrier.
Import ListNotations.

Definition exchange_error_calls:list(ident*Ctypes.fundef Clight.function):=
  [(___errno_location,gateway_errno_location_definition);
   (_close,gateway_spawn_signature gateway_close_api);
   (_PyErr_SetString,gateway_set_error_definition);
   (_PyErr_SetFromErrno,gateway_errno_error_definition);
   (_posix_spawn_file_actions_destroy,gateway_spawn_signature gateway_actions_destroy_api);
   (_posix_spawnattr_destroy,gateway_spawn_signature gateway_attributes_destroy_api)].

Definition exchange_error_allowed(identifier:ident):bool:=
  existsb(fun entry=>Pos.eqb identifier(fst entry))exchange_error_calls.

Definition exchange_guard_failure(body:statement):statement:=
  match body with
  |Sifthenelse _ failed _=>failed
  |Ssequence _(Sifthenelse _ failed _)=>failed
  |_=>Sskip
  end.

Definition exchange_early_errors:list statement:=
  map exchange_guard_failure[exchange_clock_guard;exchange_data_pair;exchange_control_pair;
    exchange_flags_guard;exchange_actions_guard;exchange_attributes_guard].

Theorem actual_exchange_error_declarations:
  Forall(fun entry=>gateway_function_binding(Clight.globalenv prog)(fst entry)(snd entry))exchange_error_calls.
Proof. repeat constructor;apply gateway_actual_function_binding;vm_compute;reflexivity. Qed.

Theorem actual_exchange_error_external:
  Forall(fun entry=>gateway_barrier_external(gateway_spawn_signature gateway_posix_spawn_api)(snd entry))exchange_error_calls.
Proof.
  repeat constructor;cbn[gateway_barrier_external gateway_spawn_signature];
    try solve[repeat eexists;reflexivity];discriminate.
Qed.

Theorem actual_exchange_errors_return:
  Forall(gateway_barrier_returns exchange_error_allowed)exchange_early_errors.
Proof.
  apply Forall_forall;intros body MEMBER;cbn[exchange_early_errors map]in MEMBER.
  repeat destruct MEMBER as[SAME|MEMBER];try contradiction;subst body;vm_compute;tauto.
Qed.

Theorem actual_exchange_error_not_local identifier:
  exchange_error_allowed identifier=true->~In identifier(map fst(fn_vars f_host_exchange)).
Proof.
  unfold exchange_error_allowed;rewrite existsb_exists.
  intros[entry[MEMBER EQUAL]];apply Pos.eqb_eq in EQUAL;subst identifier.
  cbn[exchange_error_calls]in MEMBER.
  repeat destruct MEMBER as[SAME|MEMBER];try contradiction;subst entry;cbn;intuition discriminate.
Qed.

Theorem actual_exchange_error_bindings before environment allocated:
  alloc_variables(Clight.globalenv prog)empty_env before(fn_vars f_host_exchange)environment allocated->
  gateway_barrier_bindings(Clight.globalenv prog)environment exchange_error_allowed
    (gateway_spawn_signature gateway_posix_spawn_api).
Proof.
  intros ALLOC identifier ALLOWED;split.
  - eapply actual_exchange_setup_unshadowed;[exact ALLOC|]. apply actual_exchange_error_not_local;exact ALLOWED.
  - unfold exchange_error_allowed in ALLOWED;rewrite existsb_exists in ALLOWED.
    destruct ALLOWED as[entry[MEMBER EQUAL]];apply Pos.eqb_eq in EQUAL;subst identifier.
    pose proof((proj1(Forall_forall _ _))actual_exchange_error_declarations entry MEMBER)as[symbol[SYMBOL FUNCTION]].
    pose proof((proj1(Forall_forall _ _))actual_exchange_error_external entry MEMBER)as OTHER.
    exists symbol,(snd entry);split;[exact SYMBOL|]. split;assumption.
Qed.

Theorem actual_exchange_error_never_spawns {World Event}(backend:gateway_backend World Event)
    allocation_before environment allocated body continuation temporaries before world events arguments target_cont after next:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  In body exchange_early_errors->call_cont continuation=Kstop->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_exchange body continuation environment temporaries before)world)events
    (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments target_cont after)next)->False.
Proof.
  intros ALLOC MEMBER STOP RUN.
  eapply gateway_return_barrier_excludes_call;
    [exact(actual_exchange_error_bindings allocation_before environment allocated ALLOC)| |exact STOP|exact RUN].
  exact((proj1(Forall_forall _ _))actual_exchange_errors_return body MEMBER).
Qed.
