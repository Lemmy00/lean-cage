(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: An unavailable callback cannot reach any operational callee beyond error posting. *)
From Stdlib Require Import ZArith List Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPublicInitializationGuard GatewayMemoryPrefixes
  GatewayFramedRuntime GatewayReturnBarrier GatewayBindings GatewayRuntimeABI.
Import ListNotations.

Definition public_denial_api identifier := Pos.eqb identifier _PyErr_SetString.

Theorem actual_public_denial_profile guard : gateway_barrier_returns public_denial_api (public_guard_denied guard).
Proof. destruct guard; vm_compute; tauto. Qed.

Theorem actual_public_denial_bindings environment denied :
  environment ! _PyErr_SetString = None -> gateway_set_error_definition <> denied ->
  gateway_barrier_bindings (Clight.globalenv prog) environment public_denial_api denied.
Proof.
  intros LOCAL DIFFERENT identifier ALLOWED; unfold public_denial_api in ALLOWED.
  apply Pos.eqb_eq in ALLOWED; subst identifier; split; [exact LOCAL |].
  assert (BINDING : gateway_function_binding (Clight.globalenv prog) _PyErr_SetString gateway_set_error_definition)
    by (apply gateway_actual_function_binding; vm_compute; reflexivity).
  destruct BINDING as [symbol [SYMBOL FUNCTION]].
  exists symbol, gateway_set_error_definition; split; [exact SYMBOL |]. split; [exact FUNCTION |].
  split; [repeat eexists; reflexivity |exact DIFFERENT].
Qed.

Theorem gateway_uninitialized_callback_excludes_operation {World Event} (backend : gateway_backend World Event)
    (property : mem -> World -> Prop) guard environment parameters allocation_before allocated complete
    denied before world events arguments continuation after next :
  gateway_ambient_closed backend property ->
  alloc_variables (Clight.globalenv prog) empty_env allocation_before (fn_vars (public_guard_owner guard)) environment allocated ->
  Genv.find_symbol (Clight.globalenv prog) _host_initialized = Some complete ->
  (forall memory world, property memory world -> Mem.load Mint32 memory complete 0 = Some (Vint Int.zero)) ->
  gateway_set_error_definition <> denied -> property before world ->
  gateway_steps backend (Clight.globalenv prog)
    (gateway_live (State (public_guard_owner guard) (fn_body (public_guard_owner guard)) Kstop environment parameters before) world) events
    (gateway_live (Callstate denied arguments continuation after) next) -> False.
Proof.
  intros CLOSED ALLOCATED SYMBOL LOAD DIFFERENT INPUT RUN.
  destruct (actual_public_guard_global_scope _ _ _ _ _ ALLOCATED) as [GLOBAL ERROR_GLOBAL].
  pose proof (gateway_public_guard_source_prefix backend (Clight.globalenv prog) property guard false environment parameters before complete
    CLOSED GLOBAL SYMBOL LOAD) as SCRIPT.
  destruct (gateway_memory_prefix_cut backend (Clight.globalenv prog) _ _ _ _ before world events
    (Callstate denied arguments continuation after) next SCRIPT I INPUT RUN)
    as (prefix & suffix & memory & current & EVENTS & QUIET & PREFIX & READY & SUFFIX).
  eapply gateway_return_barrier_excludes_call with
    (allowed := public_denial_api) (body := public_guard_denied guard)
    (continuation := Kseq (public_guard_after guard) Kstop).
  - exact (actual_public_denial_bindings environment denied ERROR_GLOBAL DIFFERENT).
  - apply actual_public_denial_profile.
  - reflexivity.
  - exact SUFFIX.
Qed.
