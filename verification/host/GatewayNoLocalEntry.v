(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Actual zero-local entry retains the caller's current memory. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewayFunctionEntry GatewayFrames GatewayFramedRuntime GatewayContexts GatewayCalls.
Import ListNotations.

Lemma gateway_no_local_entry ge function arguments before environment parameters allocated :
  fn_vars function = [] -> function_entry2 ge function arguments before environment parameters allocated ->
  environment = empty_env /\ allocated = before.
Proof.
  intros NO_LOCALS ENTRY; inversion ENTRY; subst.
  match goal with ALLOCATED : alloc_variables _ _ _ (fn_vars function) _ _ |- _ =>
    rewrite NO_LOCALS in ALLOCATED; inversion ALLOCATED; subst end.
  split; reflexivity.
Qed.

Theorem gateway_actual_no_local_entry {World Event} (backend : gateway_backend World Event) ge
    function arguments (property : mem -> World -> Prop) before world events value after next :
  fn_vars function = [] -> gateway_ambient_closed backend property -> property before world ->
  gateway_steps backend ge (gateway_live (Callstate (Internal function) arguments Kstop before) world) events
    (gateway_live (Returnstate value Kstop after) next) ->
  exists prefix suffix memory owner parameters,
    events = prefix ++ suffix /\
    gateway_steps backend ge (gateway_live (Callstate (Internal function) arguments Kstop before) world) prefix
      (gateway_live (State function (fn_body function) Kstop empty_env parameters memory) owner) /\
    property memory owner /\
    gateway_steps backend ge
      (gateway_live (State function (fn_body function) Kstop empty_env parameters memory) owner) suffix
      (gateway_live (Returnstate value Kstop after) next).
Proof.
  intros NO_LOCALS CLOSED INPUT RUN.
  destruct (actual_gateway_function_entry_ambient backend ge function arguments Kstop before world events value Kstop after next RUN)
    as (pending & suffix & memory & owner & environment & parameters & allocated & EVENTS & AMBIENT & PREFIX & ENTRY & REST).
  destruct (gateway_no_local_entry ge function arguments memory environment parameters allocated NO_LOCALS ENTRY) as [ENV SAME].
  subst environment allocated.
  assert (READY : property memory owner).
  { exact (gateway_ambient_run_ready backend ge property CLOSED
      (Callstate (Internal function) arguments Kstop before) before world pending memory owner INPUT AMBIENT PREFIX). }
  exists (pending ++ [gateway_source E0]), suffix, memory, owner, parameters.
  split; [rewrite EVENTS, <- app_assoc; reflexivity |]. split.
  - eapply gateway_steps_append; [exact PREFIX |].
    econstructor; [apply gateway_internal; [exact I |apply step_internal_function; exact ENTRY] |constructor].
  - split; assumption.
Qed.
