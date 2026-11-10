(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: An actual internal caller reaches its entry before an external callee, without a later return premise. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewayFunctionEntry GatewayContexts.
Import ListNotations.

Theorem actual_gateway_entry_before_external {World Event} (backend : gateway_backend World Event) ge
    function arguments continuation before world events external types result convention values target_cont after final_world :
  gateway_steps backend ge (gateway_live (Callstate (Internal function) arguments continuation before) world) events
    (gateway_live (Callstate (External external types result convention) values target_cont after) final_world) ->
  exists prefix suffix memory owner environment parameters allocated,
    events = prefix ++ gateway_source E0 :: suffix /\
    Forall (fun event => event = gateway_ambient) prefix /\
    gateway_steps backend ge (gateway_live (Callstate (Internal function) arguments continuation before) world) prefix
      (gateway_live (Callstate (Internal function) arguments continuation memory) owner) /\
    function_entry2 ge function arguments memory environment parameters allocated /\
    gateway_steps backend ge (gateway_live (State function (fn_body function) continuation environment parameters allocated) owner) suffix
      (gateway_live (Callstate (External external types result convention) values target_cont after) final_world).
Proof.
  revert before world; induction events as [|observed rest IH]; intros before world RUN.
  - inversion RUN.
  - inversion RUN; subst.
    match goal with STEP : gateway_step _ _ _ _ _ |- _ =>
      destruct (gateway_function_call_step _ _ _ _ _ _ _ _ _ STEP)
        as [[environment [parameters [allocated [EVENT [ENTRY TARGET]]]]] |
          [[changed [next [EVENT [INTERFERENCE TARGET]]]] |[EVENT TARGET]]] end; subst.
    + exists [], rest, before, world, environment, parameters, allocated; cbn.
      split; [reflexivity |]. split; [constructor |]. split; [constructor |]. split; assumption.
    + match goal with TAIL : gateway_steps _ _ (gateway_live (Callstate (Internal _) _ _ changed) next) _ _ |- _ =>
        destruct (IH changed next TAIL) as (prefix & suffix & memory & owner & environment & parameters & allocated &
          EVENTS & AMBIENT & PREFIX & ENTRY & SUFFIX) end.
      exists (gateway_ambient :: prefix), suffix, memory, owner, environment, parameters, allocated.
      split; [cbn; congruence |]. split; [constructor; [reflexivity |exact AMBIENT] |]. split.
      * econstructor; [apply gateway_interleaved; exact INTERFERENCE |exact PREFIX].
      * split; assumption.
    + match goal with TAIL : gateway_steps _ _ (gateway_dead _ _) _ _ |- _ =>
        destruct (gateway_dead_steps _ _ _ _ _ _ TAIL) as [_ BAD] end; discriminate.
Qed.
