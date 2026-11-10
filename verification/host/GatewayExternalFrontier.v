(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: A caller's actual SDK return has the same primitive
   and continuation. *)
From Stdlib Require Import List Lia.
From compcert Require Import AST Values Memory Events Ctypes Clight.
Require Import Machine CallContexts.
From HostGateway Require Import GatewayMachine GatewayContexts GatewayOperations.
Import ListNotations.

Theorem gateway_actual_external_frontier {World Event} (backend : gateway_backend World Event) ge
    external types result_type convention arguments continuation before world events final after next :
  is_call_cont continuation -> (0 < gateway_cont_weight continuation)%nat ->
  gateway_steps backend ge
    (gateway_live (Callstate (External external types result_type convention) arguments continuation before) world) events
    (gateway_live (Returnstate final Kstop after) next) ->
  exists prefix suffix memory called_world returned changed changed_world observed,
    events = prefix ++ gateway_primitive observed :: suffix /\ Forall gateway_pending_event prefix /\
    gateway_steps backend ge
      (gateway_live (Callstate (External external types result_type convention) arguments continuation before) world) prefix
      (gateway_live (Callstate (External external types result_type convention) arguments continuation memory) called_world) /\
    gateway_external backend external types result_type convention arguments memory called_world
      returned changed changed_world observed /\
    gateway_steps backend ge
      (gateway_live (Returnstate returned continuation changed) changed_world) suffix
      (gateway_live (Returnstate final Kstop after) next).
Proof.
  intros CALL WEIGHT RUN.
  destruct (gateway_return_cut backend ge (External external types result_type convention) arguments
    continuation before world events (Returnstate final Kstop after) next CALL WEIGHT RUN)
    as (local & rest & returned & terminal_memory & terminal_world & EVENTS & LOCAL & REST).
  destruct (gateway_external_operation_of_run backend ge external types result_type convention arguments
    before world local returned terminal_memory terminal_world LOCAL)
    as (prefix & suffix & memory & called_world & changed & changed_world & observed & LOCAL_EVENTS & PENDING & PREFIX & OPERATION & SUFFIX).
  exists prefix, (suffix ++ rest), memory, called_world, returned, changed, changed_world, observed.
  split.
  - rewrite EVENTS, LOCAL_EVENTS; rewrite <- app_assoc; reflexivity.
  - split; [exact PENDING |]. split.
    + exact (gateway_plug_steps backend ge _ _ _ continuation CALL PREFIX).
    + split; [exact OPERATION |]. eapply gateway_steps_append; [|exact REST].
      exact (gateway_plug_steps backend ge _ _ _ continuation CALL SUFFIX).
Qed.
