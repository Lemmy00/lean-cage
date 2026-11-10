(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: A non-stealing builtin observer retains the current
   source pool and exact independently private graph descriptions. *)
From Stdlib Require Import List Lia.
From HostGateway Require Import GatewayPython GatewayObjects GatewayReferenceThreads.

Theorem gateway_reference_observer_scope {World}python objects decimal_float ledger held world next before after:
  @gateway_reference_scope World python objects decimal_float ledger held world->
  gateway_observer_return(python world)(objects world)before(python next)(objects next)after->
  gateway_reference_scope python objects decimal_float ledger held next.
Proof.
  intros SCOPE RETURN;eapply gateway_reference_scope_thread_effect;[exact SCOPE|]. constructor.
  - intro pointer;rewrite(gateway_observer_references _ _ _ _ _ _ RETURN pointer)by(intro NONE;inversion NONE);lia.
  - exact(gateway_observer_values _ _ _ _ _ _ RETURN).
  - exact(gateway_observer_privacy _ _ _ _ _ _ RETURN).
Qed.
