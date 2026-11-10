(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Python mutations under the held GIL occur at actual SDK operations. *)
From Stdlib Require Import List Lia.
From compcert Require Import Values Memory.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayValue GatewayValueFrame
  GatewayGraphSnapshots GatewayObjectThreads GatewayReferenceThreads GatewayReferenceHeld GatewayFramedRuntime.
Import ListNotations.
Local Close Scope lean_scope.

(* Native signal/cancellation cells and all SDK events remain unconstrained by
   this contract. Python callbacks, including same-receiver reinit, are SDK events. *)
Record gateway_held_gil_views {World Event}(backend:gateway_backend World Event)
    (python:World->python_world)(objects:World->gateway_object_heap):Prop:={
  gateway_held_gil_values:forall before world after next,
    python_gil(python world)=true->gateway_interference backend before world after next->
    gateway_object_values(objects next)=gateway_object_values(objects world) /\
    gateway_object_private(objects next)=gateway_object_private(objects world)
}.

Lemma gateway_rooted_same_values before heap after next_heap pointer:
  (forall object,(python_native_strong before object<=python_native_strong after object)%nat)->
  gateway_object_values next_heap=gateway_object_values heap->
  gateway_rooted before heap pointer->gateway_rooted after next_heap pointer.
Proof.
  intros COUNTS VALUES ROOT;induction ROOT.
  - constructor;specialize(COUNTS object);lia.
  - eapply gateway_child_root;[exact IHROOT|rewrite VALUES;exact H|exact H0].
Qed.

Definition gateway_borrowed_description {World}(python:World->python_world)(objects:World->gateway_object_heap)
    decimal_float pointer description world:Prop:=
  @gateway_rooted(python world)(objects world)pointer /\gateway_private_tree(objects world)pointer /\
    gateway_destructible(objects world)pointer /\
    gateway_held_description_holds decimal_float(objects world)pointer description.

Theorem gateway_borrowed_description_thread {World}python objects decimal_float pointer description world next:
  @gateway_borrowed_description World python objects decimal_float pointer description world->
  gateway_reference_thread_effect python objects world next->
  gateway_object_values(objects next)=gateway_object_values(objects world)->
  gateway_borrowed_description python objects decimal_float pointer description next.
Proof.
  intros[ROOT[PRIVATE[DESTROY DESCRIPTION]]]EFFECT VALUES.
  assert(NEXT_ROOT:gateway_rooted(python next)(objects next)pointer).
  { eapply gateway_rooted_same_values;[exact(gateway_reference_thread_counts _ _ _ _ EFFECT)|exact VALUES|exact ROOT]. }
  destruct(gateway_private_tree_preserved _ _ _ _ _ PRIVATE DESTROY ROOT NEXT_ROOT
    (gateway_reference_thread_values _ _ _ _ EFFECT)(gateway_reference_thread_privacy _ _ _ _ EFFECT))
    as[NEXT_PRIVATE NEXT_DESTROY].
  split;[exact NEXT_ROOT|]. split;[exact NEXT_PRIVATE|]. split;[exact NEXT_DESTROY|].
  destruct description as[wire|scalar|wire initial];cbn in DESCRIPTION|-*.
  - eapply gateway_value_heap_retained;[exact DESCRIPTION|exact PRIVATE|exact ROOT|exact NEXT_ROOT|
      exact(gateway_reference_thread_values _ _ _ _ EFFECT)|exact(gateway_reference_thread_privacy _ _ _ _ EFFECT)].
  - destruct DESCRIPTION as[LOOKUP CHILDREN];split;[rewrite VALUES;exact LOOKUP|exact CHILDREN].
  - destruct DESCRIPTION as[WIRE[INITIAL SNAPSHOT]];split.
    + eapply gateway_value_heap_retained;[exact WIRE|exact PRIVATE|exact ROOT|exact NEXT_ROOT|
        exact(gateway_reference_thread_values _ _ _ _ EFFECT)|exact(gateway_reference_thread_privacy _ _ _ _ EFFECT)].
    + split;[exact INITIAL|].
      eapply(gateway_graph_snapshot_retained(python world)(objects world)(python next)(objects next)initial pointer);
        [exact PRIVATE|exact DESTROY|exact ROOT|exact NEXT_ROOT|exact(gateway_reference_thread_values _ _ _ _ EFFECT)|
         exact(gateway_reference_thread_privacy _ _ _ _ EFFECT)|exact SNAPSHOT].
Qed.
