(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Actual constructors establish the parser's owned root snapshots. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers Values Memory.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayRootLeases
  GatewayValue GatewayValueFrame GatewayObjectThreads.
Import ListNotations.
Local Close Scope lean_scope.

Lemma gateway_leaf_reachable heap root value object :
  gateway_object_values heap root=Some value ->gateway_object_children value=[] ->
  gateway_object_reachable heap root object ->object=root.
Proof.
  intros LOOKUP CHILDREN REACHED;induction REACHED;[reflexivity|].
  subst parent;assert(SAME:value0=value)by congruence;subst value0;rewrite CHILDREN in H0;contradiction.
Qed.

Lemma gateway_leaf_private heap root value :
  gateway_object_values heap root=Some value ->gateway_object_children value=[] ->
  gateway_object_private heap root=true ->gateway_private_tree heap root.
Proof.
  intros LOOKUP CHILDREN PRIVATE object REACHED.
  rewrite(gateway_leaf_reachable _ _ _ _ LOOKUP CHILDREN REACHED);exact PRIVATE.
Qed.

Lemma gateway_leaf_destructible heap root value kind :
  gateway_object_values heap root=Some value ->gateway_object_children value=[] ->
  gateway_object_kind value=Some kind ->gateway_destructor_kind kind ->gateway_destructible heap root.
Proof.
  intros LOOKUP CHILDREN KIND SAFE object REACHED.
  rewrite(gateway_leaf_reachable _ _ _ _ LOOKUP CHILDREN REACHED).
  exists value,kind;split;[exact LOOKUP|]. split;assumption.
Qed.

Lemma gateway_constructor_all_private_frames python heap before result next next_heap after value :
  gateway_constructor_return python heap before result next next_heap after value ->
  gateway_objects_frame python heap next next_heap[] /\gateway_object_privacy_frame python heap next next_heap[].
Proof.
  intro RETURN;split.
  - intros object old ROOT NEXT PRIVATE OUTSIDE LOOKUP.
    destruct(Val.eq object result)as[SAME|DIFFERENT].
    + subst object;pose proof(gateway_constructor_alias _ _ _ _ _ _ _ _ RETURN ROOT)as ALIAS.
      assert(SAME:old=value)by congruence;subst old;exact(gateway_constructor_value _ _ _ _ _ _ _ _ RETURN).
    + eapply gateway_constructor_frame;[exact RETURN|exact ROOT|exact NEXT|exact PRIVATE| |exact LOOKUP].
      intros[MEMBER|MEMBER];[congruence|contradiction].
  - intros object ROOT NEXT PRIVATE OUTSIDE.
    destruct(Val.eq object result)as[SAME|DIFFERENT].
    + subst object;exact(gateway_constructor_private _ _ _ _ _ _ _ _ RETURN).
    + eapply gateway_constructor_privacy;[exact RETURN|exact ROOT|exact NEXT|exact PRIVATE|].
      intros[MEMBER|MEMBER];[congruence|contradiction].
Qed.

Lemma gateway_reachable_rooted python heap root object :
  gateway_rooted python heap root ->gateway_object_reachable heap root object ->gateway_rooted python heap object.
Proof. intros ROOT REACHED;induction REACHED;[exact ROOT|eapply gateway_child_root;eassumption]. Qed.

(* Fresh mutable containers cannot occur inside an earlier live rooted graph.
   Shared immutable scalar aliases remain permitted. *)
Theorem gateway_new_container_outside_old_graph python heap before result next next_heap after value root :
  gateway_constructor_return python heap before result next next_heap after value ->
  gateway_objects_ready python heap before ->gateway_mutable_container value ->
  gateway_rooted python heap root ->~gateway_object_reachable heap root result.
Proof.
  intros RETURN[[WORLD_VALID[ROOTS REST]]CLEAR]MUTABLE ROOT REACHED.
  destruct(ROOTS result(gateway_reachable_rooted _ _ _ _ ROOT REACHED))as[STRONG DESCRIBED].
  pose proof(gateway_constructor_fresh_container _ _ _ _ _ _ _ _ RETURN)as FRESH.
  destruct value;cbn in MUTABLE,FRESH;try contradiction;lia.
Qed.

Section ConstructorOwnership.
Context {World Event}(backend:gateway_backend World Event)(python:World->python_world)
  (objects:World->gateway_object_heap)(decimal_float:list BinNums.Z->Floats.float->Prop)
  (leases:World->nat->Values.val->Prop).
Context(runtime:gateway_objects_runtime backend python objects decimal_float)
  (roots:gateway_root_lease_runtime backend python objects decimal_float leases).

Theorem gateway_actual_constructor_held_scalar api arguments before world result after next observed value kind :
  gateway_objects_ready(python world)(objects world)before ->
  gateway_constructor_request decimal_float(objects world)before api arguments value ->
  gateway_constructor_roots(python world)(objects world)api arguments ->
  gateway_object_operation backend api arguments before world result after next observed ->result<>Vnullptr ->
  gateway_object_children value=[] ->gateway_object_kind value=Some kind ->gateway_destructor_kind kind ->
  exists ticket,gateway_reference_created leases world next result ticket /\
    gateway_held_values python objects decimal_float leases
      [{|gateway_held_ticket:=ticket;gateway_held_object:=result;gateway_held_view:=gateway_held_scalar_value value|}]next.
Proof.
  intros READY REQUEST ROOTS OPERATION NONNULL CHILDREN KIND SAFE.
  pose proof(gateway_runtime_constructor _ _ _ _ runtime _ _ _ _ _ _ _ _ _
    READY REQUEST ROOTS OPERATION NONNULL)as RETURN.
  destruct(gateway_constructor_lease _ _ _ _ _ roots _ _ _ _ _ _ _ _ _
    READY REQUEST ROOTS OPERATION NONNULL)as[ticket CREATED].
  destruct CREATED as[LEASE[NEW RETAINED]].
  exists ticket;split;[split;[exact LEASE|split;assumption]|]. constructor;[|constructor].
  split;[exact LEASE|]. split;[eapply gateway_lease_rooted;[exact roots|exact LEASE]|].
  split.
  - eapply gateway_leaf_private;[exact(gateway_constructor_value _ _ _ _ _ _ _ _ RETURN)|exact CHILDREN|].
    exact(gateway_constructor_private _ _ _ _ _ _ _ _ RETURN).
  - split.
    + eapply gateway_leaf_destructible;[exact(gateway_constructor_value _ _ _ _ _ _ _ _ RETURN)|
        exact CHILDREN|exact KIND|exact SAFE].
    + split;[exact(gateway_constructor_value _ _ _ _ _ _ _ _ RETURN)|exact CHILDREN].
Qed.

Theorem gateway_constructor_keeps_held_values held api arguments before world result after next observed value :
  gateway_objects_ready(python world)(objects world)before ->
  gateway_constructor_request decimal_float(objects world)before api arguments value ->
  gateway_constructor_roots(python world)(objects world)api arguments ->
  gateway_object_operation backend api arguments before world result after next observed ->result<>Vnullptr ->
  gateway_held_values python objects decimal_float leases held world ->
  gateway_held_values python objects decimal_float leases held next.
Proof.
  intros READY REQUEST ROOTS OPERATION NONNULL HELD.
  pose proof(gateway_runtime_constructor _ _ _ _ runtime _ _ _ _ _ _ _ _ _
    READY REQUEST ROOTS OPERATION NONNULL)as RETURN.
  destruct(gateway_constructor_lease _ _ _ _ _ roots _ _ _ _ _ _ _ _ _
    READY REQUEST ROOTS OPERATION NONNULL)as[ticket[LEASE[NEW RETAINED]]].
  destruct(gateway_constructor_all_private_frames _ _ _ _ _ _ _ _ RETURN)as[FRAME PRIVACY].
  eapply gateway_held_values_effect;[exact roots|exact HELD|]. split;[exact RETAINED|]. split;assumption.
Qed.

End ConstructorOwnership.
