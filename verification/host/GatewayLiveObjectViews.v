(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Managed strong edges and a pure IncRef retain live builtin payloads. *)
From Stdlib Require Import List.
From compcert Require Import Values Memory.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayValue GatewayValueFrame
  GatewayGraphSnapshots GatewayObjectThreads.
Import ListNotations.
Local Close Scope lean_scope.

Definition gateway_managed_strong_edges python heap:Prop:=
  forall parent value child,python_live python parent->gateway_object_values heap parent=Some value->
    In child(gateway_object_children value)->python_live python child.

Record gateway_managed_graph_runtime {World}(python:World->python_world)(objects:World->gateway_object_heap):Prop:={
  gateway_managed_graph_current:forall memory world,
    python_world_valid(python world)memory->python_gil(python world)=true->
    gateway_managed_strong_edges(python world)(objects world)
}.

Lemma gateway_managed_reachable_live python heap root:
  gateway_managed_strong_edges python heap->python_live python root->
  forall object,gateway_object_reachable heap root object->python_live python object.
Proof.
  intros EDGES LIVE object REACHED;induction REACHED;[exact LIVE|].
  eapply EDGES;eassumption.
Qed.

(* This relation does not freeze counts, C storage or callback effects. A pure
   reference increment has no Python callback and preserves pre-live payloads. *)
Definition gateway_live_object_views python heap next_heap:Prop:=
  forall object,python_live python object->
    gateway_object_values next_heap object=gateway_object_values heap object /\
    (gateway_object_private heap object=true->gateway_object_private next_heap object=true).

Record gateway_incref_live_views {World Event}(backend:gateway_backend World Event)
    (python:World->python_world)(objects:World->gateway_object_heap):Prop:={
  gateway_incref_existing_views:forall before world pointer result after next observed,
    gateway_objects_ready(python world)(objects world)before->python_live(python world)pointer->
    gateway_object_operation backend gateway_api_incref[pointer]before world result after next observed->
    gateway_live_object_views(python world)(objects world)(objects next)
}.

Theorem gateway_live_graph_description python heap next_heap decimal_float root description:
  (forall object,gateway_object_reachable heap root object->python_live python object)->
  gateway_live_object_views python heap next_heap->gateway_private_tree heap root->gateway_destructible heap root->
  gateway_held_description_holds decimal_float heap root description->
  gateway_private_tree next_heap root /\gateway_destructible next_heap root /\
    gateway_held_description_holds decimal_float next_heap root description.
Proof.
  intros LIVE VIEWS PRIVATE DESTROY DESCRIPTION.
  assert(SNAPSHOT:gateway_graph_snapshot heap next_heap root).
  { intros object REACHED;exact(proj1(VIEWS object(LIVE object REACHED))). }
  assert(BACK:forall object,gateway_object_reachable next_heap root object->gateway_object_reachable heap root object)
    by(exact(gateway_graph_snapshot_backward heap next_heap root DESTROY SNAPSHOT)).
  split.
  - intros object REACHED;apply(proj2(VIEWS object(LIVE object(BACK object REACHED))));apply PRIVATE,BACK;exact REACHED.
  - split.
    + intros object REACHED;destruct(DESTROY object(BACK object REACHED))as(value &kind &LOOKUP &KIND &SAFE).
      exists value,kind;split;[rewrite SNAPSHOT;[exact LOOKUP|apply BACK;exact REACHED]|]. split;assumption.
    + assert(FRAME:gateway_reachable_values_frame heap next_heap root).
      { intros object value REACHED LOOKUP;rewrite SNAPSHOT;assumption. }
      destruct description as[wire|scalar|wire initial];cbn in DESCRIPTION|-*.
      * eapply(proj1(gateway_value_tree_map decimal_float heap next_heap));[exact DESCRIPTION|constructor|exact FRAME].
      * destruct DESCRIPTION as[LOOKUP CHILDREN];split;[rewrite SNAPSHOT;[exact LOOKUP|constructor]|exact CHILDREN].
      * destruct DESCRIPTION as[WIRE[INITIAL ORIGINAL]];split.
        -- eapply(proj1(gateway_value_tree_map decimal_float heap next_heap));[exact WIRE|constructor|exact FRAME].
        -- split;[exact INITIAL|]. intros object REACHED.
           rewrite SNAPSHOT by(eapply gateway_graph_snapshot_forward;[exact ORIGINAL|exact REACHED]).
           apply ORIGINAL;exact REACHED.
Qed.
