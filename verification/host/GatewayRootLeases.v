(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Current C-owned references have separate lifetime identities. *)
From Stdlib Require Import ZArith Lia List.
From compcert Require Import Integers Values Memory.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects.
Import ListNotations.

Definition gateway_leases_retained {World}(leases:World->nat->Values.val->Prop)world next :Prop:=
  forall ticket object,leases world ticket object ->leases next ticket object.

Definition gateway_reference_created {World}(leases:World->nat->Values.val->Prop)world next result ticket :Prop:=
  leases next ticket result /\(forall object,~leases world ticket object) /\gateway_leases_retained leases world next.

Definition gateway_reference_released {World}(leases:World->nat->Values.val->Prop)world next ticket :Prop:=
  (forall object,~leases next ticket object) /\
  (forall other object,other<>ticket ->leases world other object ->leases next other object).

(* This is the current native invocation's ledger, not a frame on every global
   Python reference. Reentrant/public Workspace operations may change other owners. *)
Record gateway_root_lease_runtime {World Event}(backend:gateway_backend World Event)
    (python:World->python_world)(objects:World->gateway_object_heap)
    (decimal_float:list BinNums.Z->Floats.float->Prop)(leases:World->nat->Values.val->Prop) :Prop:={
  gateway_lease_unique:forall world ticket first second,
    leases world ticket first ->leases world ticket second ->first=second;
  gateway_lease_count:forall world object tickets,NoDup tickets ->
    Forall(fun ticket=>leases world ticket object)tickets ->
    (length tickets<=python_native_strong(python world)object)%nat;
  gateway_constructor_lease:forall api arguments before world result after next observed value,
    gateway_objects_ready(python world)(objects world)before ->
    gateway_constructor_request decimal_float(objects world)before api arguments value ->
    gateway_constructor_roots(python world)(objects world)api arguments ->
    gateway_object_operation backend api arguments before world result after next observed ->result<>Vnullptr ->
    exists ticket,gateway_reference_created leases world next result ticket;
  gateway_incref_lease:forall before world object result after next observed,
    python_world_valid(python world)before ->python_gil(python world)=true ->python_live(python world)object ->
    gateway_object_operation backend gateway_api_incref[object]before world result after next observed ->
    exists ticket,gateway_reference_created leases world next object ticket;
  gateway_decref_lease:forall before world ticket object result after next observed,
    python_world_valid(python world)before ->python_gil(python world)=true ->leases world ticket object ->
    gateway_object_operation backend gateway_api_decref[object]before world result after next observed ->
    gateway_reference_released leases world next ticket
}.

Theorem gateway_lease_rooted {World Event}(backend:gateway_backend World Event)
    python objects decimal_float leases(runtime:gateway_root_lease_runtime backend python objects decimal_float leases)
    world ticket object :leases world ticket object ->gateway_rooted(python world)(objects world)object.
Proof.
  intro LEASE;apply gateway_direct_root.
  pose proof(gateway_lease_count _ _ _ _ _ runtime world object[ticket]
    ltac:(constructor;[intro BAD;inversion BAD|constructor])
    ltac:(constructor;[exact LEASE|constructor]))as COUNT;cbn in COUNT;lia.
Qed.

Theorem gateway_distinct_leases_keep_reference {World Event}(backend:gateway_backend World Event)
    python objects decimal_float leases(runtime:gateway_root_lease_runtime backend python objects decimal_float leases)
    world first second object :first<>second ->leases world first object ->leases world second object ->
    (2<=python_native_strong(python world)object)%nat.
Proof.
  intros DIFFERENT FIRST SECOND.
  pose proof(gateway_lease_count _ _ _ _ _ runtime world object[first;second]
    ltac:(constructor;[intros[SAME|BAD];[congruence|contradiction]|constructor;[intro BAD;inversion BAD|constructor]])
    ltac:(constructor;[exact FIRST|constructor;[exact SECOND|constructor]]))as COUNT;exact COUNT.
Qed.

Theorem gateway_created_reference_is_new {World}(leases:World->nat->Values.val->Prop)world next result ticket other value :
  gateway_reference_created leases world next result ticket ->leases world other value ->ticket<>other.
Proof. intros[NEW[FRESH RETAINED]]OLD SAME;subst other;exact(FRESH value OLD). Qed.
