(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Readiness and reads retain actual source-owned reference pools. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Values Memory Integers.
From HostGateway Require Import GatewayGraphSnapshots GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayValue
  GatewayValueFrame GatewayObjectThreads GatewayThreadRuntime GatewayStreamInterface GatewayNativeMemory
  GatewayThreadInvariant GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceHeld.
Import ListNotations.
Local Close Scope lean_scope.

Record gateway_reference_thread_effect {World}(python:World->python_world)(objects:World->gateway_object_heap)
    world next:Prop:={
  gateway_reference_thread_counts:forall pointer,
    (python_native_strong(python world)pointer<=python_native_strong(python next)pointer)%nat;
  gateway_reference_thread_values:gateway_objects_frame(python world)(objects world)(python next)(objects next)[];
  gateway_reference_thread_privacy:gateway_object_privacy_frame(python world)(objects world)(python next)(objects next)[]
}.

(* Only the current invocation and designated retained C-global pool is counted.
   This is not a frame on public module data, other invocations, or ob_refcnt. *)
Record gateway_reference_thread_contract {World Event}(backend:gateway_backend World Event)
    native stable base heap_allocation(python:World->python_world)(objects:World->gateway_object_heap):Prop:={
  gateway_reference_thread_ambient:forall mode before world after next,
    base mode before world->gateway_interference backend before world after next->
    gateway_reference_thread_effect python objects world next;
  gateway_reference_thread_return:forall mode before world after_mode after next,
    gateway_object_thread_operation backend native stable base heap_allocation mode before world after_mode after next->
    gateway_reference_thread_effect python objects world next
}.

Definition gateway_reference_scope {World}(python:World->python_world)(objects:World->gateway_object_heap)
    decimal_float ledger held world:Prop:=
  gateway_reference_counts_fit ledger(python world) /\
    gateway_reference_held python objects decimal_float ledger held world.

Theorem gateway_reference_scope_thread_effect {World}python objects decimal_float ledger held world next:
  @gateway_reference_scope World python objects decimal_float ledger held world->
  gateway_reference_thread_effect python objects world next->
  gateway_reference_scope python objects decimal_float ledger held next.
Proof.
  intros[FIT HELD]EFFECT.
  assert(NEXT_FIT:gateway_reference_counts_fit ledger(python next)).
  { intro pointer;specialize(FIT pointer).
    pose proof(gateway_reference_thread_counts _ _ _ _ EFFECT pointer);lia. }
  split;[exact NEXT_FIT|]. apply Forall_forall;intros captured MEMBER.
  apply Forall_forall with(x:=captured)in HELD;[|exact MEMBER].
  destruct HELD as[[place OWNED][PRIVATE[DESTROY VALUE]]].
  assert(OLD_ROOT:gateway_rooted(python world)(objects world)(gateway_held_object captured)).
  { eapply gateway_reference_owned_rooted;[exact FIT|exact OWNED]. }
  assert(NEXT_ROOT:gateway_rooted(python next)(objects next)(gateway_held_object captured)).
  { eapply gateway_reference_owned_rooted;[exact NEXT_FIT|exact OWNED]. }
  destruct(gateway_private_tree_preserved _ _ _ _ _ PRIVATE DESTROY OLD_ROOT NEXT_ROOT
    (gateway_reference_thread_values _ _ _ _ EFFECT)(gateway_reference_thread_privacy _ _ _ _ EFFECT))
    as[NEXT_PRIVATE NEXT_DESTROY].
  split;[exists place;exact OWNED|]. split;[exact NEXT_PRIVATE|]. split;[exact NEXT_DESTROY|].
  destruct(gateway_held_view captured)as[wire|scalar|wire initial];cbn[gateway_held_description_holds]in VALUE|-*.
  - eapply gateway_value_heap_retained;[exact VALUE|exact PRIVATE|exact OLD_ROOT|exact NEXT_ROOT|
      exact(gateway_reference_thread_values _ _ _ _ EFFECT)|exact(gateway_reference_thread_privacy _ _ _ _ EFFECT)].
  - destruct VALUE as[LOOKUP CHILDREN];split;[|exact CHILDREN].
    eapply gateway_reference_thread_values;[exact EFFECT|exact OLD_ROOT|exact NEXT_ROOT|
      apply PRIVATE;constructor|intro BAD;inversion BAD|exact LOOKUP].
  - destruct VALUE as[WIRE[INITIAL SNAPSHOT]];split.
    + eapply gateway_value_heap_retained;[exact WIRE|exact PRIVATE|exact OLD_ROOT|exact NEXT_ROOT|exact (gateway_reference_thread_values _ _ _ _ EFFECT)|exact (gateway_reference_thread_privacy _ _ _ _ EFFECT)].
    + split;[exact INITIAL|]. eapply gateway_graph_snapshot_retained;
        [exact PRIVATE|exact DESTROY|exact OLD_ROOT|exact NEXT_ROOT|exact (gateway_reference_thread_values _ _ _ _ EFFECT)|exact (gateway_reference_thread_privacy _ _ _ _ EFFECT)|exact SNAPSHOT].
Qed.

Section ReferenceThread.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
  (native:World->block->Prop)(stable:World->block->Z->Prop)
  (base:option Values.val->mem->World->Prop)(thread_errno:World->int)(heap_allocation:block->Z->Prop)
  (python:World->python_world)(objects:World->gateway_object_heap)
  (decimal_float:list Z->Floats.float->Prop).
Context(contract:gateway_reference_thread_contract backend native stable base heap_allocation python objects).

Lemma gateway_reference_scope_invariant ledger held:
  gateway_thread_invariant_contract backend native stable base heap_allocation
    (gateway_reference_scope python objects decimal_float ledger held).
Proof.
  constructor.
  - intros mode before world after next SIDE SCOPE AMBIENT.
    eapply gateway_reference_scope_thread_effect;[exact SCOPE|].
    eapply gateway_reference_thread_ambient;[exact contract|exact SIDE|exact AMBIENT].
  - intros mode before world after_mode after next SCOPE OPERATION.
    eapply gateway_reference_scope_thread_effect;[exact SCOPE|].
    eapply gateway_reference_thread_return;[exact contract|exact OPERATION].
Qed.

Theorem gateway_thread_with_reference_scope ledger held
    (runtime:gateway_thread_runtime backend io native stable base thread_errno):
  gateway_thread_runtime backend io native stable
    (gateway_thread_invariant_discipline base(gateway_reference_scope python objects decimal_float ledger held))thread_errno.
Proof. apply gateway_thread_with_invariant with(heap_allocation:=heap_allocation);[exact runtime|apply gateway_reference_scope_invariant]. Qed.

Theorem gateway_memory_with_reference_scope ledger held
    (runtime:gateway_native_memory_runtime backend io native stable base heap_allocation):
  gateway_native_memory_runtime backend io native stable
    (gateway_thread_invariant_discipline base(gateway_reference_scope python objects decimal_float ledger held))heap_allocation.
Proof. apply gateway_memory_with_invariant;[exact runtime|apply gateway_reference_scope_invariant]. Qed.

End ReferenceThread.
