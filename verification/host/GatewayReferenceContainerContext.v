(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Container source phases retain the same count, private
   native cells and actual reference-ledger graphs under arbitrary permitted interleaving. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Values Memory Integers.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayObjectDiscipline
  GatewayObjectThreads GatewayContainerLength GatewayContainerGuards GatewayContainerMemory GatewayValueEntry
  GatewayValueStack GatewayValueRegions GatewayReferenceLedger GatewayReferenceThreads GatewayReferenceContainerScope
  GatewayStreamInterface GatewayThreadRuntime GatewayFramedRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Definition gateway_reference_counted_context {World}python objects decimal_float detached stable ledger held container slots
    stream_block stream_offset initial readonly original size memory world:Prop:=
  gateway_container_counted(fun current candidate=>gateway_native_private(python current)candidate)stable
    (gateway_python_discipline python objects detached)container slots stream_block stream_offset initial readonly original size memory world /\
  @gateway_reference_scope World python objects decimal_float ledger held world /\
  (forall candidate position,readonly candidate position->gateway_native_private(python world)candidate).

Theorem gateway_reference_counted_context_ambient {World Event}(backend:gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (references:gateway_reference_thread_contract backend(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    ledger held container slots stream_block stream_offset initial readonly original size:
  gateway_ambient_closed backend(gateway_reference_counted_context python objects decimal_float detached stable ledger held container slots
    stream_block stream_offset initial readonly original size).
Proof.
  intros first current last following[COUNTED[HELD NATIVE]]INTERFERENCE;split.
  - eapply gateway_container_counted_ambient;[exact runtime|exact COUNTED|exact INTERFERENCE].
  - assert(SIDE:gateway_python_discipline python objects detached None first current).
    { eapply gateway_container_counted_side;exact COUNTED. }
    split.
    + eapply gateway_reference_scope_thread_effect;[exact HELD|].
      eapply gateway_reference_thread_ambient;[exact references|exact SIDE|exact INTERFERENCE].
    + intros candidate position READ.
      destruct(gateway_thread_ambient _ _ _ _ _ _ runtime None first current last following SIDE INTERFERENCE)
        as[NEXT[[RETAIN STABLE]FRAME]].
      apply RETAIN;[eapply gateway_container_counted_readonly_live;[exact COUNTED|exact READ]|
        apply NATIVE with(position:=position);exact READ].
Qed.

Definition gateway_reference_counted_exclusion {World}python objects decimal_float detached stable ledger held container slots
    stream_block stream_offset initial readonly original size protected excluded memory world:Prop:=
  @gateway_reference_counted_context World python objects decimal_float detached stable ledger held container slots
    stream_block stream_offset initial readonly original size memory world /\
  (forall captured,In captured protected->~GatewayReferences.gateway_object_reachable(objects world)(gateway_held_object captured)excluded).

Theorem gateway_reference_counted_exclusion_ambient {World Event}(backend:gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (references:gateway_reference_thread_contract backend(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    ledger held container slots stream_block stream_offset initial readonly original size protected excluded:
  (forall captured,In captured protected->In captured held)->
  gateway_ambient_closed backend(gateway_reference_counted_exclusion python objects decimal_float detached stable ledger held container slots
    stream_block stream_offset initial readonly original size protected excluded).
Proof.
  intros SUBSET first current last following[CONTEXT OUTSIDE]INTERFERENCE;split.
  - eapply gateway_reference_counted_context_ambient;[exact runtime|exact references|exact CONTEXT|exact INTERFERENCE].
  - pose proof CONTEXT as[COUNTED[HELD NATIVE]].
    assert(SIDE:gateway_python_discipline python objects detached None first current)by(eapply gateway_container_counted_side;exact COUNTED).
    pose proof(gateway_reference_thread_ambient _ _ _ _ _ _ _ references None first current last following SIDE INTERFERENCE)as EFFECT.
    intros captured MEMBER;eapply gateway_reference_thread_keeps_graph_exclusion;
      [exact HELD|apply SUBSET;exact MEMBER|apply OUTSIDE;exact MEMBER|exact EFFECT].
Qed.
