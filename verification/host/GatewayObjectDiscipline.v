(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: A normal parser operation owns its actual interpreter state. *)
From compcert Require Import Values Memory.
From HostGateway Require Import GatewayPython GatewayObjects.

Definition gateway_python_discipline {World}(python:World->python_world)(objects:World->gateway_object_heap)
    (detached:Values.val->mem->World->Prop)(mode:option Values.val)memory world :Prop:=
  match mode with
  |None=>gateway_objects_ready(python world)(objects world)memory
  |Some saved=>detached saved memory world
  end.

Lemma gateway_python_normal_ready {World}python objects detached memory world :
  @gateway_python_discipline World python objects detached None memory world <->
    gateway_objects_ready(python world)(objects world)memory.
Proof. reflexivity. Qed.
