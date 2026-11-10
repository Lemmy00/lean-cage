(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Held-GIL ambient steps do not perform Python callback mutations. *)
From Stdlib Require Import ZArith List.
From compcert Require Import AST Integers Values Memory Ctypes Clight.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayOutcome GatewayTypeRuntime
  GatewayReferenceRuntime GatewayFramedRuntime.
Import ListNotations.
Open Scope Z_scope.

(* This is a borrowed native method argument, not an invocation-owned reference.
   Its managed field may point at a public, mutable dictionary. *)
Record gateway_public_outcome_layout {World}(python:World->python_world)
    (types:World->Values.val->option gateway_type_description)
    (instances:World->Values.val->option Values.val)(dictionary:World->Values.val->Prop)
    memory world object offset class description data:Prop:={
  gateway_public_outcome_python:python_world_valid(python world)memory;
  gateway_public_outcome_gil:python_gil(python world)=true;
  gateway_public_outcome_borrowed:python_live(python world)(Vptr object offset);
  gateway_public_outcome_instance:instances world(Vptr object offset)=Some class;
  gateway_public_outcome_description:types world class=Some description;
  gateway_public_outcome_source:gateway_source_outcome_type description;
  gateway_public_outcome_loaded:Mem.loadv Mptr memory(gateway_outcome_slot object offset)=Some data;
  gateway_public_outcome_managed:data=Vnullptr \/exists block position,
    data=Vptr block position /\python_live(python world)data /\
    Mem.weak_valid_pointer memory block(Ptrofs.unsigned position)=true /\dictionary world data
}.

Record gateway_public_outcome_runtime {World Event}(backend:gateway_backend World Event)
    (python:World->python_world)(types:World->Values.val->option gateway_type_description)
    (instances:World->Values.val->option Values.val)(dictionary:World->Values.val->Prop):Prop:={
  gateway_public_outcome_layout_current:forall memory world object offset class description,
    python_world_valid(python world)memory->python_gil(python world)=true->
    python_live(python world)(Vptr object offset)->instances world(Vptr object offset)=Some class->
    types world class=Some description->gateway_source_outcome_type description->
    exists data,gateway_public_outcome_layout python types instances dictionary
      memory world object offset class description data;
  gateway_public_outcome_ambient:forall before world after next object offset class description data,
    gateway_public_outcome_layout python types instances dictionary before world object offset class description data->
    gateway_interference backend before world after next->
    gateway_public_outcome_layout python types instances dictionary after next object offset class description data
}.

(* No SDK operation occurs in this record. In particular it gives no frame for
   self->data, dictionary contents or presentation across an actual callback. *)
Theorem gateway_public_outcome_layout_closed {World Event}(backend:gateway_backend World Event)
    python types instances dictionary(runtime:gateway_public_outcome_runtime backend python types instances dictionary)
    object offset class description data:
  gateway_ambient_closed backend(fun memory world=>
    gateway_public_outcome_layout python types instances dictionary memory world object offset class description data).
Proof.
  unfold gateway_ambient_closed;intros before world after next LAYOUT INTERFERENCE.
  eapply gateway_public_outcome_ambient;eassumption.
Qed.

Theorem gateway_public_outcome_nonnull_pointer {World}python types instances dictionary
    memory world object offset class description data:
  @gateway_public_outcome_layout World python types instances dictionary
    memory world object offset class description data->data<>Vnullptr->
  exists block position,data=Vptr block position /\python_live(python world)data /\
    Mem.weak_valid_pointer memory block(Ptrofs.unsigned position)=true /\dictionary world data.
Proof.
  intros LAYOUT NONNULL;destruct(gateway_public_outcome_managed _ _ _ _ _ _ _ _ _ _ _ LAYOUT)as[NULL|MANAGED];
    [contradiction|exact MANAGED].
Qed.
