(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: One actual API return supplies its byte/refcount operation. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayPython GatewayMachine.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_runtime_operation {World Event}(backend:gateway_backend World Event)
    (definition:Ctypes.fundef Clight.function)arguments before world result after next observed :Prop:=
  match definition with
  |Internal _=>False
  |External ef types result_type convention=>
    gateway_external backend ef types result_type convention arguments before world result after next observed
  end.

Definition python_output_cells memory data size :Prop:=
  exists data_block size_block,
    data=Vptr data_block Ptrofs.zero /\size=Vptr size_block Ptrofs.zero /\
    Mem.valid_access memory Mptr data_block 0 Writable /\
    Mem.valid_access memory Mint64 size_block 0 Writable.

(* The laws are conditional on the application's real API preconditions. A call
   without those preconditions remains broad in GatewayMachine; it is not erased
   or modeled as a guaranteed rejection. GIL/reference/output ownership must be
   proved at each source call by the application consumer. *)
Record gateway_cpython_contract {World Event}(backend:gateway_backend World Event)
    (python:World->python_world):Prop:={
  gateway_bytes_operation:forall object data size before world result after next observed,
    python_gil(python world)=true ->python_pending(python world)=None ->
    python_world_valid(python world)before ->python_live(python world)object ->
    python_output_cells before data size ->
    gateway_runtime_operation backend python_bytes_definition[object;data;size]
      before world result after next observed ->
    exists returned,result=Vint returned /\
      python_bytes_return(python world)object data size before returned after(python next);
  gateway_incref_operation:forall object before world result after next observed,
    python_gil(python world)=true ->python_world_valid(python world)before ->
    python_live(python world)object ->
    gateway_runtime_operation backend python_incref_definition[object]
      before world result after next observed ->
    python_incref_return(python world)object before(python next)after
}.

Theorem actual_bytes_runtime_return {World Event}(backend:gateway_backend World Event)ge python
    (runtime:gateway_cpython_contract backend python)object data size before world result after next
    observed continuation :
  python_gil(python world)=true ->python_pending(python world)=None ->
  python_world_valid(python world)before ->python_live(python world)object ->
  python_output_cells before data size ->
  gateway_step backend ge
    (gateway_live(Callstate python_bytes_definition[object;data;size]continuation before)world)
    (gateway_primitive observed)(gateway_live(Returnstate result continuation after)next) ->
  exists returned,result=Vint returned /\
    python_bytes_return(python world)object data size before returned after(python next).
Proof.
  intros GIL CLEAR VALID LIVE OUTPUT STEP.
  inversion STEP;subst.
  eapply(gateway_bytes_operation backend python runtime);try eassumption.
  cbn[gateway_runtime_operation python_bytes_definition];eassumption.
Qed.

Theorem actual_incref_runtime_return {World Event}(backend:gateway_backend World Event)ge python
    (runtime:gateway_cpython_contract backend python)object before world result after next
    observed continuation :
  python_gil(python world)=true ->python_world_valid(python world)before ->
  python_live(python world)object ->
  gateway_step backend ge
    (gateway_live(Callstate python_incref_definition[object]continuation before)world)
    (gateway_primitive observed)(gateway_live(Returnstate result continuation after)next) ->
  python_incref_return(python world)object before(python next)after.
Proof.
  intros GIL VALID LIVE STEP.
  inversion STEP;subst.
  eapply(gateway_incref_operation backend python runtime);try eassumption.
  cbn[gateway_runtime_operation python_incref_definition];eassumption.
Qed.
