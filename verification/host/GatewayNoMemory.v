(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: The individual CPython allocation-error API returns NULL. *)
From Stdlib Require Import List String.
From compcert Require Import Integers AST Values Memory Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayRegistry GatewayMachine GatewayPython GatewayObjects
  GatewayObjectDiscipline GatewayRuntime GatewayOperations GatewayThreadRuntime GatewayStreamInterface.
Import ListNotations.

Definition gateway_no_memory_definition :Ctypes.fundef Clight.function:=External
  (EF_external "PyErr_NoMemory"(mksignature[]Xptr cc_default))[](tptr(Tstruct __object noattr))cc_default.

Theorem gateway_no_memory_actual_abi :
  gateway_program_definition _PyErr_NoMemory global_definitions=Some(Gfun gateway_no_memory_definition).
Proof. reflexivity. Qed.

Record gateway_no_memory_runtime {World Event}(backend:gateway_backend World Event)(python:World->python_world):Prop:={
  gateway_no_memory_result:forall before world result after next observed,
    python_world_valid(python world)before ->python_gil(python world)=true ->
    gateway_runtime_operation backend gateway_no_memory_definition[]before world result after next observed ->result=Vnullptr
}.

Theorem gateway_actual_no_memory_run {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects detached io native stable thread_errno
    (runtime:gateway_thread_runtime backend io native stable(gateway_python_discipline python objects detached)thread_errno)
    (errors:gateway_no_memory_runtime backend python)before world events value after next :
  gateway_objects_ready(python world)(objects world)before ->
  gateway_steps backend ge(gateway_live(Callstate gateway_no_memory_definition[]Kstop before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value=Vnullptr.
Proof.
  intros READY RUN.
  destruct(gateway_external_operation_of_run backend ge _ _ _ _ _ _ _ _ _ _ _ RUN)
    as(prefix &suffix &called &called_world &changed &changed_world &observed &EVENTS &PENDING &PREFIX &OPERATION &SUFFIX).
  assert(CALLED:gateway_objects_ready(python called_world)(objects called_world)called).
  { exact(gateway_pending_run_ready backend ge _
      (fun first current last following SIDE INTERFERENCE=>proj1(gateway_thread_ambient _ _ _ _ _ _ runtime None
        first current last following SIDE INTERFERENCE))
      (Callstate gateway_no_memory_definition[]Kstop before)before world prefix called called_world READY PENDING PREFIX). }
  eapply gateway_no_memory_result;[exact errors|exact(proj1(proj1 CALLED))|exact(proj1(proj2 CALLED))|exact OPERATION].
Qed.
