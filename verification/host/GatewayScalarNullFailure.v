(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A NULL allocation cannot become a successful decoded value. *)
From Stdlib Require Import List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayObjectDiscipline
  GatewayNoMemory GatewayNoMemoryBinding GatewayBindings GatewayScalarNull GatewayScalarAllocationPath GatewayValueEntry
  GatewaySourcePaths GatewayContexts GatewayReturns GatewayOperations GatewayThreadRuntime GatewayStreamInterface GatewayFramedRuntime.
Import ListNotations.

Theorem gateway_actual_null_scalar_allocation {World Event}(backend:gateway_backend World Event)
    python objects detached io native stable thread_errno
    (runtime:gateway_thread_runtime backend io native stable(gateway_python_discipline python objects detached)thread_errno)
    (errors:gateway_no_memory_runtime backend python)slots parameters before world events value after next :
  gateway_objects_ready(python world)(objects world)before ->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate Vnullptr(gateway_value_scalar_malloc_cont slots parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value=Vnullptr.
Proof.
  intros INPUT RUN.
  set(ready:=fun memory current=>gateway_objects_ready(python current)(objects current)memory).
  assert(CLOSED:gateway_ambient_closed backend ready).
  { intros first current last following SIDE INTERFERENCE.
    exact(proj1(gateway_thread_ambient _ _ _ _ _ _ runtime None first current last following SIDE INTERFERENCE)). }
  destruct gateway_actual_no_memory_binding as[symbol[SYMBOL FUNCTION]].
  pose proof(gateway_scalar_null_path backend(Clight.globalenv prog)ready slots parameters before symbol
    CLOSED SYMBOL FUNCTION)as PATH.
  destruct(gateway_source_path_cut backend(Clight.globalenv prog)_ _ _ _ _ _ PATH before world events value after next INPUT RUN)
    as(prefix &rest &called &called_world &EVENTS &QUIET &PREFIX &READY &FROM_ERROR).
  destruct(gateway_return_cut backend(Clight.globalenv prog)gateway_no_memory_definition[]
    (gateway_scalar_no_memory_cont slots parameters)called called_world rest(Returnstate value Kstop after)next
    ltac:(cbn;exact I)ltac:(cbn;lia)FROM_ERROR)
    as(error &suffix &returned &error_after &error_world &REST_EVENTS &ERROR_RUN &REST).
  pose proof(gateway_actual_no_memory_run backend(Clight.globalenv prog)python objects detached io native stable thread_errno
    runtime errors called called_world error returned error_after error_world READY ERROR_RUN)as NULL.
  subst returned;eapply gateway_constant_path_actual;
    [exact(gateway_scalar_no_memory_return_path(Clight.globalenv prog)slots parameters error_after)|exact REST].
Qed.
