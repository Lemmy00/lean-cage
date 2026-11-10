(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The retained references come from the maintained native function. *)
From Stdlib Require Import List ZArith.
From compcert Require Import Maps Integers AST Values Memory Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayRuntime GatewayBindings
  GatewayArgumentContext GatewayArgumentRoots.
Import ListNotations.

Lemma actual_arguments_incref_binding:
  gateway_function_binding(Clight.globalenv prog)_Py_IncRef python_incref_definition.
Proof. apply gateway_actual_function_binding;vm_compute;reflexivity. Qed.

Theorem gateway_actual_argument_roots {World Event}(backend:gateway_backend World Event)
    (python:World->python_world)(runtime:gateway_cpython_contract backend python)
    (quiet:gateway_quiet_gil backend python)array offset values original before world events returned after next:
  gateway_argument_context python array offset values[]original before world->(length values<=14)%nat->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_arguments_retain)
      [Vptr array offset;Vint(Int.repr(Z.of_nat(length values)))]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next)->
  returned=Vundef /\gateway_argument_context python array offset values values original after next /\
    (forall object,In object values->object<>Vnullptr->(0<python_native_strong(python next)object)%nat).
Proof.
  destruct actual_arguments_incref_binding as[symbol[SYMBOL FUNCTION]].
  eapply actual_arguments_retain;[exact runtime|exact quiet|exact SYMBOL|exact FUNCTION].
Qed.
