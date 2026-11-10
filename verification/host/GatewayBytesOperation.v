(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A real successful helper uses one actual checked CPython byte operation. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayPure GatewayRuntime
  GatewayPython GatewayAllocation GatewayPrefix GatewayFieldFailure GatewayOperations.
Import ListNotations.

Definition field_bytes_ready {World}(python:World->python_world)locals arguments memory world:Prop:=
  python_gil(python world)=true /\python_pending(python world)=None /\
  python_world_valid(python world)memory /\python_live(python world)(field_object arguments) /\
  python_output_cells memory(Vptr(field_local_data locals)Ptrofs.zero)
    (Vptr(field_local_size locals)Ptrofs.zero).

Theorem actual_field_bytes_operation_success {World Event}(backend:gateway_backend World Event)ge
    python(runtime:gateway_cpython_contract backend python)locals arguments before world events after final_world :
  field_bytes_ready python locals arguments before world ->
  gateway_runtime_discipline backend(field_bytes_ready python locals arguments) ->
  gateway_steps backend ge
    (gateway_live(Callstate python_bytes_definition
      [field_object arguments;Vptr(field_local_data locals)Ptrofs.zero;
        Vptr(field_local_size locals)Ptrofs.zero](field_api_cont locals arguments Kstop)before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)final_world) ->
  exists pending returned_suffix caller_suffix called_memory called_world primitive_memory primitive_world
      returned_memory returned_world observed bytes,
    events=(pending++gateway_primitive observed::returned_suffix)++caller_suffix /\
    Forall gateway_pending_event pending /\
    gateway_steps backend ge
      (gateway_live(Callstate python_bytes_definition
        [field_object arguments;Vptr(field_local_data locals)Ptrofs.zero;
          Vptr(field_local_size locals)Ptrofs.zero]Kstop before)world)pending
      (gateway_live(Callstate python_bytes_definition
        [field_object arguments;Vptr(field_local_data locals)Ptrofs.zero;
          Vptr(field_local_size locals)Ptrofs.zero]Kstop called_memory)called_world) /\
    gateway_runtime_operation backend python_bytes_definition
      [field_object arguments;Vptr(field_local_data locals)Ptrofs.zero;
        Vptr(field_local_size locals)Ptrofs.zero]called_memory called_world
      (Vint Int.zero)primitive_memory primitive_world observed /\
    python_bytes_return(python called_world)(field_object arguments)
      (Vptr(field_local_data locals)Ptrofs.zero)(Vptr(field_local_size locals)Ptrofs.zero)
      called_memory Int.zero primitive_memory(python primitive_world) /\
    python_values(python called_world)(field_object arguments)=Some(python_byte_value bytes) /\
    python primitive_world=python called_world /\
    gateway_steps backend ge(gateway_live(Returnstate(Vint Int.zero)Kstop primitive_memory)primitive_world)
      returned_suffix(gateway_live(Returnstate(Vint Int.zero)Kstop returned_memory)returned_world) /\
    gateway_steps backend ge
      (gateway_live(Returnstate(Vint Int.zero)(field_api_cont locals arguments Kstop)returned_memory)returned_world)
      caller_suffix(gateway_live(Returnstate(Vint Int.zero)Kstop after)final_world).
Proof.
  intros READY DISCIPLINE RUN.
  destruct(gateway_return_cut backend ge python_bytes_definition
    [field_object arguments;Vptr(field_local_data locals)Ptrofs.zero;
      Vptr(field_local_size locals)Ptrofs.zero](field_api_cont locals arguments Kstop)
    before world events(Returnstate(Vint Int.zero)Kstop after)final_world
    ltac:(reflexivity)ltac:(cbn[gateway_cont_weight field_api_cont gateway_continuation];lia)RUN)
    as[operation_events[caller_suffix[returned[returned_memory[returned_world[EVENTS[OPERATION CALLER]]]]]]].
  destruct(gateway_external_operation_of_run backend ge _ _ _ _ _ before world operation_events returned
    returned_memory returned_world OPERATION)
    as[pending[returned_suffix[called_memory[called_world[primitive_memory[primitive_world[observed
      [OPERATIONS[PENDING[PREFIX[PRIMITIVE RETURNED]]]]]]]]]]].
  assert(AT_OPERATION:field_bytes_ready python locals arguments called_memory called_world).
  { eapply gateway_pending_run_ready with
      (source:=Callstate python_bytes_definition
        [field_object arguments;Vptr(field_local_data locals)Ptrofs.zero;
          Vptr(field_local_size locals)Ptrofs.zero]Kstop before);
      try eassumption. }
  destruct AT_OPERATION as[GIL[CLEAR[VALID[LIVE OUTPUT]]]].
  assert(RAW:gateway_runtime_operation backend python_bytes_definition
    [field_object arguments;Vptr(field_local_data locals)Ptrofs.zero;
      Vptr(field_local_size locals)Ptrofs.zero]called_memory called_world returned
      primitive_memory primitive_world observed)by exact PRIMITIVE.
  destruct(gateway_bytes_operation backend python runtime (field_object arguments)
    (Vptr(field_local_data locals)Ptrofs.zero)(Vptr(field_local_size locals)Ptrofs.zero)
    called_memory called_world returned primitive_memory primitive_world observed
    GIL CLEAR VALID LIVE OUTPUT RAW)as[result[VALUE BYTES]].
  subst returned.
  pose proof(actual_successful_field_requires_bytes_success backend ge locals arguments returned_memory
    returned_world caller_suffix after final_world result CALLER)as ZERO;subst result.
  destruct(python_bytes_success_actual_values _ _ _ _ _ _ _ _ BYTES eq_refl)
    as[bytes[middle[SAME[VALUES[DATA SIZE]]]]].
  exists pending,returned_suffix,caller_suffix,called_memory,called_world,primitive_memory,primitive_world,
    returned_memory,returned_world,observed,bytes.
  split;[congruence|]. split;[exact PENDING|]. split;[exact PREFIX|]. split;[exact RAW|].
  split;[exact BYTES|]. split;[exact VALUES|]. split;[exact SAME|]. split;assumption.
Qed.
