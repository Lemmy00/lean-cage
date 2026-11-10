(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The filesystem codec consumes the same received scalar bytes. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayRegistry GatewayPython GatewayObjects GatewayObjectDiscipline
  GatewayScalarLength GatewayScalarContext GatewayScalarTerminate GatewayScalarSizedFrames GatewayScalarConstructorCalls GatewayScalarDecoding
  GatewayOperations GatewayRuntime GatewayFramedRuntime GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Open Scope Z_scope.

Lemma gateway_scalar_path_request {World}python objects detached stable heap_allocation slots stream_block stream_offset initial readonly original
    size object bytes memory world decimal_float characters:
  @gateway_scalar_private_ready World python objects detached stable heap_allocation gateway_scalar_path slots stream_block stream_offset initial
    readonly original size object bytes memory world ->Int64.unsigned size<=4095 ->gateway_filesystem_text bytes characters ->
  gateway_constructor_request decimal_float(objects world)memory gateway_api_unicode_fs[Vptr object Ptrofs.zero;Vlong size]
    (gateway_unicode_object characters).
Proof.
  intros READY MAXIMUM DECODED;pose proof READY as[[[BUFFER[COUNT LOAD]]TERMINATED]PRIVATE].
  replace(Vlong size)with(Vlong(Int64.repr(Z.of_nat(length bytes))))by(rewrite COUNT,Int64.repr_unsigned;reflexivity).
  apply gateway_request_unicode_filesystem;[eapply gateway_scalar_received_object;exact READY|exact DECODED|].
  change Int64.max_signed with 9223372036854775807;lia.
Qed.

Theorem gateway_actual_filesystem_scalar_bytes {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects detached decimal_float io stable thread_errno
    (runtime:gateway_thread_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (constructors:gateway_objects_runtime backend python objects decimal_float)
    definition heap_allocation slots stream_block stream_offset initial readonly original size object bytes
    before world events result after next:
  gateway_object_api_definition gateway_api_unicode_fs=Some definition ->
  gateway_scalar_private_ready python objects detached stable heap_allocation gateway_scalar_path slots stream_block stream_offset initial
    readonly original size object bytes before world ->Int64.unsigned size<=4095 ->
  gateway_steps backend ge(gateway_live(Callstate definition[Vptr object Ptrofs.zero;Vlong size]Kstop before)world)events
    (gateway_live(Returnstate result Kstop after)next) ->result<>Vnullptr ->
  exists characters,gateway_filesystem_text bytes characters.
Proof.
  intros DEFINITION INPUT MAXIMUM RUN NONNULL.
  pose proof DEFINITION as EXTERNAL;unfold gateway_object_api_definition in EXTERNAL.
  destruct(gateway_program_definition(gateway_object_api_ident gateway_api_unicode_fs)global_definitions)as[global|]eqn:GLOBAL;[|discriminate].
  destruct global as[function|variable];[|discriminate].
  destruct function as[function|external types result_type convention];[discriminate|].
  inversion EXTERNAL;subst definition.
  destruct(gateway_external_operation_of_run backend ge _ _ _ _ _ _ _ _ _ _ _ RUN)
    as(prefix &suffix &called &called_world &changed &changed_world &observed &EVENTS &PENDING &PREFIX &OPERATION &SUFFIX).
  pose proof(gateway_scalar_private_ambient backend python objects detached io stable thread_errno runtime heap_allocation gateway_scalar_path slots
    stream_block stream_offset initial readonly original size object bytes)as CLOSED.
  pose proof(gateway_pending_run_ready backend ge _ CLOSED
    (Callstate(External external types result_type convention)[Vptr object Ptrofs.zero;Vlong size]Kstop before)
    before world prefix called called_world INPUT PENDING PREFIX)as CALLED.
  pose proof CALLED as[[[READY[COUNT LOAD]]TERMINATED]PRIVATE].
  assert(SIZE:Vlong size=Vlong(Int64.repr(Z.of_nat(length bytes))))by(rewrite COUNT,Int64.repr_unsigned;reflexivity).
  assert(API:gateway_object_operation backend gateway_api_unicode_fs
    [Vptr object Ptrofs.zero;Vlong(Int64.repr(Z.of_nat(length bytes)))]called called_world result changed changed_world observed).
  { rewrite<-SIZE;eexists;split;[exact DEFINITION|exact OPERATION]. }
  destruct(gateway_runtime_filesystem_constructor _ _ _ _ constructors called called_world(Vptr object Ptrofs.zero)bytes result changed changed_world observed
    (gateway_scalar_private_side python objects detached stable heap_allocation gateway_scalar_path slots stream_block stream_offset initial readonly original
      size object bytes called called_world CALLED)
    (gateway_scalar_received_object python objects detached stable heap_allocation gateway_scalar_path slots stream_block stream_offset initial readonly original
      size object bytes called called_world CALLED)
    ltac:(change Int64.max_signed with 9223372036854775807;lia)API NONNULL)as(characters &DECODED &RETURN).
  exists characters;exact DECODED.
Qed.
