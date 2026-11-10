(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Successful Unicode APIs decode the same received scalar bytes. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayRegistry GatewayPython GatewayObjects GatewayObjectDiscipline
  GatewayValueEntry GatewayScalarLength GatewayScalarConstructorCalls GatewayScalarTerminate GatewayScalarSizedFrames GatewayOperations
  GatewayRuntime GatewayFramedRuntime GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_scalar_mode_region(symbol object:block)position :Prop:=object=symbol /\0<=position<7.

Lemma gateway_scalar_received_object {World}python objects detached stable heap_allocation scalar slots stream_block stream_offset initial readonly original
    size object bytes memory world :
  @gateway_scalar_private_ready World python objects detached stable heap_allocation scalar slots stream_block stream_offset initial readonly original
    size object bytes memory world ->gateway_object_input memory(Vptr object Ptrofs.zero)bytes.
Proof.
  intros[[[[_[[_[_[_[BOUND[HEADER OWNED]]]]]SEPARATE]][COUNT LOAD]]TERMINATED]PRIVATE].
  exists object,Ptrofs.zero;split;[reflexivity|]. split.
  - eapply Mem.perm_valid_block;apply(OWNED(-8));lia.
  - split;[change(0+Z.of_nat(length bytes)<=Ptrofs.modulus);change Ptrofs.modulus with 18446744073709551616;
      change Int64.max_unsigned with 18446744073709551615 in BOUND;lia|].
    change(Mem.loadbytes memory object 0(Z.of_nat(length bytes))=Some(inj_bytes bytes));rewrite COUNT;exact LOAD.
Qed.

Lemma gateway_scalar_current_mode {World}python objects detached stable heap_allocation scalar slots stream_block stream_offset initial readonly original
    size object bytes memory world mode_symbol :
  @gateway_scalar_private_ready World python objects detached stable heap_allocation scalar slots stream_block stream_offset initial readonly original
    size object bytes memory world ->gateway_unicode_strict_mode original(Vptr mode_symbol Ptrofs.zero) ->
  (forall candidate position,gateway_scalar_mode_region mode_symbol candidate position ->readonly candidate position) ->
  gateway_unicode_strict_mode memory(Vptr mode_symbol Ptrofs.zero).
Proof.
  intros[[[[[[[[SIDE[STREAM[STABLE[INPUT FRAME]]]]SLOTS]TAG]SIZE]REST]PAYLOAD]TERMINATED]PRIVATE]MODE SUBSET.
  destruct MODE as[NULL|[candidate[offset[POINTER[LIVE[BOUND LOAD]]]]]];[discriminate|].
  inversion POINTER;subst candidate offset.
  right;exists mode_symbol,Ptrofs.zero;split;[reflexivity|]. split.
  - eapply Mem.valid_block_unchanged_on;[exact FRAME|exact LIVE].
  - split;[exact BOUND|]. eapply Mem.loadbytes_unchanged_on;[exact FRAME| |exact LOAD].
    intros position RANGE;apply SUBSET;split;[reflexivity|change(0<=position<7)in RANGE;exact RANGE].
Qed.

Theorem gateway_actual_utf8_scalar_bytes {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects detached decimal_float io stable thread_errno
    (runtime:gateway_thread_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (constructors:gateway_objects_runtime backend python objects decimal_float)
    definition heap_allocation scalar slots stream_block stream_offset initial readonly original size object bytes
    before world events result after next mode_symbol :
  gateway_object_api_definition gateway_api_unicode_utf8=Some definition ->
  gateway_scalar_private_ready python objects detached stable heap_allocation scalar slots stream_block stream_offset initial readonly original
    size object bytes before world ->Int64.unsigned size<=16777216 ->
  gateway_unicode_strict_mode original(Vptr mode_symbol Ptrofs.zero) ->
  (forall candidate position,gateway_scalar_mode_region mode_symbol candidate position ->readonly candidate position) ->
  gateway_steps backend ge(gateway_live(Callstate definition[Vptr object Ptrofs.zero;Vlong size;Vptr mode_symbol Ptrofs.zero]Kstop before)world)events
    (gateway_live(Returnstate result Kstop after)next) ->result<>Vnullptr ->
  exists characters,gateway_utf8_text bytes characters.
Proof.
  intros DEFINITION INPUT MAXIMUM MODE SUBSET RUN NONNULL.
  pose proof DEFINITION as EXTERNAL;unfold gateway_object_api_definition in EXTERNAL.
  destruct(gateway_program_definition(gateway_object_api_ident gateway_api_unicode_utf8)global_definitions)as[global|]eqn:GLOBAL;[|discriminate].
  destruct global as[function|variable];[|discriminate].
  destruct function as[function|external types result_type convention];[discriminate|].
  inversion EXTERNAL;subst definition.
  destruct(gateway_external_operation_of_run backend ge _ _ _ _ _ _ _ _ _ _ _ RUN)
    as(prefix &suffix &called &called_world &changed &changed_world &observed &EVENTS &PENDING &PREFIX &OPERATION &SUFFIX).
  pose proof(gateway_scalar_private_ambient backend python objects detached io stable thread_errno runtime heap_allocation scalar slots
    stream_block stream_offset initial readonly original size object bytes)as CLOSED.
  pose proof(gateway_pending_run_ready backend ge _ CLOSED
    (Callstate(External external types result_type convention)[Vptr object Ptrofs.zero;Vlong size;Vptr mode_symbol Ptrofs.zero]Kstop before)
    before world prefix called called_world INPUT PENDING PREFIX)as CALLED.
  pose proof CALLED as[[[READY[COUNT LOAD]]TERMINATED]PRIVATE].
  assert(SIZE:Vlong size=Vlong(Int64.repr(Z.of_nat(length bytes))))by(rewrite COUNT,Int64.repr_unsigned;reflexivity).
  assert(API:gateway_object_operation backend gateway_api_unicode_utf8
    [Vptr object Ptrofs.zero;Vlong(Int64.repr(Z.of_nat(length bytes)));Vptr mode_symbol Ptrofs.zero]
    called called_world result changed changed_world observed).
  { rewrite<-SIZE;eexists;split;[exact DEFINITION|exact OPERATION]. }
  destruct(gateway_runtime_utf8_constructor _ _ _ _ constructors called called_world(Vptr object Ptrofs.zero)bytes(Vptr mode_symbol Ptrofs.zero)
    result changed changed_world observed
    (gateway_scalar_private_side python objects detached stable heap_allocation scalar slots stream_block stream_offset initial readonly original
      size object bytes called called_world CALLED)
    (gateway_scalar_received_object python objects detached stable heap_allocation scalar slots stream_block stream_offset initial readonly original
      size object bytes called called_world CALLED)
    ltac:(change Int64.max_signed with 9223372036854775807;lia)
    (gateway_scalar_current_mode python objects detached stable heap_allocation scalar slots stream_block stream_offset initial readonly original
      size object bytes called called_world mode_symbol CALLED MODE SUBSET)API NONNULL)
    as(characters &DECODED &RETURN).
  exists characters;exact DECODED.
Qed.
