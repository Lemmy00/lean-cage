(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A successful integer branch has checked every received byte
   before its actual decimal constructor; lexical rejection remains a null source return. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayValueEntry GatewayScalarLength GatewayScalarContext
  GatewayScalarReadPath GatewayScalarPayloadMemory GatewayScalarTerminate GatewayScalarBytesPath GatewayScalarCleanup
  GatewayIntegerMemory GatewayIntegerCanonical GatewayIntegerLexical GatewayIntegerTail GatewayIntegerScan GatewayIntegerPrefixSource
  GatewaySourcePaths GatewaySourceSegments GatewayObjects GatewayBindings GatewayFramedRuntime GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Open Scope Z_scope.

Theorem actual_gateway_integer_binding:
  exists definition,gateway_object_api_definition gateway_api_long_string=Some definition /\
    gateway_function_binding(Clight.globalenv prog)_PyLong_FromString definition /\
    type_of_fundef definition=Tfunction[tptr tschar;tptr(tptr tschar);tint](tptr(Tstruct __object noattr))cc_default.
Proof.
  eexists;split;[reflexivity|]. split;[apply gateway_actual_function_binding;vm_compute;reflexivity|reflexivity].
Qed.

Theorem gateway_actual_integer_constructor_cut {World Event}(backend:gateway_backend World Event)
    io native stable discipline thread_errno(runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    heap_allocation slots parameters stream_block stream_offset initial readonly original size object bytes before world events value after next:
  parameters!_bytes=Some(Vptr object Ptrofs.zero)->Int64.unsigned size<=32->
  gateway_scalar_payload_ready native stable discipline heap_allocation gateway_scalar_long slots stream_block stream_offset initial readonly original
    size object bytes before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate(Vint Int.zero)(gateway_scalar_read_cont slots parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  exists definition called_parameters prefix constructing suffix constructor_before constructor_world constructor_after constructor_next integer,
    gateway_object_api_definition gateway_api_long_string=Some definition /\gateway_decimal bytes integer /\
    events=prefix++constructing++suffix /\Forall(fun event=>event=gateway_source E0 \/event=gateway_ambient)prefix /\
    called_parameters!_bytes=Some(Vptr object Ptrofs.zero) /\
    gateway_scalar_terminated_ready native stable discipline heap_allocation gateway_scalar_long slots stream_block stream_offset initial readonly original
      size object bytes constructor_before constructor_world /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate definition[Vptr object Ptrofs.zero;Vnullptr;Vint(Int.repr 10)]Kstop constructor_before)constructor_world)constructing
      (gateway_live(Returnstate value Kstop constructor_after)constructor_next) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate value(gateway_scalar_constructor_cont _t'19 slots called_parameters)constructor_after)constructor_next)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros BUFFER MAXIMUM INPUT RUN NONNULL.
  pose proof(proj1(proj2 INPUT))as COUNT.
  assert(SIZE:size=Int64.repr(Z.of_nat(length bytes)))by(rewrite COUNT,Int64.repr_unsigned;reflexivity).
  assert(BOUND:Z.of_nat(length bytes)<=32)by lia.
  subst size.
  set(property:=gateway_scalar_terminated_ready native stable discipline heap_allocation gateway_scalar_long slots stream_block stream_offset initial readonly original
    (Int64.repr(Z.of_nat(length bytes)))object bytes).
  pose proof(gateway_scalar_terminated_ambient backend io native stable discipline thread_errno runtime heap_allocation gateway_scalar_long slots stream_block stream_offset
    initial readonly original(Int64.repr(Z.of_nat(length bytes)))object bytes)as CLOSED.
  assert(TAG:forall memory current,property memory current->Mem.loadv Mint64 memory(Vptr(gateway_value_tag_slot slots)Ptrofs.zero)=Some(Vlong(Int64.repr 3))).
  { intros memory current[PAYLOAD TERM];pose proof PAYLOAD as[STORAGE REST];pose proof STORAGE as[SIZED HEAP];exact(proj2(proj1 SIZED)). }
  assert(LENGTH:forall memory current,property memory current->Mem.loadv Mint64 memory(Vptr(gateway_value_size_slot slots)Ptrofs.zero)=Some(Vlong(Int64.repr(Z.of_nat(length bytes))))).
  { intros memory current[PAYLOAD TERM];pose proof PAYLOAD as[STORAGE REST];pose proof STORAGE as[SIZED HEAP];exact(proj2 SIZED). }
  assert(LOADS:forall index byte,nth_error bytes index=Some byte->forall memory current,property memory current->
    Mem.loadv Mint8signed memory(Vptr object(Ptrofs.repr(Z.of_nat index)))=Some(Vint(Int.repr(Byte.signed byte)))).
  { intros index byte SELECTED memory current[[STORAGE[SIZE LOAD]]TERM].
    eapply gateway_integer_byte_load with(bytes:=bytes);[lia|rewrite SIZE;exact LOAD|exact SELECTED]. }
  destruct(gateway_integer_lexical_segment backend(Clight.globalenv prog)property slots parameters object bytes before CLOSED BOUND BUFFER TAG LENGTH LOADS)
    as(loop_parameters &LEXICAL &LOOP_BYTES &LOOP_NULL &LOOP_FLAG).
  pose proof(gateway_scalar_terminator_segment backend(Clight.globalenv prog)io native stable discipline thread_errno runtime heap_allocation gateway_scalar_long slots parameters
    stream_block stream_offset initial readonly original(Int64.repr(Z.of_nat(length bytes)))object bytes before BUFFER)as TERMINATE.
  pose proof(gateway_integer_segments_append backend(Clight.globalenv prog)_ _ _ _ _ _ TERMINATE LEXICAL)as PATH.
  destruct(gateway_source_segment_cut backend(Clight.globalenv prog)_ _ _ _ PATH before world events value after next INPUT RUN)
    as(lexical_prefix &from_loop &loop_before &loop_world &LEXICAL_EVENTS &LEXICAL_QUIET &TO_LOOP &LOOP_READY &LOOP_REST).
  assert(CHECK:gateway_integer_check bytes=true).
  { destruct(gateway_integer_check bytes)eqn:CHECK;[reflexivity|].
    pose proof(gateway_integer_rejected_segment backend(Clight.globalenv prog)property slots loop_parameters loop_before CLOSED LOOP_FLAG)as REJECT.
    destruct(gateway_source_segment_cut backend(Clight.globalenv prog)_ _ _ _ REJECT loop_before loop_world from_loop value after next LOOP_READY LOOP_REST)
      as(reject_prefix &reject_suffix &rejected_memory &rejected_world &REJECT_EVENTS &REJECT_QUIET &TO_REJECT &REJECT_READY &REJECT_REST).
    exfalso;apply NONNULL;eapply gateway_integer_rejected_is_null;[exact LOOP_NULL|exact REJECT_REST]. }
  destruct(gateway_integer_check_sound bytes CHECK)as[integer DECIMAL].
  destruct actual_gateway_integer_binding as(definition &DEFINITION &[symbol[SYMBOL FUNCTION]]&TYPE).
  pose proof(gateway_integer_constructor_path backend(Clight.globalenv prog)property slots loop_parameters object loop_before symbol definition CLOSED LOOP_BYTES
    ltac:(rewrite CHECK in LOOP_FLAG;exact LOOP_FLAG)SYMBOL FUNCTION TYPE)as CONSTRUCTOR.
  destruct(gateway_source_path_cut backend(Clight.globalenv prog)_ _ _ _ _ _ CONSTRUCTOR loop_before loop_world from_loop value after next LOOP_READY LOOP_REST)
    as(source_prefix &rest &constructor_before &constructor_world &SOURCE_EVENTS &SOURCE_QUIET &TO_CONSTRUCTOR &READY &FROM_CONSTRUCTOR).
  destruct(gateway_return_cut backend(Clight.globalenv prog)definition[Vptr object Ptrofs.zero;Vnullptr;Vint(Int.repr 10)]
    (gateway_scalar_constructor_cont _t'19 slots loop_parameters)constructor_before constructor_world rest(Returnstate value Kstop after)next
    ltac:(cbn;exact I)ltac:(cbn;lia)FROM_CONSTRUCTOR)
    as(constructing &suffix &returned &constructor_after &constructor_next &REST_EVENTS &CONSTRUCTOR_RUN &REST).
  pose proof(proj1(gateway_actual_scalar_cleanup_cut backend _t'19 slots loop_parameters object constructor_after constructor_next suffix
    returned value after next ltac:(discriminate)LOOP_BYTES REST))as SAME;subst returned.
  exists definition,loop_parameters,(lexical_prefix++source_prefix),constructing,suffix,constructor_before,constructor_world,constructor_after,constructor_next,integer.
  split;[exact DEFINITION|]. split;[exact DECIMAL|]. split;[rewrite LEXICAL_EVENTS,SOURCE_EVENTS,REST_EVENTS;repeat rewrite app_assoc;reflexivity|].
  split;[apply Forall_app;split;assumption|]. split;[exact LOOP_BYTES|]. split;[exact READY|]. split;assumption.
Qed.
