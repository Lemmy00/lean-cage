(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual recursive decoder produces one source-owned graph
   and exact same-stream framing; each recursive use is strictly shorter in that same run. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine CallContexts.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline
  GatewayObjectConstants GatewayObjectThreads GatewayObjectInstances GatewayContainerABI GatewayValueEntry GatewayValueContext
  GatewayValueKnownTag GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceThreads GatewayReferenceStackBound
  GatewayReferenceValueProperties GatewayReferenceParserInputs GatewayReferenceParseResult GatewayReferenceParseScalars GatewayReferenceParseInteger
  GatewayReferenceParseNumber GatewayReferenceArrayValue GatewayReferenceDictionaryValue GatewayNativeMemory GatewayNoMemory GatewayObjectEvents
  GatewayScalarDecoding GatewayPathEvents GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Section ActualParser.
Context {World Event}(backend:gateway_backend World Event)
  (python:World->python_world)(objects:World->gateway_object_heap)(decimal_float:list Z->Floats.float->Prop)
  (detached:Values.val->Memory.mem->World->Prop)(io:Event->option gateway_native_io)
  (stable:World->block->Z->Prop)(thread_errno:World->int)(heap_allocation:block->Z->Prop).
Let native:=fun current object=>gateway_native_private(python current)object.
Let base:=gateway_python_discipline python objects detached.
Context(runtime:gateway_thread_runtime backend io native stable base thread_errno)
  (allocations:gateway_native_memory_runtime backend io native stable base heap_allocation)
  (constructors:gateway_objects_runtime backend python objects decimal_float)
  (references:gateway_reference_runtime backend python objects)
  (reference_threads:gateway_reference_thread_contract backend native stable base heap_allocation python objects)
  (containers:gateway_container_runtime backend python objects)(abi:gateway_container_abi_runtime backend python objects)
  (instances:gateway_instance_runtime backend(Clight.globalenv prog)python objects(fun _ _ _=>Logic.False))
  (errors:gateway_no_memory_runtime backend python)(projection:gateway_direct_io_projection backend io)
  (none_symbol mode_symbol:block)
  (constants:gateway_none_runtime python objects(Vptr none_symbol Ptrofs.zero))
  (NONE:Genv.find_symbol(Clight.globalenv prog)__Py_NoneStruct=Some none_symbol)
  (MODE_SYMBOL:Genv.find_symbol(Clight.globalenv prog)___stringlit_8=Some mode_symbol).

Theorem gateway_reference_actual_short_parser:
  forall run_limit,gateway_reference_short_parser backend python objects decimal_float detached io stable mode_symbol run_limit.
Proof.
  intro run_limit;induction run_limit using lt_wf_ind.
  unfold gateway_reference_short_parser;intros context ledger held arguments stream_block stream_offset initial readonly original
    before world events value after next CALL WELL STACK SCOPE GRAPHS MODE MODE_REGION STREAM INPUT READONLY RUN NONNULL LIMIT.
  assert(BOUND:gateway_reference_source_bound(Clight.globalenv prog)
    (Callstate(Internal f_host_value)(gateway_value_arguments_list arguments)context before)ledger).
  { eapply gateway_reference_stack_call_bound;exact STACK. }
  assert(CHILDREN:gateway_reference_short_parser backend python objects decimal_float detached io stable mode_symbol(length events)).
  { apply H;exact LIMIT. }
  destruct(gateway_actual_value_known_tag backend io native stable base thread_errno runtime arguments before world events value after next
    stream_block stream_offset initial readonly original STREAM INPUT RUN NONNULL)as(byte &RANGE &OBSERVED).
  destruct(Z.eq_dec(Byte.unsigned byte)0)as[TAG|TAG0].
  - eapply gateway_reference_parse_null;eassumption.
  - destruct(Z.eq_dec(Byte.unsigned byte)1)as[TAG|TAG1].
    + eapply gateway_reference_parse_boolean with(flag:=false);eassumption.
    + destruct(Z.eq_dec(Byte.unsigned byte)2)as[TAG|TAG2].
      * eapply gateway_reference_parse_boolean with(flag:=true);eassumption.
      * destruct(Z.eq_dec(Byte.unsigned byte)3)as[TAG|TAG3].
        -- eapply gateway_reference_parse_integer;eassumption.
        -- destruct(Z.eq_dec(Byte.unsigned byte)4)as[TAG|TAG4].
           ++ eapply gateway_reference_parse_text;eassumption.
           ++ destruct(Z.eq_dec(Byte.unsigned byte)5)as[TAG|TAG5].
              ** eapply gateway_reference_parse_bytes;eassumption.
              ** destruct(Z.eq_dec(Byte.unsigned byte)6)as[TAG|TAG6].
                 --- eapply gateway_reference_parse_path;eassumption.
                 --- destruct(Z.eq_dec(Byte.unsigned byte)7)as[TAG|TAG7].
                     +++ eapply gateway_reference_parse_array with(children:=CHILDREN);try eassumption;lia.
                     +++ destruct(Z.eq_dec(Byte.unsigned byte)8)as[TAG|TAG8].
                         *** eapply gateway_reference_parse_dictionary with(children:=CHILDREN);try eassumption;lia.
                         *** assert(TAG:Byte.unsigned byte=9)by lia.
                             eapply gateway_reference_parse_number;eassumption.
Qed.

Theorem gateway_reference_actual_parser context ledger held arguments stream_block stream_offset initial readonly original
    before world events value after next:
  is_call_cont context->gateway_reference_ledger_well_formed ledger->gateway_reference_stack_bound context ledger->
  gateway_reference_scope python objects decimal_float ledger held world->gateway_reference_graphs_only held->
  gateway_unicode_strict_mode original(Vptr mode_symbol Ptrofs.zero)->
  (forall object position,gateway_scalar_mode_region mode_symbol object position->readonly object position)->
  gateway_value_stream arguments=Vptr stream_block stream_offset->
  gateway_value_context native stable base stream_block stream_offset initial readonly original before world->
  (forall object position,readonly object position->native world object)->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_value)(gateway_value_arguments_list arguments)Kstop before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  gateway_reference_parse_result python objects decimal_float detached io stable(Clight.globalenv prog)context ledger held
    stream_block stream_offset initial readonly original events value after next.
Proof.
  intros CALL WELL STACK SCOPE GRAPHS MODE MODE_REGION STREAM INPUT READONLY RUN NONNULL.
  eapply(gateway_reference_actual_short_parser(S(length events)));try eassumption;lia.
Qed.
End ActualParser.
