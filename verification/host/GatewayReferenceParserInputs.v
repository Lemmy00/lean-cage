(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Recursive source induction receives the same initialized stream,
   retained strict-mode bytes and saved source owners; its run bound is proof bookkeeping. *)
From Stdlib Require Import ZArith List.
From compcert Require Import AST Values Memory Integers Ctypes Clight.
Require Import CallContexts.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayObjectDiscipline GatewayValueEntry GatewayValueContext
  GatewayReferenceLedger GatewayReferenceThreads GatewayReferenceStackBound GatewayReferenceValueProperties GatewayReferenceParseResult
  GatewayScalarDecoding GatewayStreamInterface.

Definition gateway_reference_short_parser {World Event}(backend:gateway_backend World Event)
    (python:World->python_world)(objects:World->gateway_object_heap)decimal_float detached(io:Event->option gateway_native_io)
    (stable:World->block->Z->Prop)mode_symbol run_limit:Prop:=
  forall context ledger held arguments stream_block stream_offset initial readonly original before world events value after next,
    is_call_cont context->gateway_reference_ledger_well_formed ledger->gateway_reference_stack_bound context ledger->
    gateway_reference_scope python objects decimal_float ledger held world->gateway_reference_graphs_only held->
    gateway_unicode_strict_mode original(Vptr mode_symbol Ptrofs.zero)->
    (forall object position,gateway_scalar_mode_region mode_symbol object position->readonly object position)->
    gateway_value_stream arguments=Vptr stream_block stream_offset->
    gateway_value_context(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)stream_block stream_offset initial readonly original before world->
    (forall object position,readonly object position->gateway_native_private(python world)object)->
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal f_host_value)(gateway_value_arguments_list arguments)Kstop before)world)events
      (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->(length events<run_limit)%nat->
    gateway_reference_parse_result python objects decimal_float detached io stable(Clight.globalenv prog)context ledger held
      stream_block stream_offset initial readonly original events value after next.

Lemma gateway_value_context_current_mode {World}native stable discipline stream_block stream_offset initial readonly original memory world mode_symbol:
  @gateway_value_context World native stable discipline stream_block stream_offset initial readonly original memory world->
  gateway_unicode_strict_mode original(Vptr mode_symbol Ptrofs.zero)->
  (forall object position,gateway_scalar_mode_region mode_symbol object position->readonly object position)->
  gateway_unicode_strict_mode memory(Vptr mode_symbol Ptrofs.zero).
Proof.
  intros[SIDE[STREAM[STABLE[INPUT FRAME]]]]MODE SUBSET.
  destruct MODE as[NULL|[candidate[offset[POINTER[LIVE[BOUND LOAD]]]]]];[discriminate|].
  inversion POINTER;subst candidate offset.
  right;exists mode_symbol,Ptrofs.zero;split;[reflexivity|]. split.
  - eapply Mem.valid_block_unchanged_on;[exact FRAME|exact LIVE].
  - split;[exact BOUND|]. eapply Mem.loadbytes_unchanged_on;[exact FRAME| |exact LOAD].
    intros position RANGE;apply SUBSET;split;[reflexivity|change(0<=position<7)%Z in RANGE;exact RANGE].
Qed.
