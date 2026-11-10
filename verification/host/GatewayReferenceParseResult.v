(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Recursive source consumers return the actual decoded graph and
   the shared framing of the bytes read on that same owned response descriptor. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Values Memory Clight.
From HostGateway Require Import GatewayImport GatewayPython GatewayObjects GatewayObjectDiscipline GatewayValue GatewayReferenceLedger
  GatewayReferencePlaces GatewayReferenceDecoded GatewayContainerEncoding GatewayValueContext GatewayPathEvents GatewayStreamInterface.

Definition gateway_reference_parse_result {World Event}(python:World->python_world)(objects:World->gateway_object_heap)decimal_float detached
    (io:Event->option gateway_native_io)(stable:World->block->Z->Prop)(ge:Clight.genv)context ledger held
    stream_block stream_offset initial readonly original events value after next:Prop:=
  exists final final_stream wire ticket,
    gateway_reference_decoded python objects decimal_float ge context ledger held wire ticket value final after next /\
    gateway_value_context(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)stream_block stream_offset final_stream readonly original after next /\
    (forall candidate position,readonly candidate position->gateway_native_private(python next)candidate) /\
    stream_descriptor final_stream=stream_descriptor initial /\
    gateway_response_frame(LeanCage_Host_GatewayResponseCode_Subject_value wire)
      (gateway_received_bytes io(stream_descriptor initial)events).
