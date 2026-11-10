(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Half-close has its own single-operation memory and return law. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayRuntime GatewayStreamInterface GatewayThreadRuntime GatewayExchangeABI.
Import ListNotations.

Record gateway_exchange_runtime {World Event}(backend:gateway_backend World Event)
    (io:Event->option gateway_native_io)(native:World->block->Prop)(stable:World->block->Z->Prop)
    (discipline:option val->mem->World->Prop):Prop:={
  gateway_shutdown_operation:forall before world descriptor result after next observed,
    discipline None before world->
    gateway_runtime_operation backend gateway_shutdown_definition[Vint descriptor;Vint Int.one]
      before world result after next observed->
    (result=Vint Int.zero\/result=Vint(Int.neg Int.one)) /\discipline None after next /\
    gateway_access_retained native stable before world next /\
    gateway_native_frame native stable gateway_native_no_output world before after /\io observed=None
}.
