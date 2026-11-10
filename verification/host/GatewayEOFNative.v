(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: The final one-byte socket receive executes with the GIL held. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Memdata Clight.
From HostGateway Require Import GatewayMachine GatewayRuntime GatewayRuntimeABI GatewayThreadRuntime GatewayStreamInterface.
Import ListNotations.
Open Scope Z_scope.

(* This is one actual recv operation, distinct from the detached receive domain
   in ThreadRuntime. It assumes no EOF, byte stream, response or helper outcome. *)
Record gateway_eof_receive_runtime {World Event}(backend:gateway_backend World Event)
    (io:Event->option gateway_native_io)(native:World->block->Prop)(stable:World->block->Z->Prop)
    (discipline:option val->mem->World->Prop):Prop:={
  gateway_eof_receive_operation:forall before world descriptor object offset result after next observed,
    discipline None before world->native world object->gateway_native_pointer before object offset 1 Writable->
    gateway_runtime_operation backend gateway_receive_definition
      [Vint descriptor;Vptr object offset;Vlong Int64.one;Vint Int.zero]before world result after next observed->
    exists count bytes,
      -1<=count<=1 /\result=Vlong(Int64.repr count) /\Z.of_nat(length bytes)=Z.max 0 count /\
      Mem.loadbytes after object(Ptrofs.unsigned offset)(Z.max 0 count)=Some(inj_bytes bytes) /\
      io observed=Some(gateway_native_receive descriptor 1 count bytes) /\
      discipline None after next /\gateway_access_retained native stable before world next /\
      gateway_native_permissions before after object offset 1 /\
      gateway_native_frame native stable(gateway_native_region object offset(Z.max 0 count))world before after
}.
