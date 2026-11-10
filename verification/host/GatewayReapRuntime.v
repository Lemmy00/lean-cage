(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Cleanup observations come from individual actual process APIs. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Memdata Clight.
From HostGateway Require Import GatewayMachine GatewayRuntime GatewayThreadRuntime GatewayStreamInterface GatewayExchangeABI GatewayReapABI.
Import ListNotations.
Open Scope Z_scope.

Inductive gateway_reap_observation:=
|gateway_reap_signal(group result:int)(number:option int)
|gateway_reap_wait(child options result:int)(status:option int)(number:option int)
|gateway_reap_pause(result:int)(number:option int).

Definition gateway_reap_errno(result number:int):option int:=
  if Int.eq result(Int.neg Int.one)then Some number else None.

(* Each law names one completed or committed operation. It does not assert that
   a helper returns, a signalled process dies, a wait succeeds, or EOF reaps it.
   The physical native history separately binds signal/reaped products to the
   same lifetime token; an optional SDK observation cannot manufacture a product. *)
Record gateway_reap_runtime {World Event}(backend:gateway_backend World Event)
    (io:Event->option gateway_native_io)(observation:Event->option gateway_reap_observation)
    (native:World->block->Prop)(stable:World->block->Z->Prop)
    (discipline:option val->mem->World->Prop)(thread_errno:World->int):Prop:={
  gateway_reap_kill_operation:forall mode before world group result after next event,
    discipline mode before world->Int.signed group<0->
    gateway_runtime_operation backend gateway_kill_definition[Vint group;Vint(Int.repr 9)]
      before world result after next event->
    exists status,result=Vint status /\(status=Int.zero\/status=Int.neg Int.one) /\
      observation event=Some(gateway_reap_signal group status(gateway_reap_errno status(thread_errno next))) /\
      discipline mode after next /\gateway_access_retained native stable before world next /\
      gateway_native_frame native stable gateway_native_no_output world before after /\io event=None;

  gateway_reap_wait_operation:forall mode before world child options object offset result after next event,
    discipline mode before world->0<Int.signed child->(options=Int.zero\/options=Int.one)->native world object->
    gateway_native_pointer before object offset 4 Writable->
    gateway_runtime_operation backend gateway_waitpid_definition[Vint child;Vptr object offset;Vint options]
      before world result after next event->
    exists observed status,
      result=Vint observed /\
      (observed=Int.neg Int.one\/(observed=Int.zero /\options=Int.one)\/observed=child) /\
      (observed=child->exists word,status=Some word /\
        Mem.loadv Mint32 after(Vptr object offset)=Some(Vint word) /\
        Mem.loadbytes after object(Ptrofs.unsigned offset)4=Some(encode_val Mint32(Vint word))) /\
      (observed<>child->status=None) /\
      observation event=Some(gateway_reap_wait child options observed status(gateway_reap_errno observed(thread_errno next))) /\
      discipline mode after next /\gateway_access_retained native stable before world next /\
      gateway_native_permissions before after object offset 4 /\
      gateway_native_frame native stable(gateway_native_region object offset 4)world before after /\io event=None;

  gateway_reap_pause_operation:forall mode before world object offset result after next event,
    discipline mode before world->native world object->gateway_native_pointer before object offset 16 Readable->
    gateway_runtime_operation backend gateway_nanosleep_definition[Vptr object offset;Vnullptr]
      before world result after next event->
    exists status,result=Vint status /\(status=Int.zero\/status=Int.neg Int.one) /\
      observation event=Some(gateway_reap_pause status(gateway_reap_errno status(thread_errno next))) /\
      discipline mode after next /\gateway_access_retained native stable before world next /\
      gateway_native_frame native stable gateway_native_no_output world before after /\io event=None
}.
