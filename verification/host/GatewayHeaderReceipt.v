(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Shared packet words come from the same owned native stores. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Events Clight.
Require Import Writers WriteBytes.
From HostGateway Require Import GatewaySource GatewayMachine GatewayStreamInterface GatewayThreadRuntime
  GatewayHeaderRuntime GatewayHeaderWords GatewayFramedRuntime GatewayRuntimeTrace GatewayReadonly
  GatewayWordsMemory GatewayWordReceipt GatewayWordsMath GatewayWordData.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Section HeaderReceipt.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
  (native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
  (discipline:option Values.val->mem->World->Prop)(thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).
Variable ge:Clight.genv.

Theorem gateway_put32_coupled mode object offset value held readonly original origin
    before world events returned after next :
  gateway_header_resources native_private stable_readonly discipline mode object held readonly original origin before world ->
  Ptrofs.unsigned offset+4<=Ptrofs.modulus ->
  Mem.range_perm before object(Ptrofs.unsigned offset)(Ptrofs.unsigned offset+4)Cur Writable ->
  (forall position,Ptrofs.unsigned offset<=position<Ptrofs.unsigned offset+4->~readonly object position) ->
  gateway_steps backend ge
    (gateway_live(writer_initial f_host_put32 object offset(Vint value)Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->
  returned=Vundef /\
  gateway_header_resources native_private stable_readonly discipline mode object held readonly original origin after next /\
  gateway_encoded_memory after object(Ptrofs.unsigned offset)4(Z.to_nat(Int.unsigned value)) /\
  Forall gateway_quiet_event events.
Proof.
  intros RESOURCES BOUND WRITABLE DISJOINT RUN.
  pose proof(gateway_put32_runtime_path backend io native_private stable_readonly discipline thread_errno runtime ge
    mode object offset value held readonly original origin before BOUND DISJOINT)as SCRIPT.
  assert(INITIAL:gateway_header_stage native_private stable_readonly discipline mode object held readonly original origin
    (Ptrofs.unsigned offset)4 [] before world).
  { split;[exact RESOURCES|apply gateway_bytes_initial;exact WRITABLE]. }
  destruct(gateway_runtime_path_return_exact backend ge _ _ _ _ before world events returned after next
    INITIAL SCRIPT RUN)as[VALUE[RESOURCES_AFTER WORD]].
  split;[exact VALUE|]. split;[exact RESOURCES_AFTER|]. split.
  - eapply gateway_encoded_memory_intro with(bytes:=gateway_native_bytes(put32_values value)).
    + rewrite gateway_native_memvals;apply gateway_bytes_complete;[exact WORD|reflexivity].
    + rewrite gateway_native_naturals by apply gateway_words32_bound;apply gateway_put32_encoding.
  - exact(gateway_runtime_path_return_events backend ge _ _ _ _ before world events returned after next
      INITIAL SCRIPT RUN).
Qed.

Theorem gateway_put64_coupled mode object offset value held readonly original origin
    before world events returned after next :
  gateway_header_resources native_private stable_readonly discipline mode object held readonly original origin before world ->
  Ptrofs.unsigned offset+8<=Ptrofs.modulus ->
  Mem.range_perm before object(Ptrofs.unsigned offset)(Ptrofs.unsigned offset+8)Cur Writable ->
  (forall position,Ptrofs.unsigned offset<=position<Ptrofs.unsigned offset+8->~readonly object position) ->
  gateway_steps backend ge
    (gateway_live(writer_initial f_host_put64 object offset(Vlong value)Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->
  returned=Vundef /\
  gateway_header_resources native_private stable_readonly discipline mode object held readonly original origin after next /\
  gateway_encoded_memory after object(Ptrofs.unsigned offset)8(Z.to_nat(Int64.unsigned value)) /\
  Forall gateway_quiet_event events.
Proof.
  intros RESOURCES BOUND WRITABLE DISJOINT RUN.
  pose proof(gateway_put64_runtime_path backend io native_private stable_readonly discipline thread_errno runtime ge
    mode object offset value held readonly original origin before BOUND DISJOINT)as SCRIPT.
  assert(INITIAL:gateway_header_stage native_private stable_readonly discipline mode object held readonly original origin
    (Ptrofs.unsigned offset)8 [] before world).
  { split;[exact RESOURCES|apply gateway_bytes_initial;exact WRITABLE]. }
  destruct(gateway_runtime_path_return_exact backend ge _ _ _ _ before world events returned after next
    INITIAL SCRIPT RUN)as[VALUE[RESOURCES_AFTER WORD]].
  split;[exact VALUE|]. split;[exact RESOURCES_AFTER|]. split.
  - eapply gateway_encoded_memory_intro with(bytes:=gateway_native_bytes(put64_values value)).
    + rewrite gateway_native_memvals;apply gateway_bytes_complete;[exact WORD|reflexivity].
    + rewrite gateway_native_naturals by apply gateway_words64_bound;apply gateway_put64_encoding.
  - exact(gateway_runtime_path_return_events backend ge _ _ _ _ before world events returned after next
      INITIAL SCRIPT RUN).
Qed.

End HeaderReceipt.
