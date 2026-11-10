(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: Source prefixes retain accumulated bytes and actual buffer owners. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Memdata.
From HostGateway Require Import GatewayMachine GatewayOperations GatewayStreamInterface GatewayReadContext
  GatewayThreadRuntime GatewayBufferReference.
Open Scope Z_scope.

Section PrefixContext.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
  (native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
  (discipline:option val->mem->World->Prop)(thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).
Variables stream_block data_block:Values.block.
Variables stream_offset data_offset:ptrofs.
Variable initial:gateway_stream_values.
Variable amount:Z.
Variable readonly:Values.block->Z->Prop.

Definition gateway_prefix_context reference owner mode base width bytes memory current :Prop:=
  gateway_owned_buffer_context native_private stable_readonly discipline stream_block data_block stream_offset data_offset
    initial amount readonly reference owner mode memory current /\
  Mem.loadbytes memory data_block(Ptrofs.unsigned base)width=Some(inj_bytes bytes).

Lemma gateway_prefix_context_ambient reference owner mode base width bytes :
  gateway_runtime_discipline backend(gateway_prefix_context reference owner mode base width bytes).
Proof.
  intros memory current changed future[CONTEXT LOAD]INTERFERENCE;split.
  - eapply gateway_owned_buffer_context_ambient;[exact runtime|exact CONTEXT|exact INTERFERENCE].
  - pose proof(proj1 CONTEXT)as RAW.
    destruct(gateway_thread_ambient _ _ _ _ _ _ runtime mode memory current changed future(proj1 RAW)INTERFERENCE)
      as[SIDE[ACCESS FRAME]].
    assert(DATA_FRAME:Mem.unchanged_on(fun object _=>object=data_block)memory changed).
    { eapply gateway_native_frame_restrict;[exact FRAME| |].
      - intros object position SAME;subst object;left;exact(proj1(proj2(proj2 RAW))).
      - intros object position SAME BAD;exact BAD. }
    eapply Mem.loadbytes_unchanged_on;[exact DATA_FRAME|intros;reflexivity|exact LOAD].
Qed.
End PrefixContext.
