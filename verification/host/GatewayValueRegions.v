(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Source dispatch retains the actual initialized private tag cell. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata Clight.
From HostGateway Require Import GatewayMachine GatewayStreamInterface GatewayThreadRuntime GatewayValueEntry
  GatewayValueContext GatewayValueStack GatewayFramedRuntime GatewayFrames GatewayWordsMemory.
Import ListNotations.
Open Scope Z_scope.

Section ValueRegions.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
  (native:World->block->Prop)(stable:World->block->Z->Prop)
  (discipline:option val->mem->World->Prop)(thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native stable discipline thread_errno).

Lemma gateway_value_active_ambient slots stream_block stream_offset initial readonly original :
  gateway_ambient_closed backend(gateway_value_active native stable discipline
    slots stream_block stream_offset initial readonly original).
Proof.
  intros before world after next[CONTEXT[TAG[SIZE[TAG_OWN[SIZE_OWN REST]]]]]INTERFERENCE.
  pose proof(gateway_value_context_ambient backend io native stable discipline thread_errno runtime
    stream_block stream_offset initial readonly original before world after next CONTEXT INTERFERENCE)as AFTER_CONTEXT.
  destruct CONTEXT as[SIDE CONTEXT_REST].
  destruct(gateway_thread_ambient _ _ _ _ _ _ runtime None _ _ _ _ SIDE INTERFERENCE)
    as[AFTER_SIDE[[RETAIN_NATIVE RETAIN_STABLE]FRAME]].
  split;[exact AFTER_CONTEXT|].
  split;[apply RETAIN_NATIVE;[eapply Mem.perm_valid_block;apply(TAG_OWN 0);lia|exact TAG]|].
  split;[apply RETAIN_NATIVE;[eapply Mem.perm_valid_block;apply(SIZE_OWN 0);lia|exact SIZE]|].
  split.
  - intros position RANGE;eapply Mem.perm_unchanged_on;[exact FRAME| |apply TAG_OWN;exact RANGE].
    split;[left;exact TAG|unfold gateway_native_no_output;tauto].
  - split;[|exact REST]. intros position RANGE;eapply Mem.perm_unchanged_on;[exact FRAME| |apply SIZE_OWN;exact RANGE].
    split;[left;exact SIZE|unfold gateway_native_no_output;tauto].
Qed.

Definition gateway_value_tagged slots stream_block stream_offset initial readonly original tag memory world :Prop:=
  gateway_value_active native stable discipline slots stream_block stream_offset initial readonly original memory world /\
  Mem.loadv Mint64 memory(Vptr(gateway_value_tag_slot slots)Ptrofs.zero)=Some(Vlong tag).

Lemma gateway_value_tagged_ambient slots stream_block stream_offset initial readonly original tag :
  gateway_ambient_closed backend(gateway_value_tagged slots stream_block stream_offset initial readonly original tag).
Proof.
  intros before world after next[ACTIVE LOAD]INTERFERENCE;split.
  - eapply gateway_value_active_ambient;eassumption.
  - destruct ACTIVE as[[SIDE CONTEXT][NATIVE REST]].
    destruct(gateway_thread_ambient _ _ _ _ _ _ runtime None _ _ _ _ SIDE INTERFERENCE)as[_[_ FRAME]].
    unfold Mem.loadv in LOAD|-*.
    change(Mem.load Mint64 after(gateway_value_tag_slot slots)0=Some(Vlong tag)).
    change(Mem.load Mint64 before(gateway_value_tag_slot slots)0=Some(Vlong tag))in LOAD.
    eapply Mem.load_unchanged_on;[exact FRAME| |exact LOAD].
    intros position RANGE;split;[left;exact NATIVE|unfold gateway_native_no_output;tauto].
Qed.

End ValueRegions.
