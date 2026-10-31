(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.finish: Derive actual finish allocation and copy from independent caller input. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers Values Memory Clight.
Require Import Slice Machine ClightSteps WriteAll StoreSteps FreshMemory ResultLayout FrameRecord FrameCopy
  FinishSource.
Open Scope Z_scope.
Theorem finish_preparation_exists : forall base input ofs r digest k,
  frame_result_owned base input ofs r digest ->
  exists allocated local copied,
    Mem.alloc base 0 144=(allocated,local) /\
    store_path result_ge (old_memory base) (finish_initial input ofs k base) 4
      (State f_finish finish_after_copy k (finish_env local) (finish_temps input ofs) copied) /\
    old_memory base copied /\ frame_result_owned copied local 0 r digest /\
    Mem.range_perm copied local 0 144 Cur Freeable.
Proof.
  intros base input ofs r digest k INPUT.
  destruct (fresh_frame_copy_exists _ _ _ _ _ INPUT) as [allocated [local [copied [ALLOC [COPY [OLD [OWN FREE]]]]]]].
  assert (PA : old_memory base allocated) by (eapply Mem.alloc_unchanged_on;exact ALLOC).
  exists allocated,local,copied;split;[exact ALLOC|]. split;[|auto].
  eapply store_next;[apply Mem.unchanged_on_refl|apply finish_entry_source;exact ALLOC|].
  eapply store_next;[exact PA|apply unchanged_store_edge;WriteAll.structural|].
  eapply store_next;[exact PA|apply finish_parameter_copy_source;exact COPY|].
  eapply store_next;[exact OLD|apply unchanged_store_edge;WriteAll.structural|].
  apply store_done;exact OLD.
Qed.
