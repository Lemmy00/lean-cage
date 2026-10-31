(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.input: Independent caller ownership reaches the actual first receiver read loop. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Clight.
Require Import Slice Machine StoreSteps WriteAll ResultLayout FreshMemory SenderReportMemory
  ResultOwnership ReceiverSource ReceiverPreparation ReceiverReadSource ReceiverReadMemory
  ReceiverMemory ReceiverInput ReceiverRouting.
Import ListNotations.
Open Scope Z_scope.
Lemma old_memory_permissions : forall before after,
  old_memory before after -> old_permissions before after.
Proof.
  intros before after OLD b pos pk p PERM;eapply Mem.perm_unchanged_on;[exact OLD| |exact PERM].
  eapply Mem.perm_valid_block;exact PERM.
Qed.
Definition receiver_first_temps output ofs fd bad entered done status :=
  PTree.set _used(Vlong Int64.zero)(receiver_temps output ofs fd bad entered done status).
Theorem receiver_entry_prepared : forall cell base output ofs fd bad entered done status run uid,
  receiver_input cell base output ofs run uid ->
  exists b allocated initialized count,
    receiver_allocations base b allocated /\
    store_path result_ge(receiver_preserved cell base output ofs)
      (receiver_initial output ofs fd bad entered done status Kstop base)count
      (receiver_loop_state b(receiver_first_temps output ofs fd bad entered done status)Kstop initialized) /\
    receiver_live_memory cell base b output ofs fd initialized /\ receiver_buffer cell b initialized [] /\
    receiver_registers(receiver_temps output ofs fd bad entered done status)bad[]
      (receiver_first_temps output ofs fd bad entered done status).
Proof.
  intros cell base output ofs fd bad entered done status run uid [DEST[TLS GLOBALS]].
  destruct(receiver_initial_storage cell base fd TLS)
    as[b[allocated[initialized[ALLOC[STORE[OA[OI[SLOTS[FD BUFFER]]]]]]]]].
  assert(PB : receiver_preserved cell base output ofs base)by(apply Mem.unchanged_on_refl).
  assert(PA : receiver_preserved cell base output ofs allocated)by(apply receiver_old_preserved;exact OA).
  assert(PI : receiver_preserved cell base output ofs initialized)by(apply receiver_old_preserved;exact OI).
  destruct(receiver_preparation_source(receiver_preserved cell base output ofs)base b allocated initialized
    output ofs fd bad entered done status Kstop ALLOC STORE PB PA PI)as[count PATH].
  exists b,allocated,initialized,count;split;[exact ALLOC|]. split;[exact PATH|]. split.
  - split;[apply old_sender_preserved;exact OI|]. split;[exact SLOTS|].
    split;[eapply receiver_destination_permissions;[exact DEST|apply old_memory_permissions;exact OI]|exact FD].
  - split;[exact BUFFER|]. unfold receiver_registers,receiver_first_temps;split;[receiver_keep|].
    split;[unfold receiver_temps;WriteAll.lookup|reflexivity].
Qed.
