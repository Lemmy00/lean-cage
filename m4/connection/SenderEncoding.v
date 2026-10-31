(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.encoding: All actual encoding paths from independently owned source input. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Clight.
Require Import Slice Machine ClightSteps WriteAll StoreSteps Library LibraryMachine CallPaths FreshMemory
  ResultLayout SourceReach FrameRecord SenderSource SenderMemory
  BytePatch SenderStorage CopyPaths SenderEncodingPrefix SenderCopies
  SenderEncodingTail SenderWire.
Import ListNotations.
Open Scope Z_scope.
Lemma source_reaches_copy : forall ge P Q R s,
  source_reaches ge P Q s -> (forall last,Q last -> copy_reaches ge P R last) -> copy_reaches ge P R s.
Proof.
  intros ge P Q R s [count [last [PATH POST]]] NEXT.
  eapply copy_reaches_path;[exact PATH|apply NEXT;exact POST].
Qed.
Definition sender_encoding_result base fd sequence r digest k s :=
  exists result_local bytes_local le after,
    s=State f_send_frame sender_reporting k (sender_env result_local bytes_local) le after /\
    le ! _fd=Some (Vint fd) /\ le ! _sequence=Some (Vlong sequence) /\
    ~Mem.valid_block base result_local /\ ~Mem.valid_block base bytes_local /\ result_local<>bytes_local /\
    sender_storage base result_local bytes_local r digest (outgoing_frame sequence r digest) after.

Theorem sender_encoding_connection : forall base fd sequence input ofs r digest k magic,
  frame_result_owned base input ofs r digest ->
  Genv.find_symbol result_ge ___stringlit_2=Some magic ->
  readable_bytes base {|address_block:=magic;address_offset:=0|} DecoderValidity.frame_magic ->
  copy_reaches result_ge (old_memory base) (sender_encoding_result base fd sequence r digest k)
    (sender_initial fd sequence input ofs k base).
Proof.
  intros base fd sequence input ofs r digest k magic INPUT MS MAGIC.
  pose proof INPUT as [_ [_ [_ [_ [DIGESTLEN _]]]]].
  destruct (sender_preparation_exists base fd sequence input ofs r digest k INPUT)
    as [first [result_local [allocated [bytes_local [prepared [count [A1 [A2 [PATH STORAGE]]]]]]]]].
  assert (FR : ~Mem.valid_block base result_local) by (eapply Mem.fresh_block_alloc;exact A1).
  assert (FB1 : ~Mem.valid_block first bytes_local) by (eapply Mem.fresh_block_alloc;exact A2).
  assert (FB : ~Mem.valid_block base bytes_local).
  { intro VALID;apply FB1;eapply Mem.valid_block_alloc;[exact A1|exact VALID]. }
  assert (NE : result_local<>bytes_local).
  { intro SAME;subst bytes_local;apply FB1;eapply Mem.valid_new_block;exact A1. }
  change (sender_storage base result_local bytes_local r digest (repeat Byte.zero 160) prepared) in STORAGE.
  eapply copy_reaches_path;[exact PATH|].
  eapply copy_reaches_path;[eapply sender_magic_call_source;[exact (proj1 STORAGE)|exact MS]|].
  apply copy_reaches_call.
  - exact (proj1 STORAGE).
  - eapply sender_magic_copy_owned;[exact FB|exact MAGIC|exact STORAGE].
  - intros schedule after RUN;eapply fresh_partial_copy_old;[exact FB|exact (proj1 STORAGE)|exact RUN].
  - intros copied COPY.
    pose proof (sender_storage_patch base prepared copied result_local bytes_local r digest
      (repeat Byte.zero 160) 0 DecoderValidity.frame_magic FB NE STORAGE ltac:(cbn;lia) (proj2 COPY)) as FIRST.
    change (sender_storage base result_local bytes_local r digest sender_magic_bytes copied) in FIRST.
    eapply copy_reaches_source;[exact (proj1 FIRST)|apply unchanged_store_edge;WriteAll.structural|].
    eapply copy_reaches_source;[exact (proj1 FIRST)|apply unchanged_store_edge;WriteAll.structural|].
    eapply source_reaches_copy.
    + apply sender_prefix_source;[exact FB|exact NE|exact FIRST|unfold sender_temps;WriteAll.lookup|unfold sender_temps;WriteAll.lookup].
    + intros last [le [before [LAST [FD [SEQ PREFIX]]]]];subst last.
      eapply copy_reaches_path;[eapply sender_digest_call_source;[exact (proj1 PREFIX)|exact DIGESTLEN]|].
      apply copy_reaches_call.
      * exact (proj1 PREFIX).
      * eapply sender_digest_copy_owned;[exact NE|exact PREFIX].
      * intros schedule after RUN;eapply fresh_partial_copy_old;[exact FB|exact (proj1 PREFIX)|exact RUN].
      * intros digested DCOPY.
        pose proof (sender_storage_patch base before digested result_local bytes_local r digest
          (sender_prefix_bytes sequence r) 104 digest FB NE PREFIX
          ltac:(rewrite sender_prefix_length,DIGESTLEN;lia) (proj2 DCOPY)) as WITHDIGEST.
        eapply copy_reaches_source;[exact (proj1 WITHDIGEST)|apply unchanged_store_edge;WriteAll.structural|].
        eapply copy_reaches_source;[exact (proj1 WITHDIGEST)|apply unchanged_store_edge;WriteAll.structural|].
        eapply source_reaches_copy.
        -- apply sender_tail_source;[exact FB|exact NE|exact WITHDIGEST|apply sender_prefix_length|exact FD|exact SEQ].
        -- intros last [final_le [final [LAST [FINALFD [FINALSEQ FINAL]]]]];subst last.
           apply copy_reaches_done;[exact (proj1 FINAL)|].
           exists result_local,bytes_local,final_le,final.
           split;[reflexivity|]. split;[exact FINALFD|]. split;[exact FINALSEQ|].
           split;[exact FR|]. split;[exact FB|]. split;[exact NE|].
           rewrite sender_tail_exact in FINAL by exact DIGESTLEN;exact FINAL.
Qed.
