(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-bridge.bytes: Explicit imported values connected to actual source executions. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers Values Memory Events Clight.
From LeanImport Require Import Lean.
Require Import NormalizedImport BridgeNat BridgeBytes BridgeWords
 Slice IO Machine Library Readers FrameBytes DecoderAllocation.
Local Close Scope lean_scope.
Import ListNotations.
Local Open Scope Z_scope.

Definition imported_value32 bs offset := Vint (Int.repr (Z.of_nat (nat_of_Nat
   (LeanCageM4_Normalized_littleBytes (imported_bytes bs) (Nat_of_nat offset) (Nat_of_nat 4))))).
Lemma imported_reader32_input m p bs offset :
 readable_bytes m p bs -> (offset+4 <= length bs)%nat ->
 reader_input m (address_block p) (Ptrofs.repr (address_offset p + Z.of_nat offset))
   f_get32 (imported_value32 bs offset) 59.
Proof.
 intros READ BOUND; unfold imported_value32; rewrite <- imported_word32_exact.
 apply frame_reader32_input; assumption.
Qed.
Theorem source32_imported_return cell m p bs offset events actual after :
 readable_bytes m p bs -> (offset+4 <= length bs)%nat ->
 steps (Clight.globalenv Slice.prog) cell
   (live (initial f_get32 (address_block p)
     (Ptrofs.repr (address_offset p + Z.of_nat offset)) Kstop m)) events
   (live (Returnstate actual Kstop after)) ->
 actual = imported_value32 bs offset /\ after = m /\
 events = repeat (source_step E0) 59.
Proof.
 intros READ BOUND RUN.
 eapply reader_return_exact; [eapply imported_reader32_input; eassumption|exact RUN].
Qed.
Theorem source32_imported_execution cell m p bs offset k :
 readable_bytes m p bs -> (offset+4 <= length bs)%nat ->
 steps (Clight.globalenv Slice.prog) cell
   (live (initial f_get32 (address_block p)
     (Ptrofs.repr (address_offset p + Z.of_nat offset)) k m))
   (repeat (source_step E0) 59)
   (live (Returnstate (imported_value32 bs offset) (call_cont k) m)).
Proof.
 intros READ BOUND; apply reader_success_exists; apply imported_reader32_input; assumption.
Qed.
Theorem source32_imported_progress cell m p bs offset events s :
 readable_bytes m p bs -> (offset+4 <= length bs)%nat ->
 steps (Clight.globalenv Slice.prog) cell
   (live (initial f_get32 (address_block p)
     (Ptrofs.repr (address_offset p + Z.of_nat offset)) Kstop m)) events (live s) ->
 s = Returnstate (imported_value32 bs offset) Kstop m \/
 exists next, step (Clight.globalenv Slice.prog) cell (live s) (source_step E0) (live next).
Proof.
 intros READ BOUND RUN; eapply reader_defined_prefix;
   [exact (imported_reader32_input m p bs offset READ BOUND)|exact RUN].
Qed.
Theorem source32_imported_loss cell m p bs offset n :
 readable_bytes m p bs -> (offset+4 <= length bs)%nat -> (n <= 59)%nat ->
 exists mid,
   steps (Clight.globalenv Slice.prog) cell
     (live (initial f_get32 (address_block p)
       (Ptrofs.repr (address_offset p + Z.of_nat offset)) Kstop m))
     (repeat (source_step E0) n) (live mid) /\
   steps (Clight.globalenv Slice.prog) cell
     (live (initial f_get32 (address_block p)
       (Ptrofs.repr (address_offset p + Z.of_nat offset)) Kstop m))
     (repeat (source_step E0) n ++ [loss_step]) (dead m).
Proof.
 intros READ BOUND N; eapply reader_loss_every_prefix;
   [exact (imported_reader32_input m p bs offset READ BOUND)|exact N].
Qed.
Theorem source32_imported_nonvacuous cell bs :
 length bs = 4%nat -> exists m block,
 readable_bytes m {|address_block:=block;address_offset:=0|} bs /\
 steps (Clight.globalenv Slice.prog) cell
   (live (initial f_get32 block Ptrofs.zero Kstop m))
   (repeat (source_step E0) 59)
   (live (Returnstate (imported_value32 bs 0) Kstop m)).
Proof.
 intros LENGTH.
 destruct (allocate_decoder_bytes Mem.empty bs ltac:(lia)) as [m [block [_ [READ _]]]].
 exists m,block;split;[exact READ|].
 exact (source32_imported_execution cell m
   {|address_block:=block;address_offset:=0|} bs 0 Kstop READ ltac:(lia)).
Qed.

Definition imported_value64 bs offset := Vlong (Int64.repr (Z.of_nat (nat_of_Nat
   (LeanCageM4_Normalized_littleBytes (imported_bytes bs) (Nat_of_nat offset) (Nat_of_nat 8))))).
Lemma imported_reader64_input m p bs offset :
 readable_bytes m p bs -> (offset+8 <= length bs)%nat ->
 reader_input m (address_block p) (Ptrofs.repr (address_offset p + Z.of_nat offset))
   f_get64 (imported_value64 bs offset) 103.
Proof.
 intros READ BOUND; unfold imported_value64; rewrite <- imported_word64_exact.
 apply frame_reader64_input; assumption.
Qed.
Theorem source64_imported_return cell m p bs offset events actual after :
 readable_bytes m p bs -> (offset+8 <= length bs)%nat ->
 steps (Clight.globalenv Slice.prog) cell
   (live (initial f_get64 (address_block p)
     (Ptrofs.repr (address_offset p + Z.of_nat offset)) Kstop m)) events
   (live (Returnstate actual Kstop after)) ->
 actual = imported_value64 bs offset /\ after = m /\
 events = repeat (source_step E0) 103.
Proof.
 intros READ BOUND RUN.
 eapply reader_return_exact; [eapply imported_reader64_input; eassumption|exact RUN].
Qed.
Theorem source64_imported_execution cell m p bs offset k :
 readable_bytes m p bs -> (offset+8 <= length bs)%nat ->
 steps (Clight.globalenv Slice.prog) cell
   (live (initial f_get64 (address_block p)
     (Ptrofs.repr (address_offset p + Z.of_nat offset)) k m))
   (repeat (source_step E0) 103)
   (live (Returnstate (imported_value64 bs offset) (call_cont k) m)).
Proof.
 intros READ BOUND; apply reader_success_exists; apply imported_reader64_input; assumption.
Qed.
Theorem source64_imported_progress cell m p bs offset events s :
 readable_bytes m p bs -> (offset+8 <= length bs)%nat ->
 steps (Clight.globalenv Slice.prog) cell
   (live (initial f_get64 (address_block p)
     (Ptrofs.repr (address_offset p + Z.of_nat offset)) Kstop m)) events (live s) ->
 s = Returnstate (imported_value64 bs offset) Kstop m \/
 exists next, step (Clight.globalenv Slice.prog) cell (live s) (source_step E0) (live next).
Proof.
 intros READ BOUND RUN; eapply reader_defined_prefix;
   [exact (imported_reader64_input m p bs offset READ BOUND)|exact RUN].
Qed.
Theorem source64_imported_loss cell m p bs offset n :
 readable_bytes m p bs -> (offset+8 <= length bs)%nat -> (n <= 103)%nat ->
 exists mid,
   steps (Clight.globalenv Slice.prog) cell
     (live (initial f_get64 (address_block p)
       (Ptrofs.repr (address_offset p + Z.of_nat offset)) Kstop m))
     (repeat (source_step E0) n) (live mid) /\
   steps (Clight.globalenv Slice.prog) cell
     (live (initial f_get64 (address_block p)
       (Ptrofs.repr (address_offset p + Z.of_nat offset)) Kstop m))
     (repeat (source_step E0) n ++ [loss_step]) (dead m).
Proof.
 intros READ BOUND N; eapply reader_loss_every_prefix;
   [exact (imported_reader64_input m p bs offset READ BOUND)|exact N].
Qed.
Theorem source64_imported_nonvacuous cell bs :
 length bs = 8%nat -> exists m block,
 readable_bytes m {|address_block:=block;address_offset:=0|} bs /\
 steps (Clight.globalenv Slice.prog) cell
   (live (initial f_get64 block Ptrofs.zero Kstop m))
   (repeat (source_step E0) 103)
   (live (Returnstate (imported_value64 bs 0) Kstop m)).
Proof.
 intros LENGTH.
 destruct (allocate_decoder_bytes Mem.empty bs ltac:(lia)) as [m [block [_ [READ _]]]].
 exists m,block;split;[exact READ|].
 exact (source64_imported_execution cell m
   {|address_block:=block;address_offset:=0|} bs 0 Kstop READ ltac:(lia)).
Qed.
