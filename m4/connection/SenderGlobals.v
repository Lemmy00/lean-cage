(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.evidence: Inhabited mode, literals, magic and error cell at actual source symbols. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Globalenvs Clight.
Require Import Slice IO Machine Library LibraryWitnesses Fault ProcessEffects FreshMemory ResultLayout
  FailureContract FailureWitnesses DecoderValidity DecoderAllocation SenderSelectors.
Import ListNotations.
Open Scope Z_scope.
Definition sender_literal_location tag : block := match tag with
  |wrong_sequence=>24%positive|bad_reserved=>28%positive|duplicate_frame=>27%positive
  |short_frame=>26%positive|drop_frame=>20%positive end.
Theorem sender_literal_symbols : forall tag,
  Genv.find_symbol result_ge (report_literal tag)=Some (sender_literal_location tag).
Proof. destruct tag;vm_compute;reflexivity. Qed.
Lemma report_name_nonzero : forall tag,Forall (fun b=>b<>Byte.zero) (report_name tag).
Proof. destruct tag;repeat constructor;vm_compute;discriminate. Qed.
Lemma report_name_size : forall tag,(length (report_name tag)<=158)%nat.
Proof. destruct tag;cbn;lia. Qed.
Ltac carry_sender_string := first [assumption|
  lazymatch goal with |- c_string ?m _ _ =>
    match goal with OLD : old_memory ?previous m |- _=>
      eapply old_memory_string;[exact OLD|carry_sender_string]
    end end].
Ltac carry_sender_bytes := first [assumption|
  lazymatch goal with |- readable_bytes ?m _ _ =>
    match goal with OLD : old_memory ?previous m |- _=>
      eapply old_memory_readable;[exact OLD|carry_sender_bytes]
    end end].
Theorem allocated_sender_globals : forall mode_bytes,
  Forall (fun b=>b<>Byte.zero) mode_bytes -> (length mode_bytes<=158)%nat ->
  exists cell base mode,
    sender_selectors cell base mode mode_bytes sender_literal_location /\
    readable_bytes base {|address_block:=25%positive;address_offset:=0|} frame_magic.
Proof.
  intros mode_bytes NONZERO LENGTH.
  destruct (allocate_failure_string (vacant_memory 20%positive) (report_name drop_frame)
    (report_name_nonzero _) (report_name_size _)) as [m1 [b1 [O1 [S1 [B1 N1]]]]].
  change (b1=20%positive) in B1;subst b1;change (Mem.nextblock m1=21%positive) in N1.
  set (gap1:=empty_allocations 1 m1).
  assert (OG1 : old_memory m1 gap1) by apply empty_allocations_preserve.
  assert (NG1 : Mem.nextblock gap1=22%positive).
  { apply Pos2Nat.inj;unfold gap1;rewrite empty_allocations_next,N1;reflexivity. }
  destruct (allocate_failure_string gap1 mode_bytes NONZERO LENGTH) as [m2 [mode [O2 [S2 [B2 N2]]]]].
  rewrite NG1 in B2,N2;subst mode;change (Mem.nextblock m2=23%positive) in N2.
  set (gap2:=empty_allocations 1 m2).
  assert (OG2 : old_memory m2 gap2) by apply empty_allocations_preserve.
  assert (NG2 : Mem.nextblock gap2=24%positive).
  { apply Pos2Nat.inj;unfold gap2;rewrite empty_allocations_next,N2;reflexivity. }
  destruct (allocate_failure_string gap2 (report_name wrong_sequence) (report_name_nonzero _) (report_name_size _))
    as [m3 [b3 [O3 [S3 [B3 N3]]]]].
  rewrite NG2 in B3,N3;subst b3;change (Mem.nextblock m3=25%positive) in N3.
  destruct (allocate_decoder_bytes m3 frame_magic ltac:(cbn;lia)) as [m4 [magic [O4 [MAGIC [B4 N4]]]]].
  rewrite N3 in B4,N4;subst magic;change (Mem.nextblock m4=26%positive) in N4.
  destruct (allocate_failure_string m4 (report_name short_frame) (report_name_nonzero _) (report_name_size _))
    as [m5 [b5 [O5 [S5 [B5 N5]]]]].
  rewrite N4 in B5,N5;subst b5;change (Mem.nextblock m5=27%positive) in N5.
  destruct (allocate_failure_string m5 (report_name duplicate_frame) (report_name_nonzero _) (report_name_size _))
    as [m6 [b6 [O6 [S6 [B6 N6]]]]].
  rewrite N5 in B6,N6;subst b6;change (Mem.nextblock m6=28%positive) in N6.
  destruct (allocate_failure_string m6 (report_name bad_reserved) (report_name_nonzero _) (report_name_size _))
    as [m7 [b7 [O7 [S7 [B7 N7]]]]].
  rewrite N6 in B7,N7;subst b7;change (Mem.nextblock m7=29%positive) in N7.
  set (gap:=empty_allocations 46 m7).
  assert (OG : old_memory m7 gap) by apply empty_allocations_preserve.
  assert (NG : Mem.nextblock gap=75%positive).
  { apply Pos2Nat.inj;unfold gap;rewrite empty_allocations_next,N7;reflexivity. }
  destruct (allocate_decoder_scalar gap Mint64 (address_value (global_address 22%positive)) eq_refl)
    as [pointed [mb [OP [POINTER [MB NP]]]]].
  rewrite NG in MB,NP;subst mb;change (Mem.nextblock pointed=76%positive) in NP.
  destruct (Mem.alloc pointed 0 4) as [base eb] eqn:TLSALLOC.
  assert (EB : eb=76%positive) by (rewrite (Mem.alloc_result _ _ _ _ _ TLSALLOC);exact NP);subst eb.
  assert (OB : old_memory pointed base) by (eapply Mem.alloc_unchanged_on;exact TLSALLOC).
  change (old_memory (vacant_memory 20%positive) m1) in O1.
  change (old_memory m1 gap1) in OG1.
  change (old_memory gap1 m2) in O2.
  change (old_memory m2 gap2) in OG2.
  change (old_memory gap2 m3) in O3.
  change (old_memory m4 m5) in O5.
  change (old_memory m5 m6) in O6.
  change (old_memory m6 m7) in O7.
  change (old_memory m7 gap) in OG.
  exists {|tls_block:=76%positive;tls_offset:=0|},base,(global_address 22%positive);split.
  - split.
    + unfold tls_ready;cbn;split;[lia|]. split;[change (4<=18446744073709551616);lia|].
      eapply Mem.valid_access_implies with (p1:=Freeable);[|constructor].
      eapply Mem.valid_access_alloc_same;[exact TLSALLOC|cbn;lia|cbn;lia|exists 0;reflexivity].
    + split.
      * exists 75%positive;split;[exact source_mode_symbol|]. split.
        -- eapply old_memory_load;[exact OB|exact POINTER].
        -- intros pos RANGE;left;discriminate.
      * split.
        -- split;[carry_sender_string|intros pos RANGE;left;discriminate].
        -- intros tag;split;[apply sender_literal_symbols|]. destruct tag;split;
             [carry_sender_string|intros pos RANGE;left;discriminate|
              carry_sender_string|intros pos RANGE;left;discriminate|
              carry_sender_string|intros pos RANGE;left;discriminate|
              carry_sender_string|intros pos RANGE;left;discriminate|
              carry_sender_string|intros pos RANGE;left;discriminate].
  - carry_sender_bytes.
Qed.
