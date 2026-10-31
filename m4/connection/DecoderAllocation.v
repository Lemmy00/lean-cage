(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-decoder.evidence: Allocate all owned globals, arbitrary input bytes and output storage. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Globalenvs Clight.
Require Import Slice Machine Readers Library LibraryWitnesses FreshMemory FailureWitnesses
  ResultLayout ResultSource DecoderValidity DecoderMemory DecoderInput.
Import ListNotations.
Open Scope Z_scope.
Lemma allocate_decoder_bytes : forall base bytes,
  (length bytes <= 160)%nat -> exists after b,
  old_memory base after /\ readable_bytes after {|address_block:=b;address_offset:=0|} bytes /\
  b=Mem.nextblock base /\ Mem.nextblock after=Pos.succ (Mem.nextblock base).
Proof.
  intros base bytes BOUND.
  destruct (allocated_bytes base bytes) as [allocated [b [after [ALLOC [STORE LOAD]]]]].
  assert (FRESH : ~ Mem.valid_block base b) by (eapply Mem.fresh_block_alloc;exact ALLOC).
  exists after,b;split.
  - eapply Mem.unchanged_on_trans;[eapply Mem.alloc_unchanged_on;exact ALLOC|].
    eapply Mem.storebytes_unchanged_on;[exact STORE|]. intros pos RANGE VALID;contradiction.
  - split.
    + split;[|exact LOAD]. unfold span_bounds;cbn [address_offset].
      change (0<=0<18446744073709551616 /\ 0+Z.of_nat (length bytes)<=18446744073709551616 /\
        Z.of_nat (length bytes)<=18446744073709551615);lia.
    + split;[exact (Mem.alloc_result _ _ _ _ _ ALLOC)|].
      rewrite (Mem.nextblock_storebytes _ _ _ _ _ STORE),(Mem.nextblock_alloc _ _ _ _ _ ALLOC);reflexivity.
Qed.
Lemma allocate_decoder_scalar : forall base chunk value,
  Val.load_result chunk value=value -> exists after b,
  old_memory base after /\ Mem.load chunk after b 0=Some value /\
  b=Mem.nextblock base /\ Mem.nextblock after=Pos.succ (Mem.nextblock base).
Proof.
  intros base chunk value NORMAL.
  destruct (Mem.alloc base 0 (size_chunk chunk)) as [allocated b] eqn:ALLOC.
  assert (ACCESS : Mem.valid_access allocated chunk b 0 Writable).
  { eapply Mem.valid_access_implies with (p1:=Freeable);[|constructor].
    eapply Mem.valid_access_alloc_same;[exact ALLOC|lia|lia|exists 0;lia]. }
  destruct (Mem.valid_access_store _ _ _ _ value ACCESS) as [after STORE].
  exists after,b;split.
  - eapply Mem.unchanged_on_trans;[eapply Mem.alloc_unchanged_on;exact ALLOC|].
    eapply Mem.store_unchanged_on;[exact STORE|]. intros pos RANGE VALID.
    eapply (Mem.fresh_block_alloc _ _ _ _ _ ALLOC);exact VALID.
  - split;[rewrite (Mem.load_store_same _ _ _ _ _ _ STORE),NORMAL;reflexivity|].
    split;[exact (Mem.alloc_result _ _ _ _ _ ALLOC)|].
    rewrite (Mem.nextblock_store _ _ _ _ _ _ STORE),(Mem.nextblock_alloc _ _ _ _ _ ALLOC);reflexivity.
Qed.
Theorem source_decoder_global_symbols :
  Genv.find_symbol result_ge ___stringlit_2=Some 25%positive /\
  Genv.find_symbol result_ge _run_id=Some 74%positive /\
  Genv.find_symbol result_ge _run_uid=Some 77%positive /\
  Genv.find_symbol result_ge _preflight=Some 76%positive.
Proof. split;[vm_compute;reflexivity|]. split;[vm_compute;reflexivity|]. split;vm_compute;reflexivity. Qed.
Theorem allocated_decoder_globals : forall run uid preflight,
  exists m, decoder_globals m 25%positive 74%positive 77%positive 76%positive run uid preflight.
Proof.
  intros run uid preflight.
  destruct (allocate_decoder_bytes (vacant_memory 25%positive) frame_magic ltac:(cbn;lia))
    as [m1 [magic [O1 [MAGIC [B1 N1]]]]].
  change (magic=25%positive) in B1;subst magic. change (Mem.nextblock m1=26%positive) in N1.
  set (gap:=empty_allocations 48 m1).
  assert (OG : old_memory m1 gap) by apply empty_allocations_preserve.
  assert (NG : Mem.nextblock gap=74%positive).
  { apply Pos2Nat.inj;unfold gap;rewrite empty_allocations_next,N1;reflexivity. }
  destruct (allocate_decoder_scalar gap Mint64 (Vlong run) eq_refl) as [m2 [rb [O2 [RUN [B2 N2]]]]].
  rewrite NG in B2,N2;subst rb. change (Mem.nextblock m2=75%positive) in N2.
  set (gap2:=empty_allocations 1 m2).
  assert (OG2 : old_memory m2 gap2) by apply empty_allocations_preserve.
  assert (NG2 : Mem.nextblock gap2=76%positive).
  { apply Pos2Nat.inj;unfold gap2;rewrite empty_allocations_next,N2;reflexivity. }
  destruct (allocate_decoder_scalar gap2 Mint32 (Vint preflight) eq_refl) as [m3 [pb [O3 [PRE [B3 N3]]]]].
  rewrite NG2 in B3,N3;subst pb. change (Mem.nextblock m3=77%positive) in N3.
  destruct (allocate_decoder_scalar m3 Mint32 (Vint uid) eq_refl) as [m4 [ub [O4 [UID [B4 N4]]]]].
  rewrite N3 in B4;subst ub. exists m4.
  destruct source_decoder_global_symbols as [MS [RS [US PS]]].
  split;[exact MS|]. split;[exact RS|]. split;[exact US|]. split;[exact PS|]. split.
  - eapply old_memory_readable;[exact O4|]. eapply old_memory_readable;[exact O3|].
    eapply old_memory_readable;[exact OG2|]. eapply old_memory_readable;[exact O2|].
    eapply old_memory_readable;[exact OG|exact MAGIC].
  - split.
    + eapply old_memory_load;[exact O4|]. eapply old_memory_load;[exact O3|].
      eapply old_memory_load;[exact OG2|exact RUN].
    + split;[exact UID|]. eapply old_memory_load;[exact O4|exact PRE].
Qed.
Theorem arbitrary_decoder_source_input : forall bytes run uid preflight,
  length bytes=160%nat -> exists m p output, decoder_input m p bytes output 0 run uid preflight.
Proof.
  intros bytes run uid preflight LEN.
  destruct (allocated_decoder_globals run uid preflight) as [globals GLOBALS].
  destruct (allocate_decoder_bytes globals bytes ltac:(rewrite LEN;lia)) as [frame [fb [OF [FRAME [BF NF]]]]].
  pose proof (old_decoder_globals _ _ _ _ _ _ _ _ _ OF GLOBALS) as GF.
  destruct (Mem.alloc frame 0 144) as [m output] eqn:ALLOC.
  assert (OM : old_memory frame m) by (eapply Mem.alloc_unchanged_on;exact ALLOC).
  assert (FRESH : ~ Mem.valid_block frame output) by (eapply Mem.fresh_block_alloc;exact ALLOC).
  assert (BFV : Mem.valid_block frame fb).
  { destruct FRAME as [BOUNDS LOAD]. eapply Mem.perm_valid_block with (ofs:=0).
    eapply Mem.loadbytes_range_perm;[exact LOAD|cbn;rewrite LEN;cbn;lia]. }
  assert (BN : fb<>output) by congruence.
  exists m,{|address_block:=fb;address_offset:=0|},output.
  split;[exact LEN|]. split;[eapply old_memory_readable;eassumption|]. split.
  - split;[lia|]. split;[change (144<=18446744073709551616);lia|]. split;[exists 0;reflexivity|].
    red;intros pos RANGE;eapply Mem.perm_implies;[eapply Mem.perm_alloc_2;eassumption|constructor].
  - split;[left;exact BN|]. exists 25%positive,74%positive,77%positive,76%positive.
    split;[eapply old_decoder_globals;[exact OM|exact GF]|].
    destruct GF as [_ [_ [_ [_ [_ [_ [UID PRE]]]]]]]. split;left;intro SAME;subst output;apply FRESH;
      eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;
      [eapply Mem.load_valid_access;eassumption|constructor|eapply Mem.load_valid_access;eassumption|constructor].
Qed.
