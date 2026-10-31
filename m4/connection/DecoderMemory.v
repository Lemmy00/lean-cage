(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-decoder.prefixes: Derive local storage and frame preservation from independent permissions. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Ctypes Ctypesdefs Clight.
Require Import Slice Machine StoreSteps Library ScalarMemory ResultLayout ResultSource ResultSafety FreshMemory
  FrameBytes DecoderLayout DecoderSource.
Import ListNotations.
Open Scope Z_scope.

Definition frame_output_separate p (bytes : list Byte.int) output ofs :=
  address_block p <> output \/ address_offset p + Z.of_nat (length bytes) <= ofs \/
  ofs+144 <= address_offset p.
Lemma frame_preserved_readable : forall base after p bytes output ofs,
  readable_bytes base p bytes -> frame_output_separate p bytes output ofs ->
  result_preserved base output ofs after -> readable_bytes after p bytes.
Proof.
  intros base after p bytes output ofs [BOUNDS LOAD] SEP PRESERVED.
  split; [exact BOUNDS|]. eapply Mem.loadbytes_unchanged_on; [exact PRESERVED| |exact LOAD].
  intros pos RANGE; split.
  - eapply Mem.perm_valid_block. eapply Mem.loadbytes_range_perm; [exact LOAD|exact RANGE].
  - destruct SEP as [NE|[BEFORE|AFTER]]; auto; [right; left|right; right]; lia.
Qed.

Definition decoder_storage base local allocated built copied output ofs bytes :=
  ~ Mem.valid_block base local /\
  Mem.range_perm allocated local 0 144 Cur Freeable /\
  scalar_stores local allocated (decoded_cells bytes) built /\
  assign_loc result_ge result_type built output (Ptrofs.repr ofs) Full (Vptr local Ptrofs.zero) copied /\
  decoded_contents copied output ofs bytes /\
  Mem.range_perm copied local 0 144 Cur Freeable /\
  result_preserved base output ofs allocated /\ result_preserved base output ofs copied.

Theorem decoder_storage_exists : forall base output ofs bytes,
  result_destination base output ofs ->
  exists allocated local built copied,
    Mem.alloc base 0 144 = (allocated,local) /\
    decoder_storage base local allocated built copied output ofs bytes.
Proof.
  intros base output ofs bytes [LOW [HIGH [ALIGN WRITABLE]]].
  destruct (Mem.alloc base 0 144) as [allocated local] eqn:ALLOC.
  assert (FRESH : ~ Mem.valid_block base local) by (eapply Mem.fresh_block_alloc; exact ALLOC).
  assert (LOCAL : Mem.range_perm allocated local 0 144 Cur Freeable).
  { red; intros; eapply Mem.perm_alloc_2; eassumption. }
  assert (ON : output <> local).
  { intro EQ; subst output; apply FRESH. eapply Mem.perm_valid_block.
    apply WRITABLE with (ofs := ofs); lia. }
  destruct (scalar_stores_exist local 144 (decoded_cells bytes) allocated
    (decoded_cells_valid bytes) LOCAL) as [built STORES].
  assert (BUILT_RANGE : Mem.range_perm built local 0 144 Cur Freeable).
  { red; intros; apply (scalar_stores_permissions _ _ _ _ STORES); apply LOCAL; assumption. }
  destruct (Mem.range_perm_loadbytes built local 0 144) as [values LOAD].
  { red; intros pos BOUND. eapply Mem.perm_implies; [apply BUILT_RANGE; cbn in *; lia|constructor]. }
  pose proof (Mem.loadbytes_length _ _ _ _ _ LOAD) as LENGTH.
  assert (LEN : Z.of_nat (length values) = 144) by (rewrite LENGTH; reflexivity).
  assert (OUT : Mem.range_perm built output ofs (ofs + Z.of_nat (length values)) Cur Writable).
  { rewrite LEN. red; intros pos BOUND. apply (scalar_stores_permissions _ _ _ _ STORES).
    eapply Mem.perm_alloc_1; [exact ALLOC|apply WRITABLE; exact BOUND]. }
  destruct (Mem.range_perm_storebytes _ _ _ _ OUT) as [copied COPY].
  assert (COPYLOC : assign_loc result_ge result_type built output (Ptrofs.repr ofs) Full
      (Vptr local Ptrofs.zero) copied).
  { assert (REP : Ptrofs.unsigned (Ptrofs.repr ofs) = ofs)
      by (apply Ptrofs.unsigned_repr; unfold Ptrofs.max_unsigned; lia).
    eapply assign_loc_copy with (bytes := values).
    - reflexivity.
    - intros; exists 0; reflexivity.
    - intros; rewrite REP; exact ALIGN.
    - left; congruence.
    - exact LOAD.
    - rewrite REP; exact COPY. }
  assert (COPIED_RANGE : Mem.range_perm copied local 0 144 Cur Freeable).
  { red; intros; eapply Mem.perm_storebytes_1; [exact COPY|apply BUILT_RANGE; assumption]. }
  assert (PA : result_preserved base output ofs allocated).
  { eapply Mem.alloc_unchanged_on; exact ALLOC. }
  assert (PB : result_preserved base output ofs built).
  { eapply result_local_stores_preserves; eassumption. }
  assert (PC : result_preserved base output ofs copied).
  { eapply Mem.unchanged_on_trans; [exact PB|]. eapply Mem.storebytes_unchanged_on; [exact COPY|].
    intros pos BOUND [_ [NE|[BEFORE|AFTER]]]; rewrite LEN in BOUND; lia. }
  exists allocated, local, built, copied. split; [reflexivity|].
  split; [exact FRESH|]. split; [exact LOCAL|]. split; [exact STORES|].
  split; [exact COPYLOC|]. split.
  - eapply decoded_struct_copy_fields;
      [eapply decoded_cells_complete; exact STORES|exact ALIGN|exact LOAD|exact COPY].
  - auto.
Qed.

Theorem decoder_owned_construction : forall (cell : tls) base output ofs p bytes k le,
  readable_bytes base p bytes -> length bytes = 160%nat ->
  result_destination base output ofs -> frame_output_separate p bytes output ofs ->
  le ! _p = Some (address_value p) -> le ! _r = Some (Vptr output (Ptrofs.repr ofs)) ->
  exists allocated local copied count le',
    Mem.alloc base 0 144 = (allocated,local) /\
    store_path result_ge (result_preserved base output ofs)
      (State Slice.f_decode_frame decoder_construction k (decoder_env local) le allocated) count
      (State Slice.f_decode_frame Sskip k (decoder_env local) le' copied) /\
    decoded_contents copied output ofs bytes /\
    Mem.range_perm copied local 0 144 Cur Freeable /\
    le' ! _p = Some (address_value p) /\ le' ! _r = Some (Vptr output (Ptrofs.repr ofs)).
Proof.
  intros cell base output ofs p bytes k le READ LEN DEST SEP PTR OUT.
  destruct (decoder_storage_exists base output ofs bytes DEST)
    as [allocated [local [built [copied [ALLOC [FRESH [LOCAL [STORES [COPY [CONTENT [FREE [PA PC]]]]]]]]]]]].
  destruct (decoder_construction_source_path cell (result_preserved base output ofs)
    allocated local built copied output ofs p bytes k le PTR OUT LEN STORES COPY PA PC)
    as [count [le' [PATH [PTR' OUT']]]].
  - intros; eapply frame_preserved_readable; eassumption.
  - intros; eapply result_local_store_preserves; eassumption.
  - exists allocated, local, copied, count, le'.
    split; [exact ALLOC|]. split; [exact PATH|]. split; [exact CONTENT|].
    split; [exact FREE|]. auto.
Qed.
