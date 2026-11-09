(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.acceptance: Derive a useful admitted frame from the actual result constructor bytes. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata Ctypes Clight.
Require Import Library ScalarMemory FrameRecord FrameAllocation.
From EntryReporting Require Import ResultLayout ResultSafety.
Import ListNotations.
Open Scope Z_scope.

Lemma namespace_zero_byte_load memory object offset:
  Mem.load Mint8unsigned memory object offset=Some(Vint Int.zero) ->
  Mem.loadbytes memory object offset 1=Some[Byte Byte.zero].
Proof.
  intro LOAD;destruct(Mem.load_loadbytes _ _ _ _ _ LOAD)as[values[BYTES DECODE]].
  pose proof(Mem.loadbytes_length _ _ _ _ _ BYTES)as SIZE.
  change(length values=1%nat)in SIZE.
  destruct values as[|value rest];[discriminate|];destruct rest;[|discriminate].
  destruct value as[|byte|fragment quantity index].
  - rewrite decode_val_undef in DECODE;discriminate.
  - rewrite Readers.decode_byte in DECODE.
    assert(WORD:Int.zero=Readers.byte_word byte)by congruence.
    assert(BYTE:byte=Byte.zero).
    { pose proof(Byte.unsigned_range byte)as RANGE;change(0<=Byte.unsigned byte<256)in RANGE.
      apply(f_equal Int.unsigned)in WORD;unfold Readers.byte_word in WORD.
      rewrite Int.unsigned_zero,Int.unsigned_repr in WORD by
        (change(0<=Byte.unsigned byte<=4294967295);lia).
      rewrite <-(Byte.repr_unsigned byte);replace(Byte.unsigned byte)with 0 by lia;reflexivity. }
    subst byte;exact BYTES.
  - cbn in DECODE;discriminate.
Qed.

From EntryReporting Require Import FrameCopy.

Theorem namespace_copy_owned_frame before src dst r digest:
  src<>dst ->frame_result_owned before src 0 r digest ->
  Mem.range_perm before dst 0 144 Cur Freeable ->
  exists after,assign_loc result_ge result_type before dst Ptrofs.zero Full
    (Vptr src Ptrofs.zero)after /\frame_result_owned after dst 0 r digest /\
    Mem.range_perm after dst 0 144 Cur Freeable /\
    Mem.unchanged_on(fun object _=>object<>dst)before after.
Proof.
  intros SEPARATE OWN WRITABLE.
  pose proof OWN as[LOW[HIGH[ALIGN[READABLE[LENGTH REST]]]]].
  destruct(Mem.range_perm_loadbytes before src 0 144 READABLE)as[values LOAD].
  assert(SIZE:Z.of_nat(length values)=144)by(rewrite(Mem.loadbytes_length _ _ _ _ _ LOAD);reflexivity).
  assert(WRITE:Mem.range_perm before dst 0(0+Z.of_nat(length values))Cur Writable).
  { rewrite SIZE;intros position RANGE;eapply Mem.perm_implies;[apply WRITABLE;exact RANGE|constructor]. }
  destruct(Mem.range_perm_storebytes _ _ _ _ WRITE)as[after STORE].
  assert(AFTER:Mem.range_perm after dst 0 144 Cur Freeable).
  { intros position RANGE;eapply Mem.perm_storebytes_1;[exact STORE|apply WRITABLE;exact RANGE]. }
  destruct(frame_copied_contents _ _ _ _ _ _ _ _ OWN LOAD STORE)as[CELLS DIGEST].
  exists after;split.
  - eapply assign_loc_copy with(bytes:=values).
    + reflexivity.
    + intros;apply Z.divide_0_r.
    + intros;apply Z.divide_0_r.
    + left;exact SEPARATE.
    + exact LOAD.
    + exact STORE.
  - split.
    + split;[lia|]. split;[exact HIGH|]. split;[exact ALIGN|]. split.
      * intros position RANGE;eapply Mem.perm_implies;[apply AFTER;exact RANGE|constructor].
      * split;[exact LENGTH|]. split;assumption.
    + split;[exact AFTER|]. eapply Mem.storebytes_unchanged_on;[exact STORE|intros;congruence].
Qed.

Lemma namespace_zero_bytes memory object offset count:
  (forall index,(index<count)%nat->
    Mem.load Mint8unsigned memory object(offset+Z.of_nat index)=Some(Vint Int.zero)) ->
  Mem.loadbytes memory object offset(Z.of_nat count)=Some(repeat(Byte Byte.zero)count).
Proof.
  revert offset;induction count as[|count IH];intros offset LOAD.
  - apply Mem.loadbytes_empty;lia.
  - assert(HEAD:Mem.loadbytes memory object offset 1=Some[Byte Byte.zero]).
    { apply namespace_zero_byte_load;replace offset with(offset+Z.of_nat 0)by lia;apply LOAD;lia. }
    assert(TAIL:Mem.loadbytes memory object(offset+1)(Z.of_nat count)=Some(repeat(Byte Byte.zero)count)).
    { apply IH;intros index RANGE;replace(offset+1+Z.of_nat index)with(offset+Z.of_nat(S index))by lia.
      apply LOAD;lia. }
    replace(Z.of_nat(S count))with(1+Z.of_nat count)by lia.
    exact(Mem.loadbytes_concat _ _ _ _ _ _ _ HEAD TAIL ltac:(lia)ltac:(lia)).
Qed.

Definition namespace_admitted_record run uid milliseconds:frame_result:=
  {|fr_kind:=Int.repr 5;fr_stage:=Int.zero;fr_detail:=Int.zero;fr_entry:=Int.zero;
    fr_clean:=Int.zero;fr_triggers:=Int.zero;fr_uid:=uid;fr_run:=run;
    fr_cpu:=Int64.zero;fr_peak:=Int64.zero;fr_out:=Int64.zero;fr_err:=Int64.zero;fr_elapsed:=milliseconds;
    fr_oom:=Int64.zero;fr_pids:=Int64.zero;fr_export_state:=Int.zero;fr_omitted:=Int.zero;fr_export_error:=Int.zero|}.

Lemma namespace_constructed_cells run uid:
  frame_result_cells(namespace_admitted_record run uid Int64.zero)(repeat Byte.zero 32)=
    result_cells(Int.repr 5)Int.zero Int.zero Int.zero uid run.
Proof. reflexivity. Qed.

Theorem namespace_constructed_frame memory object run uid:
  Mem.range_perm memory object 0 144 Cur Readable ->
  result_contents memory object 0(Int.repr 5)Int.zero Int.zero Int.zero uid run ->
  frame_result_owned memory object 0(namespace_admitted_record run uid Int64.zero)(repeat Byte.zero 32).
Proof.
  intros OWN CONTENTS;split;[lia|]. split;[change(144<=18446744073709551616);lia|].
  split;[apply Z.divide_0_r|]. split;[exact OWN|]. split;[apply repeat_length|]. split.
  - intros cell MEMBER;rewrite namespace_constructed_cells in MEMBER;apply CONTENTS;exact MEMBER.
  - split;[unfold span_bounds;cbn;change(0<=108<18446744073709551616 /\108+32<=18446744073709551616 /\32<=18446744073709551615);lia|].
    change(Mem.loadbytes memory object 108 32=Some(map Byte(repeat Byte.zero 32))).
    rewrite map_repeat;apply(namespace_zero_bytes memory object 108 32).
    intros index RANGE;specialize(CONTENTS(digest_cell index)).
    cbn[digest_cell scalar_chunk scalar_offset scalar_value Val.load_result]in CONTENTS.
    replace(0+(108+Z.of_nat index))with(108+Z.of_nat index)in CONTENTS by lia.
    apply CONTENTS;unfold result_cells;apply in_or_app;right;apply in_map;apply in_seq;lia.
Qed.

Lemma namespace_elapsed_cell run uid before after cell:
  In cell(frame_result_cells(namespace_admitted_record run uid after)(repeat Byte.zero 32)) ->
  cell=cell64 72 after \/
  In cell(frame_result_cells(namespace_admitted_record run uid before)(repeat Byte.zero 32)) /\
    (scalar_offset cell+size_chunk(scalar_chunk cell)<=72 \/80<=scalar_offset cell).
Proof.
  unfold frame_result_cells,namespace_admitted_record;cbn[fr_kind fr_stage fr_detail fr_entry fr_clean
    fr_triggers fr_uid fr_run fr_cpu fr_peak fr_out fr_err fr_elapsed fr_oom fr_pids
    fr_export_state fr_omitted fr_export_error].
  intro MEMBER;apply in_app_or in MEMBER;destruct MEMBER as[FIELDS|DIGEST].
  - repeat destruct FIELDS as[FIELDS|FIELDS];try contradiction;subst cell.
    all: first[left;reflexivity|right;split;[apply in_or_app;left;cbn;tauto|cbn;lia]].
  - right;split;[apply in_or_app;right;exact DIGEST|].
    apply in_map_iff in DIGEST;destruct DIGEST as[index[VALUE RANGE]];subst cell.
    cbn[frame_digest_cell scalar_offset];right;lia.
Qed.

Theorem namespace_store_elapsed memory after object run uid old milliseconds:
  frame_result_owned memory object 0(namespace_admitted_record run uid old)(repeat Byte.zero 32) ->
  Mem.store Mint64 memory object 72(Vlong milliseconds)=Some after ->
  frame_result_owned after object 0(namespace_admitted_record run uid milliseconds)(repeat Byte.zero 32).
Proof.
  intros[LOW[HIGH[ALIGN[READABLE[LENGTH[CELLS[BOUNDS BYTES]]]]]]]STORE.
  split;[exact LOW|]. split;[exact HIGH|]. split;[exact ALIGN|]. split.
  - intros position RANGE;eapply Mem.perm_store_1;[exact STORE|apply READABLE;exact RANGE].
  - split;[exact LENGTH|]. split.
    + intros cell MEMBER;destruct(namespace_elapsed_cell run uid old milliseconds cell MEMBER)
        as[SAME|[BEFORE SEPARATE]].
      * subst cell;change(Mem.load Mint64 after object 72=Some(Vlong milliseconds)).
        erewrite Mem.load_store_same by exact STORE;reflexivity.
      * replace(0+scalar_offset cell)with(scalar_offset cell)by lia.
        erewrite Mem.load_store_other;[|exact STORE|right;destruct SEPARATE;[left|right];cbn;lia].
        replace(scalar_offset cell)with(0+scalar_offset cell)by lia;apply CELLS;exact BEFORE.
    + split;[exact BOUNDS|].
      cbn[address_block address_offset]in BYTES|-*.
      erewrite Mem.loadbytes_store_other;[exact BYTES|exact STORE|right;right;cbn;lia].
Qed.

Theorem namespace_frame_unchanged before after object offset record digest:
  frame_result_owned before object offset record digest ->
  Mem.unchanged_on(fun other _=>other=object)before after ->
  frame_result_owned after object offset record digest.
Proof.
  intros[LOW[HIGH[ALIGN[RANGE[LENGTH[CELLS[BOUNDS BYTES]]]]]]]FRAME.
  split;[exact LOW|]. split;[exact HIGH|]. split;[exact ALIGN|]. split.
  - intros position BOUND;eapply Mem.perm_unchanged_on;
      [exact FRAME|reflexivity|apply RANGE;exact BOUND].
  - split;[exact LENGTH|]. split.
    + intros cell MEMBER;eapply Mem.load_unchanged_on;
        [exact FRAME|intros;reflexivity|apply CELLS;exact MEMBER].
    + split;[exact BOUNDS|]. eapply Mem.loadbytes_unchanged_on;
        [exact FRAME|intros;reflexivity|exact BYTES].
Qed.
