(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Source byte stores use writable ownership and a private-region frame. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata.
Require Import WriteBytes.
From HostGateway Require Import GatewayFrames.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_byte_region (block:block)(offset:Z)(width:nat) other position : Prop :=
  other=block /\ offset<=position<offset+Z.of_nat width.

Record gateway_bytes_ready block offset width (written:list int)(memory:mem) : Prop := {
  gateway_ready_length : (length written<=width)%nat;
  gateway_ready_permissions : Mem.range_perm memory block offset(offset+Z.of_nat width)Cur Writable;
  gateway_ready_loads : forall index value,nth_error written index=Some value ->
    Mem.load Mint8unsigned memory block(offset+Z.of_nat index)=Some(Vint value)
}.

Lemma gateway_bytes_initial block offset width memory :
  Mem.range_perm memory block offset(offset+Z.of_nat width)Cur Writable ->
  gateway_bytes_ready block offset width [] memory.
Proof. intro OWN;constructor;[cbn;lia|exact OWN|intros index value LOAD;destruct index;discriminate]. Qed.

Lemma gateway_bytes_ready_closed block offset width written :
  gateway_region_closed(gateway_byte_region block offset width)
    (gateway_bytes_ready block offset width written).
Proof.
  intros before after[COUNT OWN LOADS]FRAME;constructor;[exact COUNT| |].
  - intros position RANGE;eapply Mem.perm_unchanged_on;[exact FRAME|split;[reflexivity|exact RANGE]|].
    apply OWN;exact RANGE.
  - intros index value SELECTED.
    assert(INDEX:(index<length written)%nat).
    { apply nth_error_Some;rewrite SELECTED;discriminate. }
    eapply Mem.load_unchanged_on;[exact FRAME| |apply LOADS;exact SELECTED].
    intros position RANGE;split;[reflexivity|]. cbn[size_chunk]in RANGE.
    apply Nat2Z.inj_le in COUNT;apply Nat2Z.inj_lt in INDEX;lia.
Qed.

Lemma gateway_bytes_store block offset width written memory value :
  gateway_bytes_ready block offset width written memory -> (length written<width)%nat ->
  Int.zero_ext 8 value=value ->
  exists after,Mem.store Mint8unsigned memory block(offset+Z.of_nat(length written))(Vint value)=Some after /\
    gateway_bytes_ready block offset width(written++[value])after.
Proof.
  intros[COUNT OWN LOADS]SPACE BYTE.
  destruct(Mem.valid_access_store memory Mint8unsigned block(offset+Z.of_nat(length written))(Vint value))
    as[after STORE].
  { split;[|apply Z.divide_1_l]. intros position RANGE;apply OWN.
    cbn[size_chunk]in RANGE;apply Nat2Z.inj_lt in SPACE;lia. }
  exists after;split;[exact STORE|];constructor.
  - rewrite length_app;cbn;lia.
  - intros position RANGE;eapply Mem.perm_store_1;[exact STORE|apply OWN;exact RANGE].
  - intros index selected MEMBER.
    destruct(lt_dec index(length written))as[EARLIER|LATER].
    + rewrite nth_error_app1 in MEMBER by exact EARLIER.
      erewrite Mem.load_store_other;[apply LOADS;exact MEMBER|exact STORE|].
      right;left;cbn[size_chunk];apply Nat2Z.inj_lt in EARLIER;lia.
    + rewrite nth_error_app2 in MEMBER by lia.
      destruct(index-length written)%nat eqn:AT;[|destruct n;discriminate].
      cbn in MEMBER;inversion MEMBER;subst selected.
      assert(SAME:index=length written)by lia;subst index.
      erewrite Mem.load_store_same by exact STORE.
      cbn[Val.load_result];rewrite BYTE;reflexivity.
Qed.

Lemma gateway_single_byte_load memory block offset value :
  Mem.load Mint8unsigned memory block offset=Some(Vint value) ->
  Mem.loadbytes memory block offset 1=Some[byte_encoding value].
Proof.
  intro LOAD.
  destruct(Mem.load_loadbytes _ _ _ _ _ LOAD)as[bytes[BYTES DECODE]].
  pose proof(Mem.loadbytes_length _ _ _ _ _ BYTES)as LENGTH.
  change(length bytes=1%nat)in LENGTH.
  destruct bytes as[|first rest];[discriminate|].
  destruct rest;[|discriminate].
  destruct first;cbn[decode_val decode_int proj_bytes]in DECODE;try discriminate.
  inversion DECODE;subst value.
  unfold byte_encoding.
  pose proof(Byte.unsigned_range i)as RANGE;change(0<=Byte.unsigned i<256)in RANGE.
  change(decode_int[i])with(Byte.unsigned i+256*0).
  rewrite ?Z.mul_0_r,?Z.add_0_r.
  rewrite Int.zero_ext_mod by(change(0<=8<32);lia).
  rewrite Int.unsigned_repr by(change Int.max_unsigned with 4294967295;lia).
  change(Mem.loadbytes memory block offset 1=
    Some[Byte(Byte.repr(Byte.unsigned i mod 256))]).
  rewrite Z.mod_small by exact RANGE;rewrite Byte.repr_unsigned;exact BYTES.
Qed.

Lemma gateway_loadbytes_from_loads memory block offset values :
  (forall index value,nth_error values index=Some value ->
    Mem.load Mint8unsigned memory block(offset+Z.of_nat index)=Some(Vint value)) ->
  Mem.loadbytes memory block offset(Z.of_nat(length values))=Some(map byte_encoding values).
Proof.
  revert offset;induction values as[|value rest IH];intros offset LOADS.
  - change(Mem.loadbytes memory block offset 0=Some[]);apply Mem.loadbytes_empty;lia.
  - assert(HEAD:Mem.loadbytes memory block offset 1=Some[byte_encoding value]).
    { apply gateway_single_byte_load.
      specialize(LOADS 0%nat value eq_refl);replace(offset+Z.of_nat 0)with offset in LOADS by lia;exact LOADS. }
    assert(TAIL:Mem.loadbytes memory block(offset+1)(Z.of_nat(length rest))=Some(map byte_encoding rest)).
    { apply IH;intros index selected MEMBER.
      specialize(LOADS(S index)selected MEMBER);rewrite Nat2Z.inj_succ in LOADS.
      replace(offset+1+Z.of_nat index)with(offset+Z.succ(Z.of_nat index))by lia;exact LOADS. }
    cbn[length map];rewrite Nat2Z.inj_succ.
    replace(Z.succ(Z.of_nat(length rest)))with(1+Z.of_nat(length rest))by lia.
    change(Some(byte_encoding value::map byte_encoding rest))with
      (Some([byte_encoding value]++map byte_encoding rest)).
    eapply Mem.loadbytes_concat;[exact HEAD|exact TAIL|lia|lia].
Qed.

Theorem gateway_bytes_complete block offset width written memory :
  gateway_bytes_ready block offset width written memory -> length written=width ->
  Mem.loadbytes memory block offset(Z.of_nat width)=Some(map byte_encoding written).
Proof. intros[_ _ LOADS]LENGTH;rewrite<-LENGTH;apply gateway_loadbytes_from_loads;exact LOADS. Qed.

Definition gateway_read_ready block ofs (values:list int)(memory:mem) : Prop :=
  forall index value,nth_error values index=Some value ->
    Mem.loadv Mint8unsigned memory
      (Vptr block(Ptrofs.add ofs(Ptrofs.repr(Z.of_nat index))))=Some(Vint value).

Lemma gateway_pointer_index ofs width index :
  Ptrofs.unsigned ofs+Z.of_nat width<=Ptrofs.modulus -> (index<width)%nat ->
  Ptrofs.unsigned(Ptrofs.add ofs(Ptrofs.repr(Z.of_nat index)))=Ptrofs.unsigned ofs+Z.of_nat index.
Proof.
  intros BOUND INDEX;pose proof(Ptrofs.unsigned_range ofs)as OFFSET.
  apply Nat2Z.inj_lt in INDEX.
  rewrite Ptrofs.add_unsigned.
  rewrite(Ptrofs.unsigned_repr(Z.of_nat index))by(unfold Ptrofs.max_unsigned;lia).
  rewrite Ptrofs.unsigned_repr;[reflexivity|unfold Ptrofs.max_unsigned;lia].
Qed.

Lemma gateway_read_ready_closed block ofs values :
  Ptrofs.unsigned ofs+Z.of_nat(length values)<=Ptrofs.modulus ->
  gateway_region_closed(gateway_byte_region block(Ptrofs.unsigned ofs)(length values))
    (gateway_read_ready block ofs values).
Proof.
  intros BOUND before after LOADS FRAME index value SELECTED.
  assert(INDEX:(index<length values)%nat)by(apply nth_error_Some;rewrite SELECTED;discriminate).
  specialize(LOADS index value SELECTED).
  unfold Mem.loadv in LOADS|-*.
  rewrite(gateway_pointer_index ofs(length values)index BOUND INDEX)in LOADS|-*.
  cbn[size_chunk]in LOADS|-*.
  rewrite zle_true in LOADS|-* by(apply Nat2Z.inj_lt in INDEX;lia).
  eapply Mem.load_unchanged_on;[exact FRAME| |exact LOADS].
  intros position RANGE;split;[reflexivity|].
  cbn[size_chunk]in RANGE;apply Nat2Z.inj_lt in INDEX;lia.
Qed.
