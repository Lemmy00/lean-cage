(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Native signed-character loads denote the exact received bytes,
   including high bytes rejected by the numeric scanner. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps Readers LocalAccess.
From HostGateway Require Import GatewaySource GatewayValueEntry GatewayIntegerLoop GatewayWordsMemory GatewayWordReceipt.
Import ListNotations.
Open Scope Z_scope.

Lemma gateway_integer_signed_byte byte:
  Int.sign_ext 8(byte_word byte)=Int.repr(Byte.signed byte).
Proof.
  pose proof(Int.sign_ext_range 8(byte_word byte)ltac:(change(0<8<32);lia))as RANGE.
  pose proof(Int.eqmod_sign_ext 8(byte_word byte)ltac:(change(0<8<32);lia))as[quotient CONGRUENT].
  change(-128<=Int.signed(Int.sign_ext 8(byte_word byte))<128)in RANGE.
  unfold byte_word in CONGRUENT.
  rewrite Int.unsigned_repr in CONGRUENT by(pose proof(Byte.unsigned_range byte);
    change Byte.modulus with 256 in *;change Int.max_unsigned with 4294967295;lia).
  change(two_p 8)with 256 in CONGRUENT.
  pose proof(Byte.unsigned_range byte)as BYTE;change(0<=Byte.unsigned byte<256)in BYTE.
  assert(SIGNED:Int.signed(Int.sign_ext 8(byte_word byte))=Byte.signed byte).
  { unfold byte_word in *;unfold Byte.signed;change Byte.half_modulus with 128;change Byte.modulus with 256.
    destruct(zlt(Byte.unsigned byte)128);lia. }
  rewrite<-(Int.repr_signed(Int.sign_ext 8(byte_word byte))),SIGNED;reflexivity.
Qed.

Theorem gateway_integer_byte_load memory object bytes index byte:
  Z.of_nat(length bytes)<=65536->
  Mem.loadbytes memory object 0(Z.of_nat(length bytes))=Some(inj_bytes bytes)->nth_error bytes index=Some byte->
  Mem.loadv Mint8signed memory(Vptr object(Ptrofs.repr(Z.of_nat index)))=Some(Vint(Int.repr(Byte.signed byte))).
Proof.
  intros BOUND LOAD SELECTED.
  pose proof(gateway_read_ready_from_bytes memory object Ptrofs.zero bytes
    ltac:(change(0+Z.of_nat(length bytes)<=18446744073709551616);lia)LOAD)as READY.
  specialize(READY index(byte_word byte)ltac:(rewrite nth_error_map,SELECTED;reflexivity)).
  rewrite Ptrofs.add_zero_l in READY.
  unfold Mem.loadv in READY|-*;destruct(zle _ _);[|discriminate].
  rewrite Mem.load_int8_signed_unsigned,READY.
  change(Some(Vint(Int.sign_ext 8(byte_word byte)))=Some(Vint(Int.repr(Byte.signed byte)))).
  rewrite gateway_integer_signed_byte;reflexivity.
Qed.

Lemma gateway_integer_fixed_character ge environment parameters memory object index byte:
  0<=index<=32->parameters!_bytes=Some(Vptr object Ptrofs.zero)->
  Mem.loadv Mint8signed memory(Vptr object(Ptrofs.repr index))=Some(Vint(Int.repr(Byte.signed byte)))->
  expression_value ge environment parameters memory
    (Ederef(Ebinop Oadd(Etempvar _bytes(tptr tschar))(Econst_int(Int.repr index)tint)(tptr tschar))tschar)
    (Vint(Int.repr(Byte.signed byte))).
Proof.
  intros INDEX BYTES LOAD.
  eapply location_read_value with(b:=object)(ofs:=Ptrofs.repr index).
  - apply pointer_location_value;eapply binary_expression_value with(v:=Vptr object Ptrofs.zero)(w:=Vint(Int.repr index)).
    + apply old_expression_value,value_temp;exact BYTES.
    + apply old_expression_value,value_int.
    + change(Some(Vptr object(Ptrofs.add Ptrofs.zero(Ptrofs.mul Ptrofs.one(Ptrofs.of_ints(Int.repr index)))))=
        Some(Vptr object(Ptrofs.repr index))).
      rewrite Ptrofs.add_zero_l,Ptrofs.mul_commut,Ptrofs.mul_one.
      unfold Ptrofs.of_ints;rewrite Int.signed_repr by(change Int.min_signed with (-2147483648);
        change Int.max_signed with 2147483647;lia);reflexivity.
  - apply deref_loc_value with(chunk:=Mint8signed);[reflexivity|exact LOAD].
Qed.

Lemma gateway_integer_temporary_character ge environment parameters memory identifier object index byte:
  0<=index<=32->parameters!_bytes=Some(Vptr object Ptrofs.zero)->parameters!identifier=Some(Vlong(Int64.repr index))->
  Mem.loadv Mint8signed memory(Vptr object(Ptrofs.repr index))=Some(Vint(Int.repr(Byte.signed byte)))->
  expression_value ge environment parameters memory
    (Ederef(Ebinop Oadd(Etempvar _bytes(tptr tschar))(Etempvar identifier tulong)(tptr tschar))tschar)
    (Vint(Int.repr(Byte.signed byte))).
Proof.
  intros INDEX BYTES POSITION LOAD.
  eapply location_read_value with(b:=object)(ofs:=Ptrofs.repr index).
  - apply pointer_location_value;eapply binary_expression_value with(v:=Vptr object Ptrofs.zero)(w:=Vlong(Int64.repr index)).
    + apply old_expression_value,value_temp;exact BYTES.
    + apply old_expression_value,value_temp;exact POSITION.
    + change(Some(Vptr object(Ptrofs.add Ptrofs.zero(Ptrofs.mul Ptrofs.one(Ptrofs.of_int64(Int64.repr index)))))=
        Some(Vptr object(Ptrofs.repr index))).
      rewrite Ptrofs.add_zero_l,Ptrofs.mul_commut,Ptrofs.mul_one.
      unfold Ptrofs.of_int64;rewrite Int64.unsigned_repr by(change Int64.max_unsigned with 18446744073709551615;lia);reflexivity.
  - apply deref_loc_value with(chunk:=Mint8signed);[reflexivity|exact LOAD].
Qed.
