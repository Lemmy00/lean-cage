(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.decimal: Exact source parsing, memory behavior and interruption. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata.
Require Import Readers WriteMemory.
Import ListNotations.
Open Scope Z_scope.
Definition number_input m b ofs bytes :=
 Ptrofs.unsigned ofs + Z.of_nat (length (bytes++[Byte.zero])) <= Ptrofs.modulus /\
 Forall (fun byte => byte<>Byte.zero) bytes /\
 Mem.loadbytes m b (Ptrofs.unsigned ofs) (Z.of_nat (length (bytes++[Byte.zero]))) =
 Some (map Byte (bytes++[Byte.zero])).
Definition number_output m b ofs :=
 Ptrofs.unsigned ofs+8<=Ptrofs.modulus /\ Mem.valid_access m Mint64 b (Ptrofs.unsigned ofs) Writable.
Lemma number_input_head m b ofs byte rest :
 number_input m b ofs (byte::rest) -> byte<>Byte.zero.
Proof. intros [_ [NE _]];inversion NE;assumption. Qed.
Lemma number_read_head m b ofs bytes byte tail :
 number_input m b ofs bytes -> bytes++[Byte.zero]=byte::tail ->
 Mem.loadv Mint8unsigned m (Vptr b ofs)=Some(Vint (byte_word byte)) /\
 Mem.loadv Mint8signed m (Vptr b ofs)=Some(Vint(Int.sign_ext 8 (Int.repr(Byte.unsigned byte)))).
Proof.
 intros [BOUND [NE LOAD]] BYTES. rewrite BYTES in LOAD,BOUND.
 pose proof (load_first m b (Ptrofs.unsigned ofs) [byte] tail LOAD) as ONE.
 assert (U : Mem.load Mint8unsigned m b (Ptrofs.unsigned ofs)=Some(Vint(byte_word byte))).
 { rewrite <- decode_byte. eapply Mem.loadbytes_load;[exact ONE|apply Z.divide_1_l]. }
 assert (S : Mem.load Mint8signed m b (Ptrofs.unsigned ofs)=Some(Vint(Int.sign_ext 8 (Int.repr(Byte.unsigned byte))))).
 { replace (Vint(Int.sign_ext 8 (Int.repr(Byte.unsigned byte)))) with (decode_val Mint8signed [Byte byte]).
   - eapply Mem.loadbytes_load;[exact ONE|apply Z.divide_1_l].
   - change (Vint(Int.sign_ext 8 (Int.repr(Byte.unsigned byte+256*0)))=Vint(Int.sign_ext 8 (Int.repr(Byte.unsigned byte)))).
     rewrite Z.mul_0_r,Z.add_0_r;reflexivity. }
 unfold Mem.loadv; cbn [size_chunk].
 destruct (zle (Ptrofs.unsigned ofs+1) Ptrofs.modulus);[auto|cbn in BOUND;lia].
Qed.
Lemma number_input_tail m b ofs byte rest :
 number_input m b ofs (byte::rest) ->
 number_input m b (Ptrofs.add ofs Ptrofs.one) rest.
Proof.
 intros [BOUND [NE LOAD]].
 assert (OFFSET : Ptrofs.unsigned(Ptrofs.add ofs Ptrofs.one)=Ptrofs.unsigned ofs+1).
 { unfold Ptrofs.add. change (Ptrofs.unsigned (Ptrofs.repr(Ptrofs.unsigned ofs+1))=Ptrofs.unsigned ofs+1).
   apply Ptrofs.unsigned_repr. pose proof (Ptrofs.unsigned_range ofs).
   unfold Ptrofs.max_unsigned. rewrite length_app in BOUND;cbn in BOUND;lia. }
 unfold number_input;rewrite OFFSET;split.
 - rewrite length_app in *;cbn in *;lia.
 - split;[inversion NE;assumption|].
   exact (load_suffix m b (Ptrofs.unsigned ofs) [byte] (rest++[Byte.zero]) LOAD).
Qed.
Lemma number_store_exists m b ofs value :
 number_output m b ofs -> exists after, Mem.storev Mint64 m (Vptr b ofs) (Vlong value)=Some after.
Proof.
 intros [BOUND ACCESS]. destruct (Mem.valid_access_store _ _ _ _ (Vlong value) ACCESS) as [after STORE].
 exists after. unfold Mem.storev. destruct (zle (Ptrofs.unsigned ofs+size_chunk Mint64) Ptrofs.modulus);[exact STORE|cbn in *;lia].
Qed.
