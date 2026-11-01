(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.main-inputs: Owned NUL-terminated fields in a freshly allocated byte block. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata.
Require Import Readers WriteMemory ScalarMemory.
From LeanCageMainNumber Require Import NumberMemory.
From LeanCageMain Require Import MainMemory.
Import ListNotations.
Open Scope Z_scope.
Fixpoint packed_bytes fields : list byte := match fields with
 | []=>[]|bytes::rest=>(bytes++[Byte.zero])++packed_bytes rest end.
Fixpoint packed_inputs block ofs fields : list numeric_input := match fields with
 | []=>[]|bytes::rest=>{|input_block:=block;input_offset:=Ptrofs.repr ofs;input_bytes:=bytes|}::
 packed_inputs block(ofs+Z.of_nat(length(bytes++[Byte.zero])))rest end.
Definition inputs_owned m inputs := Forall(fun x=>number_input m(input_block x)(input_offset x)(input_bytes x))inputs.
Lemma packed_inputs_length b ofs fields : length(packed_inputs b ofs fields)=length fields.
Proof. revert ofs;induction fields;intros ofs;cbn;auto. Qed.
Lemma packed_inputs_data b ofs fields : map input_bytes(packed_inputs b ofs fields)=fields.
Proof. revert ofs;induction fields;intros ofs;cbn;[reflexivity|rewrite IHfields;reflexivity]. Qed.
Lemma packed_inputs_block b ofs fields : Forall(fun x=>input_block x=b)(packed_inputs b ofs fields).
Proof. revert ofs;induction fields;intros ofs;constructor;[reflexivity|apply IHfields]. Qed.
Theorem packed_inputs_owned m b ofs fields :
 Forall(fun bytes=>Forall(fun byte=>byte<>Byte.zero)bytes)fields -> 0<=ofs ->
 ofs+Z.of_nat(length(packed_bytes fields))<=Ptrofs.modulus ->
 Mem.loadbytes m b ofs(Z.of_nat(length(packed_bytes fields)))=Some(map Byte(packed_bytes fields)) ->
 inputs_owned m(packed_inputs b ofs fields).
Proof.
 revert ofs;induction fields as[|bytes rest IH];intros ofs NOZERO LOW HIGH LOAD;[constructor|].
 inversion NOZERO as[|? ? HERE REST];subst.
 change(Mem.loadbytes m b ofs(Z.of_nat(length((bytes++[Byte.zero])++packed_bytes rest)))=
  Some(map Byte((bytes++[Byte.zero])++packed_bytes rest)))in LOAD.
 change(ofs+Z.of_nat(length((bytes++[Byte.zero])++packed_bytes rest))<=Ptrofs.modulus)in HIGH.
 constructor.
 - unfold number_input;cbn[input_block input_offset input_bytes].
   rewrite Ptrofs.unsigned_repr by(unfold Ptrofs.max_unsigned;rewrite !length_app in HIGH;cbn[length]in HIGH;lia).
   split;[rewrite length_app in HIGH;lia|]. split;[exact HERE|apply load_first with(rest:=packed_bytes rest);exact LOAD].
 - apply IH;[exact REST|lia|rewrite length_app in HIGH;lia|].
   apply load_suffix with(done:=bytes++[Byte.zero]);exact LOAD.
Qed.
Lemma number_input_valid m b ofs bytes : number_input m b ofs bytes -> Mem.valid_block m b.
Proof.
 intros[BOUND[NOZERO LOAD]].
 eapply Mem.perm_valid_block with(ofs:=Ptrofs.unsigned ofs)(k:=Cur)(p:=Readable);eapply Mem.loadbytes_range_perm;[exact LOAD|].
 rewrite length_app;cbn[length];lia.
Qed.
Lemma number_input_after_alloc m next new lo hi b ofs bytes :
 Mem.alloc m lo hi=(next,new) -> number_input m b ofs bytes ->
 number_input next b ofs bytes /\ b<>new.
Proof.
 intros ALLOC INPUT;pose proof(number_input_valid _ _ _ _ INPUT)as VALID.
 destruct INPUT as[BOUND[NOZERO LOAD]];split.
 - split;[exact BOUND|]. split;[exact NOZERO|].
   rewrite(Mem.loadbytes_alloc_unchanged _ _ _ _ _ ALLOC _ _ _ VALID);exact LOAD.
 - intro EQ;subst new;eapply Mem.fresh_block_alloc;eassumption.
Qed.
Lemma inputs_owned_after_alloc m next new lo hi inputs :
 Mem.alloc m lo hi=(next,new) -> inputs_owned m inputs ->
 inputs_owned next inputs /\ Forall(fun x=>input_block x<>new)inputs.
Proof.
 intros ALLOC OWN;induction OWN as[|x rest INPUT OWN IH];[split;constructor|].
 destruct(number_input_after_alloc _ _ _ _ _ _ _ _ ALLOC INPUT)as[NEW NE];destruct IH as[TAIL SEP];split;constructor;assumption.
Qed.
Lemma policy_writable_after_alloc m next new lo hi policy :
 Mem.alloc m lo hi=(next,new) -> policy_writable m policy -> policy_writable next policy.
Proof.
 intros ALLOC OWN i INDEX;destruct(OWN i INDEX)as[BOUND ACCESS];split;[exact BOUND|].
 eapply Mem.valid_access_alloc_other;eassumption.
Qed.
Lemma policy_writable_after_storebytes m next b ofs bytes policy :
 Mem.storebytes m b ofs bytes=Some next -> policy_writable m policy -> policy_writable next policy.
Proof.
 intros STORE OWN i INDEX;destruct(OWN i INDEX)as[BOUND ACCESS];split;[exact BOUND|].
 eapply Mem.storebytes_valid_access_1;eassumption.
Qed.
Lemma policy_writable_after_stores m next b cells policy :
 scalar_stores b m cells next -> policy_writable m policy -> policy_writable next policy.
Proof.
 intros STORES OWN i INDEX;destruct(OWN i INDEX)as[BOUND[PERM ALIGN]];split;[exact BOUND|]. split;[|exact ALIGN].
 red;intros pos RANGE;apply(scalar_stores_permissions _ _ _ _ STORES);apply PERM;exact RANGE.
Qed.
Lemma inputs_owned_after_stores m next b cells inputs :
 scalar_stores b m cells next -> inputs_owned m inputs -> Forall(fun x=>input_block x<>b)inputs ->
 inputs_owned next inputs.
Proof.
 intros STORES;induction STORES;intros OWN SEP;[exact OWN|]. apply IHSTORES;[|exact SEP].
 unfold inputs_owned in *;rewrite Forall_forall in *;intros x IN;destruct(OWN x IN)as[BOUND[NOZERO LOAD]];split;[exact BOUND|]. split;[exact NOZERO|].
 rewrite(Mem.loadbytes_store_other _ _ _ _ _ _ H)by(auto using SEP);exact LOAD.
Qed.
