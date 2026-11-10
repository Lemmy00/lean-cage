(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: One-byte source effects retain disjoint initialized header data. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory.
From HostGateway Require Import GatewayFrames GatewayWordsMemory.
Import ListNotations.
Open Scope Z_scope.

Record gateway_write_family(block:Values.block)(offset:Z)(width:nat)(protected:Values.block->Z->Prop) := {
  gateway_family_ready : list int->mem->Prop;
  gateway_family_closed : forall written,gateway_region_closed protected(gateway_family_ready written);
  gateway_family_store : forall written memory value,
    gateway_family_ready written memory -> (length written<width)%nat -> Int.zero_ext 8 value=value ->
    exists after,Mem.store Mint8unsigned memory block(offset+Z.of_nat(length written))(Vint value)=Some after /\
      gateway_family_ready(written++[value])after
}.

Arguments gateway_family_ready {block offset width protected} _ _ _.
Arguments gateway_family_closed {block offset width protected} _ _.
Arguments gateway_family_store {block offset width protected} _ _ _ _ _ _ _.

Definition gateway_simple_family block offset width :
    gateway_write_family block offset width(gateway_byte_region block offset width) := {|
  gateway_family_ready:=gateway_bytes_ready block offset width;
  gateway_family_closed:=gateway_bytes_ready_closed block offset width;
  gateway_family_store:=gateway_bytes_store block offset width
|}.

Definition gateway_join_region (first second:block->Z->Prop) block offset := first block offset \/ second block offset.

Definition gateway_extended_ready block offset width read_only initial written memory :=
  gateway_bytes_ready block offset width written memory /\ Mem.unchanged_on read_only initial memory.

Lemma gateway_extended_closed block offset width read_only initial written :
  gateway_region_closed(gateway_join_region(gateway_byte_region block offset width)read_only)
    (gateway_extended_ready block offset width read_only initial written).
Proof.
  intros before after[READY PRIOR]FRAME;split.
  - eapply gateway_bytes_ready_closed;[exact READY|].
    eapply Mem.unchanged_on_implies;[exact FRAME|intros other position INSIDE VALID;left;exact INSIDE].
  - eapply Mem.unchanged_on_trans;[exact PRIOR|].
    eapply Mem.unchanged_on_implies;[exact FRAME|intros other position INSIDE VALID;right;exact INSIDE].
Qed.

Definition gateway_disjoint_readonly block offset width(read_only:Values.block->Z->Prop) : Prop :=
  forall other position,read_only other position -> ~gateway_byte_region block offset width other position.

Lemma gateway_extended_store block offset width read_only initial written memory value :
  gateway_disjoint_readonly block offset width read_only ->
  gateway_extended_ready block offset width read_only initial written memory ->
  (length written<width)%nat -> Int.zero_ext 8 value=value ->
  exists after,Mem.store Mint8unsigned memory block(offset+Z.of_nat(length written))(Vint value)=Some after /\
    gateway_extended_ready block offset width read_only initial(written++[value])after.
Proof.
  intros DISJOINT[READY PRIOR]SPACE BYTE.
  destruct(gateway_bytes_store block offset width written memory value READY SPACE BYTE)as[after[STORE NEXT]].
  exists after;split;[exact STORE|];split;[exact NEXT|].
  eapply Mem.unchanged_on_trans;[exact PRIOR|].
  eapply Mem.store_unchanged_on;[exact STORE|].
  intros position INSIDE READONLY;apply(DISJOINT block position READONLY);split;[reflexivity|].
  cbn[size_chunk]in INSIDE;apply Nat2Z.inj_lt in SPACE;lia.
Qed.

Definition gateway_readonly_family block offset width read_only initial
    (disjoint:gateway_disjoint_readonly block offset width read_only) :
    gateway_write_family block offset width
      (gateway_join_region(gateway_byte_region block offset width)read_only) := {|
  gateway_family_ready:=gateway_extended_ready block offset width read_only initial;
  gateway_family_closed:=gateway_extended_closed block offset width read_only initial;
  gateway_family_store:=fun written memory value=>
    gateway_extended_store block offset width read_only initial written memory value disjoint
|}.

Lemma gateway_extended_initial block offset width read_only memory :
  Mem.range_perm memory block offset(offset+Z.of_nat width)Cur Writable ->
  gateway_extended_ready block offset width read_only memory [] memory.
Proof. intro OWN;split;[apply gateway_bytes_initial;exact OWN|apply Mem.unchanged_on_refl]. Qed.
