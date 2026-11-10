(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Preserve the exact strictly imported Nat-list word data. *)
From Stdlib Require Import ZArith List Lia.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewayImport.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Fixpoint gateway_imported_nats (bytes:list nat) : List_inst1 Nat :=
  match bytes with
  | [] => List_nil_inst1 Nat
  | byte::rest => List_cons_inst1 Nat(Nat_of_nat byte)(gateway_imported_nats rest)
  end.

Lemma gateway_imported_add first second :
  nat_of_Nat(Nat_add first second)=(nat_of_Nat first+nat_of_Nat second)%nat.
Proof.
  induction second as[|second IH];[cbn;lia|].
  change(S(nat_of_Nat(Nat_add first second))=nat_of_Nat first+S(nat_of_Nat second))%nat.
  rewrite IH;lia.
Qed.

Lemma gateway_imported_mul first second :
  nat_of_Nat(Nat_mul first second)=(nat_of_Nat first*nat_of_Nat second)%nat.
Proof.
  induction second as[|second IH];[change(0=nat_of_Nat first*0)%nat;lia|].
  change(nat_of_Nat(Nat_add(Nat_mul first second)first)=nat_of_Nat first*S(nat_of_Nat second))%nat.
  rewrite gateway_imported_add,IH;lia.
Qed.

Definition gateway_natural_decode (bytes:list nat) : nat :=
  fold_right(fun byte value=>byte+256*value)%nat 0%nat bytes.

Lemma gateway_shared_decode bytes :
  nat_of_Nat(LeanCage_Host_GatewayWords_decode(gateway_imported_nats bytes))=gateway_natural_decode bytes.
Proof.
  induction bytes as[|byte rest IH];[reflexivity|].
  change(nat_of_Nat(Nat_add(Nat_of_nat byte)
    (Nat_mul(Nat_of_N 256)(LeanCage_Host_GatewayWords_decode(gateway_imported_nats rest))))=
    byte+256*gateway_natural_decode rest)%nat.
  rewrite gateway_imported_add,gateway_imported_mul,nat2Natid,IH;reflexivity.
Qed.

Lemma gateway_shared_length bytes :
  List_length_inst1 Nat(gateway_imported_nats bytes)=Nat_of_nat(length bytes).
Proof. induction bytes;[reflexivity|change(Nat_succ(List_length_inst1 Nat(gateway_imported_nats bytes))=
  Nat_succ(Nat_of_nat(length bytes)));rewrite IHbytes;reflexivity]. Qed.

Lemma gateway_shared_bound bytes :
  Forall(fun byte=>(byte<256)%nat)bytes -> forall byte,
    List_Mem_inst1 Nat byte(gateway_imported_nats bytes) -> Nat_le(Nat_succ byte)(Nat_of_nat 256).
Proof.
  intro BOUNDED;induction BOUNDED as[|first rest SMALL REST IH];intros byte MEMBER.
  - inversion MEMBER.
  - inversion MEMBER;subst.
    + apply nat_le_Nat_le;change(S(nat_of_Nat(Nat_of_nat first))<=256)%nat;rewrite nat2Natid;lia.
    + apply IH;assumption.
Qed.

Theorem gateway_shared_encoding width value bytes :
  length bytes=width -> Forall(fun byte=>(byte<256)%nat)bytes -> gateway_natural_decode bytes=value ->
  LeanCage_Host_GatewayWords_Encoding(Nat_of_nat width)(Nat_of_nat value)(gateway_imported_nats bytes).
Proof.
  intros LENGTH BOUND DECODE.
  unfold LeanCage_Host_GatewayWords_Encoding;constructor.
  - rewrite gateway_shared_length,LENGTH;constructor.
  - constructor.
    + intros byte MEMBER;change(List_Mem_inst1 Nat byte(gateway_imported_nats bytes))in MEMBER.
      change(Nat_le(Nat_succ byte)(Nat_of_nat 256));eapply gateway_shared_bound;eassumption.
    + rewrite<-(Nat2natid(LeanCage_Host_GatewayWords_decode(gateway_imported_nats bytes))).
      rewrite gateway_shared_decode,DECODE;constructor.
Qed.
