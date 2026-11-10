(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Framing comparisons retain the unchanged strict shared word data. *)
From Stdlib Require Import List Arith Lia.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewayImport GatewayWordData GatewayResponseHeaderEncoding GatewayScalarEncoding.
Import ListNotations.
Local Close Scope lean_scope.
Local Open Scope nat_scope.

Fixpoint gateway_plain_nats (bytes : List_inst1 Nat) : list nat :=
  match bytes with
  | List_nil_inst1 _ => []
  | List_cons_inst1 _ byte rest => nat_of_Nat byte :: gateway_plain_nats rest
  end.

Lemma gateway_plain_imported_nats bytes : gateway_plain_nats (gateway_imported_nats bytes) = bytes.
Proof. induction bytes; cbn; rewrite ?nat2Natid, ?IHbytes; reflexivity. Qed.
Lemma gateway_imported_plain_nats bytes : gateway_imported_nats (gateway_plain_nats bytes) = bytes.
Proof. induction bytes; cbn; rewrite ?Nat2natid, ?IHbytes; reflexivity. Qed.
Lemma gateway_plain_nats_length bytes :
  nat_of_Nat (List_length_inst1 Nat bytes) = length (gateway_plain_nats bytes).
Proof.
  induction bytes as [|value rest IH]; [reflexivity |].
  change (S (nat_of_Nat (List_length_inst1 Nat rest)) = S (length (gateway_plain_nats rest))).
  rewrite IH; reflexivity.
Qed.
Lemma gateway_plain_nats_append first second :
  gateway_plain_nats (HAppend_hAppend_inst7 (List_inst1 Nat) (List_inst1 Nat) (List_inst1 Nat)
    (instHAppendOfAppend_inst1 (List_inst1 Nat) (List_instAppend_inst1 Nat)) first second) =
  gateway_plain_nats first ++ gateway_plain_nats second.
Proof.
  pose proof (gateway_imported_nats_append (gateway_plain_nats first) (gateway_plain_nats second)) as SAME.
  rewrite !gateway_imported_plain_nats in SAME.
  apply (f_equal gateway_plain_nats) in SAME; rewrite gateway_plain_imported_nats in SAME; symmetry; exact SAME.
Qed.

Theorem gateway_plain_word_encoding width value bytes :
  LeanCage_Host_GatewayWords_Encoding width value bytes ->
  length (gateway_plain_nats bytes) = nat_of_Nat width /\
  gateway_natural_decode (gateway_plain_nats bytes) = nat_of_Nat value.
Proof.
  intros [SIZE [_ DECODE]].
  pose proof (gateway_header_imported_equality _ _ _ SIZE) as LENGTH.
  pose proof (gateway_header_imported_equality _ _ _ DECODE) as VALUE.
  split.
  - rewrite <- gateway_plain_nats_length, LENGTH; reflexivity.
  - rewrite <- gateway_shared_decode, gateway_imported_plain_nats, VALUE; reflexivity.
Qed.

Theorem gateway_plain_tag_encoding value bytes :
  LeanCage_Host_GatewayWords_Encoding (Nat_of_nat 1) value bytes ->
  gateway_plain_nats bytes = [nat_of_Nat value].
Proof.
  intro WORD; destruct (gateway_plain_word_encoding _ _ _ WORD) as (LENGTH & VALUE).
  change (length (gateway_plain_nats bytes) = 1) in LENGTH.
  destruct (gateway_plain_nats bytes) as [|first rest]; [discriminate |].
  destruct rest; [|discriminate].
  change (first + 256 * 0 = nat_of_Nat value) in VALUE.
  f_equal; lia.
Qed.

Lemma gateway_equal_length_prefix {A} (first second left_tail right_tail : list A) :
  length first = length second -> first ++ left_tail = second ++ right_tail ->
  first = second /\ left_tail = right_tail.
Proof.
  revert second; induction first as [|item rest IH]; intros [|other tail] LENGTH SAME;
    cbn in LENGTH, SAME; try discriminate; [auto |].
  inversion SAME; subst other.
  destruct (IH tail ltac:(lia) ltac:(assumption)) as (PREFIX & SUFFIX); subst tail; auto.
Qed.
