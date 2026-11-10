(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Compare the actual native parser's shared source-word framing. *)
From Stdlib Require Import List Arith Lia.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewayImport GatewayWordData GatewayValue GatewayScalarEncoding
  GatewayCanonicalBytes GatewayCanonicalSubject GatewayPrefixReader GatewayResponseHeaderEncoding.
Import ListNotations.
Local Close Scope lean_scope.
Local Open Scope nat_scope.

Local Abbreviation Subject := LeanCage_Host_GatewayResponseCode_Subject.
Local Abbreviation SValue := LeanCage_Host_GatewayResponseCode_Subject_value.
Local Abbreviation SValues := LeanCage_Host_GatewayResponseCode_Subject_values.
Local Abbreviation SFields := LeanCage_Host_GatewayResponseCode_Subject_fields.
Local Abbreviation VNull := LeanCage_Host_GatewayResponseCode_Value_null.
Local Abbreviation VBool := LeanCage_Host_GatewayResponseCode_Value_boolean.
Local Abbreviation VScalar := LeanCage_Host_GatewayResponseCode_Value_scalar.
Local Abbreviation VArray := LeanCage_Host_GatewayResponseCode_Value_array.
Local Abbreviation VObject := LeanCage_Host_GatewayResponseCode_Value_object.
Local Abbreviation SourceEncoded := LeanCage_Host_GatewayResponseWords_SourceEncoded.

Lemma gateway_prefix_scalar_actual tag width payload sizeBytes tail :
  LeanCage_Host_GatewayWords_Encoding (Nat_of_nat width) (List_length_inst1 _ payload) sizeBytes ->
  gateway_prefix_scalar tag width (gateway_plain_nats sizeBytes ++ (gateway_plain_nats payload ++ tail)) =
    Some (SValue (VScalar (Nat_of_nat tag) payload), tail).
Proof.
  intro SIZE.
  pose proof (gateway_prefix_word_actual _ _ _ (gateway_plain_nats payload ++ tail) SIZE) as WORD.
  rewrite nat2Natid, gateway_plain_nats_length in WORD.
  unfold gateway_prefix_scalar; rewrite WORD.
  rewrite firstn_app, firstn_all, Nat.sub_diag, skipn_app, skipn_all, Nat.sub_diag.
  cbn; rewrite app_nil_r, gateway_imported_plain_nats; reflexivity.
Qed.

Lemma gateway_prefix_read_more fuel more mode bytes subject tail :
  fuel <= more -> Lean.eq (gateway_prefix_read fuel mode bytes) (Some (subject, tail)) ->
  gateway_prefix_read more mode bytes = Some (subject, tail).
Proof.
  intros BOUND SAME; eapply gateway_prefix_read_monotone;
    [exact BOUND |eapply gateway_header_imported_equality; exact SAME].
Qed.

Theorem gateway_source_encoding_readable subject bytes :
  SourceEncoded subject bytes -> gateway_canonical_subject subject ->
  gateway_prefix_readable subject (gateway_plain_nats bytes).
Proof.
  intro SOURCE; induction SOURCE as
    [tagBytes TAG | flag tagBytes TAG | tag payload tagBytes sizeBytes TAG SMALL SIZE |
     values tagBytes sizeBytes bytes TAG SIZE BODY IH |
     fields tagBytes sizeBytes bytes TAG SIZE BODY IH |
     | value values bytes rest FIRST firstIH REMAINING restIH |
     | key value fields keyBytes valueBytes rest KEY keyIH VALUE valueIH REMAINING restIH]; intro CANONICAL.
  - apply gateway_prefix_readable_intro with (fuel := 1); intro tail.
    rewrite (gateway_plain_tag_encoding _ _ TAG).
    cbn [gateway_prefix_read gateway_subject_mode gateway_prefix_step]; constructor.
  - apply gateway_prefix_readable_intro with (fuel := 1); intro tail.
    rewrite (gateway_plain_tag_encoding _ _ TAG).
    destruct flag; cbn [gateway_prefix_read gateway_subject_mode gateway_prefix_step]; constructor.
  - inversion CANONICAL; subst.
    match goal with VALID : gateway_canonical_scalar_tag _ |- _ =>
      unfold gateway_canonical_scalar_tag in VALID; cbn [In] in VALID;
      repeat destruct VALID as [VALID | VALID]; try contradiction;
      apply (f_equal Nat_of_nat) in VALID; rewrite Nat2natid in VALID; subst tag
    end.
    all: apply gateway_prefix_readable_intro with (fuel := 1); intro tail.
    all: rewrite !gateway_plain_nats_append, (gateway_plain_tag_encoding _ _ TAG), nat2Natid;
      repeat rewrite <- app_assoc; cbn [app].
    all: cbv beta iota delta [gateway_prefix_read gateway_subject_mode gateway_prefix_step].
    all: rewrite gateway_prefix_scalar_actual by exact SIZE; constructor.
  - inversion CANONICAL; subst.
    match goal with CHILD : gateway_canonical_subject (SValues _) |- _ =>
      destruct (IH CHILD) as [fuel READ]
    end.
    apply gateway_prefix_readable_intro with (fuel := S fuel); intro tail.
    rewrite !gateway_plain_nats_append, (gateway_plain_tag_encoding _ _ TAG).
    try rewrite nat2Natid; repeat rewrite <- app_assoc; cbn [app].
    change (Lean.eq
      (match gateway_prefix_read fuel
        (gateway_prefix_values (@Datatypes.fst nat (list nat) (gateway_prefix_word 4
          (gateway_plain_nats sizeBytes ++ (gateway_plain_nats bytes ++ tail)))))
        (@Datatypes.snd nat (list nat) (gateway_prefix_word 4 (gateway_plain_nats sizeBytes ++ (gateway_plain_nats bytes ++ tail)))) with
       | Some (SValues found, suffix) => Some (SValue (VArray found), suffix)
       | _ => None end) (Some (SValue (VArray values), tail))).
    rewrite (gateway_prefix_word_actual _ _ _ _ SIZE).
    cbn [Datatypes.fst Datatypes.snd].
    cbn [gateway_subject_mode] in READ.
    rewrite (gateway_header_imported_equality _ _ _ (READ tail)); constructor.
  - inversion CANONICAL; subst.
    match goal with CHILD : gateway_canonical_subject (SFields _) |- _ =>
      destruct (IH CHILD) as [fuel READ]
    end.
    apply gateway_prefix_readable_intro with (fuel := S fuel); intro tail.
    rewrite !gateway_plain_nats_append, (gateway_plain_tag_encoding _ _ TAG).
    try rewrite nat2Natid; repeat rewrite <- app_assoc; cbn [app].
    change (Lean.eq
      (match gateway_prefix_read fuel
        (gateway_prefix_fields (@Datatypes.fst nat (list nat) (gateway_prefix_word 4
          (gateway_plain_nats sizeBytes ++ (gateway_plain_nats bytes ++ tail)))))
        (@Datatypes.snd nat (list nat) (gateway_prefix_word 4 (gateway_plain_nats sizeBytes ++ (gateway_plain_nats bytes ++ tail)))) with
       | Some (SFields found, suffix) => Some (SValue (VObject found), suffix)
       | _ => None end) (Some (SValue (VObject fields), tail))).
    rewrite (gateway_prefix_word_actual _ _ _ _ SIZE).
    cbn [Datatypes.fst Datatypes.snd].
    cbn [gateway_subject_mode] in READ.
    rewrite (gateway_header_imported_equality _ _ _ (READ tail)); constructor.
  - apply gateway_prefix_readable_intro with (fuel := 1); intro tail; constructor.
  - inversion CANONICAL; subst.
    match goal with HEAD : gateway_canonical_subject (SValue _), TAIL : gateway_canonical_subject (SValues _) |- _ =>
      destruct (firstIH HEAD) as [left LEFT]; destruct (restIH TAIL) as [right RIGHT]
    end.
    apply gateway_prefix_readable_intro with (fuel := S (Nat.max left right)); intro tail.
    rewrite gateway_plain_nats_append, <- app_assoc.
    change (Lean.eq (gateway_prefix_step (gateway_prefix_read (Nat.max left right))
      (gateway_prefix_values (S (nat_of_Nat (List_length_inst1 _ values))))
      (gateway_plain_nats bytes ++ (gateway_plain_nats rest ++ tail)))
      (Some (SValues (List_cons_inst1 _ value values), tail))).
    unfold gateway_prefix_step.
    cbn [gateway_subject_mode] in LEFT, RIGHT.
    rewrite (gateway_prefix_read_more left (Nat.max left right) _ _ _ _ (Nat.le_max_l _ _) (LEFT _)).
    rewrite (gateway_prefix_read_more right (Nat.max left right) _ _ _ _ (Nat.le_max_r _ _) (RIGHT _)).
    constructor.
  - apply gateway_prefix_readable_intro with (fuel := 1); intro tail; constructor.
  - inversion CANONICAL; subst.
    match goal with
      KEY_CANONICAL : gateway_canonical_subject (SValue key),
      VALUE_CANONICAL : gateway_canonical_subject (SValue value),
      TAIL : gateway_canonical_subject (SFields _) |- _ =>
      destruct (keyIH KEY_CANONICAL) as [left LEFT];
      destruct (valueIH VALUE_CANONICAL) as [middle MIDDLE];
      destruct (restIH TAIL) as [right RIGHT]
    end.
    set (fuel := Nat.max left (Nat.max middle right)).
    apply gateway_prefix_readable_intro with (fuel := S fuel); intro tail.
    rewrite !gateway_plain_nats_append, <- !app_assoc.
    change (Lean.eq (gateway_prefix_step (gateway_prefix_read fuel)
      (gateway_prefix_fields (S (nat_of_Nat (List_length_inst1 _ fields))))
      (gateway_plain_nats keyBytes ++ (gateway_plain_nats valueBytes ++ (gateway_plain_nats rest ++ tail))))
      (Some (SFields (List_cons_inst1 _ (Prod_mk_inst3 _ _ key value) fields), tail))).
    unfold gateway_prefix_step.
    cbn [gateway_subject_mode] in LEFT, MIDDLE, RIGHT.
    rewrite (gateway_prefix_read_more left fuel _ _ _ _ ltac:(unfold fuel; lia) (LEFT _)).
    rewrite (gateway_prefix_read_more middle fuel _ _ _ _ ltac:(unfold fuel; lia) (MIDDLE _)).
    rewrite (gateway_prefix_read_more right fuel _ _ _ _ ltac:(unfold fuel; lia) (RIGHT _)).
    constructor.
Qed.

Theorem gateway_source_prefix_strict first second left right leftTail rightTail :
  SourceEncoded first left -> SourceEncoded second right ->
  gateway_canonical_subject first -> gateway_canonical_subject second ->
  gateway_subject_mode first = gateway_subject_mode second ->
  gateway_plain_nats left ++ leftTail = gateway_plain_nats right ++ rightTail ->
  Lean.And (Lean.eq first second) (Lean.eq leftTail rightTail).
Proof.
  intros LEFT_SOURCE RIGHT_SOURCE LEFT_CANONICAL RIGHT_CANONICAL MODE BYTES.
  destruct (gateway_source_encoding_readable _ _ LEFT_SOURCE LEFT_CANONICAL) as [leftFuel LEFT].
  destruct (gateway_source_encoding_readable _ _ RIGHT_SOURCE RIGHT_CANONICAL) as [rightFuel RIGHT].
  pose proof (gateway_prefix_read_more leftFuel (Nat.max leftFuel rightFuel) _ _ _ _
    (Nat.le_max_l _ _) (LEFT leftTail)) as LEFT_READ.
  pose proof (gateway_prefix_read_more rightFuel (Nat.max leftFuel rightFuel) _ _ _ _
    (Nat.le_max_r _ _) (RIGHT rightTail)) as RIGHT_READ.
  rewrite MODE, BYTES, RIGHT_READ in LEFT_READ.
  inversion LEFT_READ; subst; constructor; constructor.
Qed.

Theorem gateway_source_prefix_unique first second left right leftTail rightTail :
  SourceEncoded first left -> SourceEncoded second right ->
  gateway_canonical_subject first -> gateway_canonical_subject second ->
  gateway_subject_mode first = gateway_subject_mode second ->
  gateway_plain_nats left ++ leftTail = gateway_plain_nats right ++ rightTail ->
  first = second /\ leftTail = rightTail.
Proof.
  intros LEFT RIGHT LEFT_CANONICAL RIGHT_CANONICAL MODE BYTES.
  destruct (gateway_source_prefix_strict _ _ _ _ _ _ LEFT RIGHT LEFT_CANONICAL RIGHT_CANONICAL MODE BYTES)
    as [SUBJECT TAIL].
  split; eapply gateway_header_imported_equality; eassumption.
Qed.
