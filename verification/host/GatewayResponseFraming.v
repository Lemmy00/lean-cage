(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A complete accepted response identifies this unfinished source writer. *)
From Stdlib Require Import List Arith Lia.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewayImport GatewayWordData GatewayValue GatewayScalarEncoding
  GatewayCanonicalBytes GatewayCanonicalSubject GatewayPrefixReader GatewaySourceFraming GatewayResponseHeaderEncoding.
Import ListNotations.
Local Close Scope lean_scope.
Local Open Scope nat_scope.

Local Abbreviation SValue := LeanCage_Host_GatewayResponseCode_Subject_value.
Local Abbreviation SourceResponse := LeanCage_Host_GatewayResponseWords_SourceResponseEncoding.

Definition gateway_response_prefix_read fuel bytes :=
  let '(status, rest) := gateway_prefix_word 4 (skipn 8 bytes) in
  (status, gateway_prefix_read fuel gateway_prefix_value (skipn 8 (skipn 4 rest))).

Local Lemma gateway_response_skip {A} (prefix tail : list A) count :
  length prefix = count -> skipn count (prefix ++ tail) = tail.
Proof.
  intro SIZE; rewrite <- SIZE, skipn_app, skipn_all, Nat.sub_diag; reflexivity.
Qed.

Inductive gateway_response_readable status value bytes : SProp :=
| gateway_response_readable_intro : forall fuel,
    (forall more tail, fuel <= more ->
      Lean.eq (gateway_response_prefix_read more (bytes ++ tail))
        (nat_of_Nat status, Some (SValue value, tail))) ->
    gateway_response_readable status value bytes.

Theorem gateway_source_response_readable status value bytes :
  SourceResponse status value bytes -> gateway_canonical_subject (SValue value) ->
  gateway_response_readable status value (gateway_plain_nats bytes).
Proof.
  intros [payload [statusBytes [reservedBytes [sizeBytes [PAYLOAD [STATUS [RESERVED [SIZE BYTES]]]]]]]] CANONICAL.
  destruct (gateway_source_encoding_readable _ _ PAYLOAD CANONICAL) as [fuel READ].
  pose proof (gateway_header_imported_equality _ _ _ BYTES) as SAME.
  destruct (gateway_plain_word_encoding _ _ _ RESERVED) as [RESERVED_LENGTH RESERVED_VALUE].
  destruct (gateway_plain_word_encoding _ _ _ SIZE) as [SIZE_LENGTH SIZE_VALUE].
  change (length (gateway_plain_nats reservedBytes) = 4) in RESERVED_LENGTH.
  change (length (gateway_plain_nats sizeBytes) = 8) in SIZE_LENGTH.
  apply gateway_response_readable_intro with (fuel := fuel); intros more tail BOUND.
  rewrite SAME, !gateway_plain_nats_append.
  repeat rewrite <- app_assoc.
  unfold gateway_response_prefix_read.
  change (Lean.eq
    (let '(actualStatus, rest) := gateway_prefix_word 4
        (gateway_plain_nats statusBytes ++ (gateway_plain_nats reservedBytes ++
          (gateway_plain_nats sizeBytes ++ (gateway_plain_nats payload ++ tail)))) in
      (actualStatus, gateway_prefix_read more gateway_prefix_value (skipn 8 (skipn 4 rest))))
    (nat_of_Nat status, Some (SValue value, tail))).
  rewrite (gateway_prefix_word_actual _ _ _ _ STATUS).
  cbv beta iota.
  rewrite (gateway_response_skip _ _ _ RESERVED_LENGTH).
  rewrite (gateway_response_skip _ _ _ SIZE_LENGTH).
  cbn [gateway_subject_mode] in READ.
  rewrite (gateway_prefix_read_more _ _ _ _ _ _ BOUND (READ tail)); constructor.
Qed.

Theorem gateway_response_prefix_strict leftStatus rightStatus leftValue rightValue
    left right leftTail rightTail :
  SourceResponse leftStatus leftValue left -> SourceResponse rightStatus rightValue right ->
  gateway_canonical_subject (SValue leftValue) -> gateway_canonical_subject (SValue rightValue) ->
  gateway_plain_nats left ++ leftTail = gateway_plain_nats right ++ rightTail ->
  Lean.And (Lean.eq leftStatus rightStatus)
    (Lean.And (Lean.eq leftValue rightValue) (Lean.eq leftTail rightTail)).
Proof.
  intros LEFT_SOURCE RIGHT_SOURCE LEFT_CANONICAL RIGHT_CANONICAL BYTES.
  destruct (gateway_source_response_readable _ _ _ LEFT_SOURCE LEFT_CANONICAL) as [leftFuel LEFT].
  destruct (gateway_source_response_readable _ _ _ RIGHT_SOURCE RIGHT_CANONICAL) as [rightFuel RIGHT].
  pose proof (gateway_header_imported_equality _ _ _
    (LEFT (Nat.max leftFuel rightFuel) leftTail (Nat.le_max_l _ _))) as LEFT_READ.
  pose proof (gateway_header_imported_equality _ _ _
    (RIGHT (Nat.max leftFuel rightFuel) rightTail (Nat.le_max_r _ _))) as RIGHT_READ.
  rewrite BYTES, RIGHT_READ in LEFT_READ.
  injection LEFT_READ as STATUS VALUE TAIL.
  assert (STATUS_SAME : leftStatus = rightStatus).
  { apply (f_equal Nat_of_nat) in STATUS; rewrite !Nat2natid in STATUS; congruence. }
  subst; constructor; [constructor |constructor; constructor].
Qed.

Theorem gateway_response_prefix_unique leftStatus rightStatus leftValue rightValue
    left right leftTail rightTail :
  SourceResponse leftStatus leftValue left -> SourceResponse rightStatus rightValue right ->
  gateway_canonical_subject (SValue leftValue) -> gateway_canonical_subject (SValue rightValue) ->
  gateway_plain_nats left ++ leftTail = gateway_plain_nats right ++ rightTail ->
  leftStatus = rightStatus /\ leftValue = rightValue /\ leftTail = rightTail.
Proof.
  intros LEFT RIGHT LEFT_CANONICAL RIGHT_CANONICAL BYTES.
  destruct (gateway_response_prefix_strict _ _ _ _ _ _ _ _ LEFT RIGHT LEFT_CANONICAL RIGHT_CANONICAL BYTES)
    as [STATUS [VALUE TAIL]].
  split; [eapply gateway_header_imported_equality; exact STATUS |].
  split; eapply gateway_header_imported_equality; eassumption.
Qed.

Theorem gateway_response_complete_prefix writerStatus parsedStatus writerValue parsedValue
    writerBytes parsedBytes pending :
  SourceResponse writerStatus writerValue writerBytes -> SourceResponse parsedStatus parsedValue parsedBytes ->
  gateway_canonical_subject (SValue writerValue) -> gateway_canonical_subject (SValue parsedValue) ->
  gateway_plain_nats writerBytes = gateway_plain_nats parsedBytes ++ pending ->
  writerStatus = parsedStatus /\ writerValue = parsedValue /\ pending = [] /\ writerBytes = parsedBytes.
Proof.
  intros WRITER PARSED WRITER_CANONICAL PARSED_CANONICAL PREFIX.
  assert (BOTH : gateway_plain_nats writerBytes ++ [] = gateway_plain_nats parsedBytes ++ pending)
    by (rewrite app_nil_r; exact PREFIX).
  destruct (gateway_response_prefix_unique _ _ _ _ _ _ _ _ WRITER PARSED WRITER_CANONICAL PARSED_CANONICAL BOTH)
    as [STATUS [VALUE TAIL]].
  split; [exact STATUS |]. split; [exact VALUE |]. split; [symmetry; exact TAIL |].
  rewrite <- TAIL, app_nil_r in PREFIX.
  apply (f_equal gateway_imported_nats) in PREFIX; rewrite !gateway_imported_plain_nats in PREFIX; exact PREFIX.
Qed.

(* The actual heap producer removes the parser-side canonicality premise. *)
Theorem gateway_decoded_response_prefix decimal_float heap object writerStatus parsedStatus
    writerValue parsedValue writerBytes parsedBytes pending :
  SourceResponse writerStatus writerValue writerBytes -> SourceResponse parsedStatus parsedValue parsedBytes ->
  gateway_canonical_subject (SValue writerValue) -> gateway_value_heap decimal_float heap object parsedValue ->
  gateway_plain_nats writerBytes = gateway_plain_nats parsedBytes ++ pending ->
  writerStatus = parsedStatus /\ writerValue = parsedValue /\ pending = [] /\ writerBytes = parsedBytes.
Proof.
  intros WRITER PARSED WRITER_CANONICAL HEAP PREFIX.
  eapply gateway_response_complete_prefix; try eassumption.
  eapply gateway_heap_value_canonical; exact HEAP.
Qed.
