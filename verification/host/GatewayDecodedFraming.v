(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual call72 parser result consumes typed writer-prefix identity. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Values Memory Clight.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewayImport GatewayPython GatewayObjects GatewayObjectDiscipline
  GatewayValue GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceDecoded GatewayReferenceParseResult
  GatewayContainerEncoding GatewayValueContext GatewayPathEvents GatewayStreamInterface GatewayWordData GatewayWordReceipt
  GatewayCanonicalBytes GatewayCanonicalSubject GatewaySourceFraming.
Local Close Scope lean_scope.

Theorem gateway_source_value_complete_prefix writer parsed writerBytes parsedBytes pending :
  LeanCage_Host_GatewayResponseWords_SourceEncoded
    (LeanCage_Host_GatewayResponseCode_Subject_value writer) writerBytes ->
  LeanCage_Host_GatewayResponseWords_SourceEncoded
    (LeanCage_Host_GatewayResponseCode_Subject_value parsed) parsedBytes ->
  gateway_canonical_subject (LeanCage_Host_GatewayResponseCode_Subject_value writer) ->
  gateway_canonical_subject (LeanCage_Host_GatewayResponseCode_Subject_value parsed) ->
  gateway_plain_nats writerBytes = gateway_plain_nats parsedBytes ++ pending ->
  writer = parsed /\ pending = nil /\ writerBytes = parsedBytes.
Proof.
  intros WRITER PARSED WRITER_CANONICAL PARSED_CANONICAL PREFIX.
  assert (BOTH : gateway_plain_nats writerBytes ++ nil = gateway_plain_nats parsedBytes ++ pending)
    by (rewrite app_nil_r; exact PREFIX).
  destruct (gateway_source_prefix_unique _ _ _ _ nil pending WRITER PARSED
    WRITER_CANONICAL PARSED_CANONICAL ltac:(reflexivity) BOTH) as [VALUE TAIL].
  inversion VALUE; subst parsed; split; [reflexivity |]. split; [symmetry; exact TAIL |].
  rewrite <- TAIL, app_nil_r in PREFIX.
  apply (f_equal gateway_imported_nats) in PREFIX; rewrite !gateway_imported_plain_nats in PREFIX; exact PREFIX.
Qed.

(* The source-connected parser and EOF consumers supply this result predicate;
   its private graph, source ticket, descriptor and original ownership are kept. *)
Theorem gateway_reference_decoded_writer {World Event}
    (python : World -> python_world) (objects : World -> gateway_object_heap) decimal_float detached
    (io : Event -> option gateway_native_io) stable ge context ledger held
    stream offset initial readonly original events pointer after next writer writerBytes pending :
  gateway_reference_parse_result python objects decimal_float detached io stable ge context ledger held
    stream offset initial readonly original events pointer after next ->
  LeanCage_Host_GatewayResponseWords_SourceEncoded
    (LeanCage_Host_GatewayResponseCode_Subject_value writer) writerBytes ->
  gateway_canonical_subject (LeanCage_Host_GatewayResponseCode_Subject_value writer) ->
  gateway_plain_nats writerBytes = gateway_byte_naturals
    (gateway_received_bytes io (stream_descriptor initial) events) ++ pending ->
  pending = nil /\ exists final finalStream ticket,
    gateway_reference_decoded python objects decimal_float ge context ledger held writer ticket pointer final after next /\
    gateway_value_context (fun current candidate => gateway_native_private (python current) candidate) stable
      (gateway_python_discipline python objects detached) stream offset finalStream readonly original after next /\
    (forall candidate position, readonly candidate position -> gateway_native_private (python next) candidate) /\
    stream_descriptor finalStream = stream_descriptor initial /\
    writerBytes = gateway_wire_bytes (gateway_received_bytes io (stream_descriptor initial) events) /\
    gateway_response_frame (LeanCage_Host_GatewayResponseCode_Subject_value writer)
      (gateway_received_bytes io (stream_descriptor initial) events).
Proof.
  intros (final & finalStream & wire & ticket & DECODED & CONTEXT & NATIVE & DESCRIPTOR & FRAMED)
    WRITER CANONICAL PREFIX.
  pose proof (gateway_decoded_value _ _ _ _ _ _ _ _ _ _ _ _ _ DECODED) as HEAP.
  pose proof (gateway_heap_value_canonical _ _ _ _ HEAP) as PARSED_CANONICAL.
  assert (SOURCE : LeanCage_Host_GatewayResponseWords_SourceEncoded
    (LeanCage_Host_GatewayResponseCode_Subject_value wire)
    (gateway_wire_bytes (gateway_received_bytes io (stream_descriptor initial) events))).
  { apply gateway_response_frame_shared; exact FRAMED. }
  assert (SAME : gateway_plain_nats writerBytes = gateway_plain_nats
    (gateway_wire_bytes (gateway_received_bytes io (stream_descriptor initial) events)) ++ pending).
  { unfold gateway_wire_bytes; rewrite gateway_plain_imported_nats; exact PREFIX. }
  destruct (gateway_source_value_complete_prefix _ _ _ _ _ WRITER SOURCE CANONICAL PARSED_CANONICAL SAME)
    as [VALUE [TAIL BYTES]]; subst wire.
  split; [exact TAIL |]. exists final, finalStream, ticket.
  split; [exact DECODED |]. split; [exact CONTEXT |]. split; [exact NATIVE |].
  split; [exact DESCRIPTOR |]. split; assumption.
Qed.
