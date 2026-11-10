(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual phase transitions retain sign/indices and select a constructor only after complete syntax. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayJsonNumberSource GatewayJsonNumberSourceBytes
  GatewayJsonNumberSourceTests GatewayJsonNumberSourceScans GatewayJsonNumberSourceFraction GatewayJsonNumberSourceExponent
  GatewayNumberConstruction GatewaySourceSegments GatewaySourceSegmentAutomation GatewayFramedRuntime GatewaySourceCuts GatewayFailurePaths.
Import ListNotations.
Open Scope Z_scope.

Definition json_lexical_fraction_cont := Kseq json_number_after_fraction Kstop.
Definition json_lexical_exponent_cont := Kseq json_number_after_exponent Kstop.
Definition json_lexical_long_cont := Kseq gateway_number_zero_assign (Kseq gateway_number_after_zero Kstop).
Definition json_lexical_decode_cont := Kseq gateway_number_decode_assign
  (Kseq gateway_number_after_decode (Kseq json_number_integer_construction Kstop)).
Definition json_lexical_constructor integer count parameters memory :=
  if Z.eqb integer count then State f_host_json_number json_number_long_call json_lexical_long_cont empty_env parameters memory
  else State f_host_json_number json_number_decode_call json_lexical_decode_cont empty_env parameters memory.

Lemma json_number_segment_failure_when {World Event} (backend : gateway_backend World Event) ge
    property source target :
  gateway_source_segment backend ge property source target property ->
  gateway_failure_when backend ge property target -> gateway_failure_when backend ge property source.
Proof.
  intros SEGMENT FAILURE before world events value after next GOOD RUN.
  destruct (gateway_source_segment_cut backend ge _ _ _ _ SEGMENT before world events value after next GOOD RUN)
    as (prefix & suffix & middle & current & EVENTS & QUIET & PREFIX & READY & SUFFIX).
  exact (FAILURE middle current suffix value after next READY SUFFIX).
Qed.

Theorem gateway_json_number_to_fraction {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) parameters index memory :
  gateway_ambient_closed backend property -> parameters ! _index = Some (Vlong (Int64.repr index)) ->
  gateway_source_segment backend ge property
    (State f_host_json_number Sskip (Kseq json_number_after_integer Kstop) empty_env parameters memory)
    (State f_host_json_number json_number_fraction json_lexical_fraction_cont empty_env
      (PTree.set _integer_end (Vlong (Int64.repr index)) parameters) memory) property.
Proof.
  intros CLOSED POSITION; unfold json_lexical_fraction_cont.
  gateway_segment_dynamic CLOSED ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
Qed.

Theorem gateway_json_number_to_exponent {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) parameters memory :
  gateway_ambient_closed backend property ->
  gateway_source_segment backend ge property
    (State f_host_json_number Sskip json_lexical_fraction_cont empty_env parameters memory)
    (State f_host_json_number json_number_exponent json_lexical_exponent_cont empty_env parameters memory) property.
Proof.
  intro CLOSED; unfold json_lexical_fraction_cont, json_lexical_exponent_cont.
  gateway_segment_dynamic CLOSED ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
Qed.

Theorem gateway_json_number_constructor_select {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) parameters finish integer count memory :
  gateway_ambient_closed backend property -> 0 <= finish <= 65536 -> 0 <= integer <= 65536 -> 0 <= count <= 65536 ->
  parameters ! _index = Some (Vlong (Int64.repr finish)) ->
  parameters ! _integer_end = Some (Vlong (Int64.repr integer)) ->
  parameters ! _size = Some (Vlong (Int64.repr count)) ->
  gateway_source_segment backend ge property
    (State f_host_json_number Sskip json_lexical_exponent_cont empty_env parameters memory)
    (if Z.eqb finish count then json_lexical_constructor integer count parameters memory
     else State f_host_json_number (Sgoto _invalid) (Kseq json_number_after_complete Kstop) empty_env parameters memory) property.
Proof.
  intros CLOSED FINISH INTEGER COUNT POSITION END SIZE.
  destruct (Z.eqb finish count) eqn:COMPLETE; [destruct (Z.eqb integer count) eqn:KIND |];
    unfold json_lexical_constructor; rewrite ?KIND;
    unfold json_lexical_exponent_cont, json_lexical_long_cont, json_lexical_decode_cont;
    gateway_segment_dynamic CLOSED ltac:(fun _ => fail)
      ltac:(fun _ => json_number_source_reduce).
Qed.
