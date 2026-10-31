(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.reporting: Exact byte results for sequential reports and failed first reports. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers Values.
Require Import FrameRecord SenderSelectors SenderWriteReturn SenderShortReport.
Import ListNotations.
Lemma output_result_prefix : forall expected sent value,
  sender_output_result expected sent value -> exists rest,expected=sent++rest.
Proof.
  intros expected sent value [[VALUE SENT]|[VALUE [NE PREFIX]]];[subst;exists [];rewrite app_nil_r;reflexivity|exact PREFIX].
Qed.
Lemma output_append_success : forall first expected sent value,
  sender_output_result expected sent value -> sender_output_result (first++expected) (first++sent) value.
Proof.
  intros first expected sent value [[VALUE SENT]|[VALUE [NE [rest PREFIX]]]].
  - left;subst;auto.
  - right;split;[exact VALUE|]. split.
    + intro SAME;apply NE;eapply app_inv_head;exact SAME.
    + exists rest;rewrite PREFIX,app_assoc;reflexivity.
Qed.
Lemma output_failed_first : forall first remaining sent,
  sent<>first -> (exists rest,first=sent++rest) ->
  sender_output_result (first++remaining) sent (Vint Int.mone).
Proof.
  intros first remaining sent NE [rest PREFIX];right;split;[reflexivity|]. split.
  - intro SAME;assert (length rest>0)%nat.
    { destruct rest;[rewrite app_nil_r in PREFIX;congruence|cbn;lia]. }
    apply (f_equal (@length Byte.int)) in SAME;rewrite PREFIX,!app_length in SAME;lia.
  - exists (rest++remaining);rewrite PREFIX,app_assoc;reflexivity.
Qed.
Lemma duplicate_final_report : forall fd r mode_bytes bytes,
  report_selected fd r mode_bytes duplicate_frame=true -> selected_final_report fd r mode_bytes bytes=bytes.
Proof.
  intros fd r mode_bytes bytes DUP;unfold selected_final_report.
  destruct (report_selected fd r mode_bytes short_frame) eqn:SHORT.
  - pose proof (report_selection_unique _ _ _ _ _ DUP SHORT);discriminate.
  - destruct (report_selected fd r mode_bytes drop_frame) eqn:DROP;[|reflexivity].
    pose proof (report_selection_unique _ _ _ _ _ DUP DROP);discriminate.
Qed.
