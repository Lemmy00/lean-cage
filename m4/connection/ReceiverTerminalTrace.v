(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.reads: Close errors, waits and loss compose with the exact terminal classifier. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Clight.
Require Import Slice Machine StoreSteps WriteAll CallPaths SourcePaths SourceGuarantees ProcessEffects
  ResultLayout ResultSafety SenderReportMemory ReceiverSource ReceiverReadSource
  ReceiverReadMemory ReceiverPreparation ReceiverChoice ReceiverMemory
  ReceiverConstruction ReceiverClassification ReceiverInput ReceiverCloseMemory
  ReceiverCloseSource CloseControl ReceiverTrace.
Import ListNotations.
Open Scope Z_scope.
Theorem receiver_terminal_quiet : forall cell base b bytes fd bad entered done status le m output ofs run uid,
  receiver_input cell base output ofs run uid -> receiver_live_memory cell base b output ofs fd m ->
  receiver_buffer cell b m bytes ->
  le!__res=Some(Vptr output(Ptrofs.repr ofs)) ->
  le!_bad=Some(Vint bad) -> le!_entered=Some(Vint entered) ->
  le!_leader_done=Some(Vint done) -> le!_leader_status=Some(Vint status) ->
  le!_used=Some(Vlong(Int64.repr(Z.of_nat(length bytes)))) ->
  receiver_quiet result_ge cell
    (receiver_closed_state b le Kstop m).
Proof.
  intros cell base b bytes fd bad entered done status le m output ofs run uid
    INPUT LIVE BUFFER OUT BAD ENTERED DONE STATUS USED.
  pose proof(proj1(proj2 INPUT))as TLS.
  pose proof LIVE as[OLD[SLOTS[DEST FD]]].
  assert(VALID : Mem.valid_block base output).
  { eapply Mem.perm_valid_block with(ofs:=ofs);apply(proj2(proj2(proj2(proj1 INPUT))));lia. }
  assert(PM : receiver_preserved cell base output ofs m)by(apply receiver_sender_preserved;exact OLD).
  destruct(receiver_to_close b le Kstop m fd FD)as[count PATH].
  eapply receiver_quiet_path.
  - exact PATH.
  - apply receiver_close_quiet.
    intros reply after EFFECT.
    pose proof(receiver_live_close _ _ _ _ _ _ _ _ _ TLS LIVE EFFECT)as LIVE'.
    pose proof(receiver_buffer_close _ _ _ _ _ _ BUFFER EFFECT)as BUFFER'.
    assert(PA : receiver_preserved cell base output ofs after).
    { apply receiver_sender_preserved;exact(proj1 LIVE'). }
    apply receiver_source_quiet with(P:=receiver_preserved cell base output ofs)
      (R:=receiver_choice_result output ofs(receiver_select bytes bad entered done status)uid run b);
      eapply source_returns_path.
    + eapply store_path_consequence;[apply receiver_close_ignored|intros last SAME;change(last=after)in SAME;subst last;exact PA].
    + eapply receiver_classification_source.
      * exact PA.
      * exact(proj1(proj2 LIVE')).
      * eapply receiver_live_result_input;[exact INPUT|exact LIVE'].
      * exact VALID.
      * exact BUFFER'.
      * WriteAll.lookup.
      * WriteAll.lookup.
      * WriteAll.lookup.
      * WriteAll.lookup.
      * WriteAll.lookup.
      * WriteAll.lookup.
Qed.
