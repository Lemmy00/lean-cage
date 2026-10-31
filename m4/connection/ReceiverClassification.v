(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.classification: Exact classification reaches fully copied fields and actual local deallocation. *)
From Coq Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Clight.
Require Import Slice Machine ClightSteps StoreSteps WriteAll CallPaths SourcePaths SourceReach
  ResultLayout ResultSafety SenderSource ReceiverSource ReceiverReadSource ReceiverReadMemory
  ReceiverPreparation ReceiverChoice ReceiverSelectionSource ReceiverSelection
  ReceiverMemory ReceiverConstruction.
Import ListNotations.
Open Scope Z_scope.
Theorem receiver_classification_source : forall cell base b bytes bad entered done status le m output ofs run uid,
  receiver_preserved cell base output ofs m -> receiver_slots_owned base b m ->
  result_input m output ofs run uid -> Mem.valid_block base output -> receiver_buffer cell b m bytes ->
  le!__res=Some(Vptr output(Ptrofs.repr ofs)) ->
  le!_bad=Some(Vint bad) -> le!_entered=Some(Vint entered) ->
  le!_leader_done=Some(Vint done) -> le!_leader_status=Some(Vint status) ->
  le!_used=Some(Vlong(Int64.repr(Z.of_nat(length bytes)))) ->
  source_returns result_ge(receiver_preserved cell base output ofs)
    (receiver_choice_result output ofs(receiver_select bytes bad entered done status)uid run b)
    (State f_m4_collect_failure receiver_after_close Kstop(receiver_env b)le m).
Proof.
  intros cell base b bytes bad entered done status le m output ofs run uid
    PRE SLOTS INPUT VALID BUFFER OUT BAD ENTERED DONE STATUS USED.
  eapply source_returns_prepend;[exact PRE|apply unchanged_store_edge;WriteAll.structural|].
  destruct(receiver_selection_source cell b bytes bad entered done status le Kstop m
    (receiver_buffer_readable _ _ _ _ BUFFER)(proj1 BUFFER)BAD ENTERED DONE STATUS USED)
    as[count[last[PATH[selected[EQ KEEP]]]]];subst last.
  eapply source_returns_path.
  - eapply store_path_consequence;[exact PATH|intros after SAME;change(after=m)in SAME;subst after;exact PRE].
  - eapply receiver_construction_source;[exact PRE|exact SLOTS|exact INPUT|exact VALID|].
    rewrite(KEEP __res ltac:(cbn;tauto));exact OUT.
Qed.
