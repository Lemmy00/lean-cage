(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.memory: Actual branch copy, caller copy and seven-local return path. *)
From Coq Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Slice Machine ClightSteps StoreSteps WriteAll LocalAccess CallAccess ResultLayout
  SenderSource ReceiverSource ReceiverReadSource ReceiverChoice ReceiverSelectionSource.
Import ListNotations.
Open Scope Z_scope.
Ltac receiver_tail_route := eapply store_next;[assumption|apply unchanged_store_edge;WriteAll.structural|].
Theorem receiver_tail_source : forall (P : mem->Prop) b choice le k before middle copied final output ofs,
  le!__res=Some(Vptr output(Ptrofs.repr ofs)) ->
  assign_loc result_ge result_type before(rb_result b)Ptrofs.zero Full
    (Vptr(receiver_choice_block b choice)Ptrofs.zero)middle ->
  assign_loc result_ge result_type middle output(Ptrofs.repr ofs)Full
    (Vptr(rb_result b)Ptrofs.zero)copied ->
  Mem.free_list copied(blocks_of_env result_ge(receiver_env b))=Some final ->
  P before -> P middle -> P copied -> P final ->
  exists count,store_path result_ge P(Returnstate Vundef(receiver_choice_cont b choice le k)before)count
    (Returnstate Vundef(call_cont k)final).
Proof.
  intros P b choice le k before middle copied final output ofs OUT FIRST SECOND FREE PB PM PC PF.
  eexists;unfold receiver_choice_cont,receiver_choice_copy.
  receiver_tail_route. receiver_tail_route.
  eapply store_next;[exact PB| |].
  - eapply assignment_source_edge with(v:=Vptr(receiver_choice_block b choice)Ptrofs.zero);
      [receiver_location| |reflexivity|exact FIRST].
    unfold receiver_choice_block,receiver_choice_ident;destruct(rc_branch choice);(eapply location_read_value;
      [receiver_location|apply deref_loc_copy;reflexivity]).
  - receiver_tail_route. receiver_tail_route.
    unfold receiver_copy_return,receiver_after_close,receiver_after_loop;cbn [statement_drop].
    eapply store_next;[exact PM| |].
    + eapply assignment_source_edge with(v:=Vptr(rb_result b)Ptrofs.zero);
        [receiver_location| |reflexivity|exact SECOND].
      eapply location_read_value;[receiver_location|apply deref_loc_copy;reflexivity].
    + receiver_tail_route. eapply store_next;[exact PC|apply local_void_return_edge;exact FREE|].
      apply store_done;exact PF.
Qed.
