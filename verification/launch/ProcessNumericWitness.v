(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.acceptance: Honest PID2 bytes traverse every actual numeric guard successfully. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From EntryNative Require Import EntrySource NativeArguments NativeHandoffNumeric NativeHandoffNumberBound.
From EntryProcess Require Import ProcessAllocation ProcessStructure ProcessReturns ProcessNumeric.
From LeanCageMainNumber Require Import NumberMath NumberMemory NumberStorage NumberSource NumberInitial.
Import ListNotations.
Open Scope Z_scope.

Definition admission_useful_numeric_env le :=
  PTree.set _t'8 (Vlong(Int64.repr 2))
    (PTree.set _t'5 (Vint Int.zero) (PTree.set _t'9 (Vint(Int.repr 50)) le)).

Theorem admission_useful_numeric_source locals before le k :
  le!_child=Some(Vint(Int.repr 2)) -> le!_pidlength=Some(Vint Int.one) ->
  number_input before(admission_text locals)Ptrofs.zero[Byte.repr 50] ->
  number_output before(admission_encoded locals)Ptrofs.zero ->
  admission_text locals<>admission_encoded locals ->
  exists count after,
    number_post before(admission_encoded locals)Ptrofs.zero(Some 2)after /\
    number_input after(admission_text locals)Ptrofs.zero[Byte.repr 50] /\
    store_path admission_ge(fun _=>True)
      (State f_admit_child(admission_tail 5(fn_body f_admit_child))k(admission_env locals)le before)count
      (State f_admit_child(admission_tail 10(fn_body f_admit_child))k(admission_env locals)
        (admission_useful_numeric_env le)after).
Proof.
  intros CHILD COUNT INPUT OUTPUT SEPARATE.
  set(leading:=PTree.set _t'9(Vint(Int.repr 50))le).
  set(numbered:=PTree.set _t'5(Vint Int.zero)leading).
  destruct(handoff_number_source_bound admission_ge before(admission_text locals)Ptrofs.zero
    [Byte.repr 50](admission_encoded locals)Ptrofs.zero
    (admission_number_cont locals leading(Kseq(admission_tail 9(fn_body f_admit_child))k))
    INPUT OUTPUT)as[number_count[after[BOUND[POST NUMBER]]]].
  change(decimal_number[Byte.repr 50])with(Some 2)in POST,NUMBER.
  exists(25+number_count)%nat,after;split;[exact POST|]. split.
  - eapply admission_numeric_input_preserved;[eapply admission_numeric_memory_post;right;exact POST|
      exact SEPARATE|exact INPUT].
  - rewrite admission_numeric_tail5_actual at 1.
    admission_route.
    eapply store_path_trans with(n:=1%nat).
    + pose proof(admission_positive_length_source locals le before Int.one
        (Kseq(admission_tail 6(fn_body f_admit_child))k)COUNT)as CHECK.
      change(Int.signed Int.one<=?0)with false in CHECK.
      eapply number_path_implication;[|exact CHECK];intros;exact I.
    + admission_route;rewrite admission_numeric_tail6_actual at 1;admission_route.
      eapply store_path_trans with(n:=1%nat).
      * pose proof(admission_bounded_length_source locals le before Int.one
          (Kseq(admission_tail 7(fn_body f_admit_child))k)COUNT ltac:(vm_compute;reflexivity))as CHECK.
        change(32<=?Int.signed Int.one)with false in CHECK.
        eapply number_path_implication;[|exact CHECK];intros;exact I.
      * admission_route;rewrite admission_numeric_tail7_actual at 1;admission_route.
        eapply store_path_trans with(n:=4%nat).
        -- pose proof(admission_leading_digit_source locals le before(Byte.repr 50)[]
             (Kseq(admission_tail 8(fn_body f_admit_child))k)INPUT)as CHECK.
           change(admission_leading_zero(Byte.repr 50))with false in CHECK.
           change(admission_leading_word(Byte.repr 50))with(Int.repr 50)in CHECK.
           eapply number_path_implication;[|exact CHECK];intros;exact I.
        -- change(PTree.set _t'9(Vint(Int.repr 50))le)with leading.
           admission_route;rewrite admission_numeric_tail8_actual at 1;admission_route.
           eapply store_path_trans with(n:=2%nat).
           ++ eapply number_path_implication;[|apply admission_number_call_source];intros;exact I.
           ++ match goal with |-store_path _ _ _ ?remaining _=>
                replace remaining with(number_count+10)%nat by lia end.
              eapply store_path_trans with(n:=number_count).
              ** eapply number_path_implication;[|rewrite current_entry_number_exact;exact NUMBER].
                 intros;exact I.
              ** eapply store_path_trans with(n:=3%nat).
                 --- eapply number_path_implication;[|apply admission_number_return_source with(parsed:=Some 2)].
                     intros;exact I.
                 --- change(PTree.set _t'5(Vint Int.zero)leading)with numbered.
                     admission_route;rewrite admission_numeric_tail9_actual at 1;admission_route.
                     eapply store_path_trans with(n:=4%nat).
                     +++ pose proof(admission_pid_equal_source locals numbered after 2(Int.repr 2)
                           (Kseq(admission_tail 10(fn_body f_admit_child))k))as CHECK.
                         change(Int.signed(Int.repr 2))with 2 in CHECK.
                         specialize(CHECK ltac:(unfold numbered,leading;rewrite !PTree.gso by discriminate;exact CHILD)
                           ltac:(lia) ltac:(change Int64.max_unsigned with 18446744073709551615;lia)
                           (admission_numeric_post_load _ _ _ _ POST)).
                         change(2=?2)with true in CHECK.
                         eapply number_path_implication;[|exact CHECK];intros;exact I.
                     +++ admission_route;apply store_done;exact I.
Qed.
