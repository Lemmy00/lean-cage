(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.decimal: Exact source parsing, memory behavior and interruption. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Readers Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From LeanCageController Require Import NumberSlice NumberStructure NumberMath NumberWords NumberMemory NumberValues NumberEntry.
Open Scope Z_scope.
Lemma number_bool_value m flag : bool_val (Val.of_bool flag) tint m=Some flag.
Proof. destruct flag;reflexivity. Qed.
Lemma number_bool_cast m flag : sem_cast (Val.of_bool flag) tint tbool m=Some (Val.of_bool flag).
Proof. destruct flag;reflexivity. Qed.
Definition number_guard_env le b := PTree.set _t'7 (Vint (byte_word b)) le.
Lemma number_guard_path ge m block ofs b le k P :
 le ! _p=Some(Vptr block ofs) -> Mem.loadv Mint8unsigned m (Vptr block ofs)=Some(Vint(byte_word b)) -> P m ->
 store_path ge P (State f_number number_guard k empty_env le m) 4
 (State f_number (if negb(Int.eq (byte_word b) Int.zero) then Sskip else Sbreak) k empty_env (number_guard_env le b) m).
Proof.
 intros PTR LOAD GOOD. number_unfold number_guard.
 number_route;number_set;[exact LOAD|]. number_route.
 number_branch (negb(Int.eq (byte_word b) Int.zero));[reflexivity|].
 apply store_done;exact GOOD.
Qed.
Definition number_digit_bad b := (Byte.unsigned b <? 48) || (57 <? Byte.unsigned b).
Definition number_digit_env le b := PTree.set _t'1 (Val.of_bool(number_digit_bad b))
 (if Byte.unsigned b <? 48 then PTree.set _t'5 (Vint(byte_word b)) le
 else PTree.set _t'6 (Vint(byte_word b)) (PTree.set _t'5 (Vint(byte_word b)) le)).
Lemma number_digit_path ge m block ofs b le k P :
 le ! _p=Some(Vptr block ofs) -> Mem.loadv Mint8unsigned m (Vptr block ofs)=Some(Vint(byte_word b)) -> P m ->
 store_path ge P (State f_number number_digit_test k empty_env le m)
 (if Byte.unsigned b <? 48 then 5%nat else 8%nat)
 (State f_number Sskip k empty_env (number_digit_env le b) m).
Proof.
 intros PTR LOAD GOOD. number_unfold number_digit_test.
 unfold number_digit_env,number_digit_bad.
 destruct (Byte.unsigned b <? 48) eqn:LOW.
 - number_route;number_set;[exact LOAD|]. number_route.
   number_branch true.
   + change (bool_val (Val.of_bool(Int.lt(byte_word b)(Int.repr 48))) tint m=Some true).
     rewrite number_bool_value,number_low_test,LOW;reflexivity.
   + number_set. apply store_done;exact GOOD.
 - number_route;number_set;[exact LOAD|]. number_route.
   number_branch false.
   + change (bool_val (Val.of_bool(Int.lt(byte_word b)(Int.repr 48))) tint m=Some false).
     rewrite number_bool_value,number_low_test,LOW;reflexivity.
   + number_route;number_set;[exact LOAD|]. number_route.
     number_next;[eapply certified_set_edge; eapply cast_expression_value;
       [apply old_expression_value;WriteAll.expression|]|].
     * match goal with |- _ = Some ?v =>
         change (sem_cast (Val.of_bool(Int.lt(Int.repr 57)(byte_word b))) tint tbool m=Some v) end.
       rewrite number_high_test;apply number_bool_cast.
     * apply store_done;exact GOOD.
Qed.
Definition number_overflow_flag acc b bad := bad || Int64.ltu (number_machine_threshold b) (Int64.repr acc).
Definition number_overflow_env le acc b (bad : bool) :=
 if bad then PTree.set _t'2 (Vint Int.one) le else
 PTree.set _t'2 (Val.of_bool (Int64.ltu (number_machine_threshold b) (Int64.repr acc)))
   (PTree.set _t'4 (Vint(byte_word b)) le).
Lemma number_overflow_path ge m block ofs acc b bad le k P :
 le ! _p=Some(Vptr block ofs) -> le ! _result=Some(Vlong(Int64.repr acc)) ->
 le ! _t'1=Some(Val.of_bool bad) ->
 Mem.loadv Mint8unsigned m (Vptr block ofs)=Some(Vint(byte_word b)) -> P m ->
 store_path ge P (State f_number number_overflow_test k empty_env le m)
 (if bad then 2%nat else 5%nat)
 (State f_number Sskip k empty_env (number_overflow_env le acc b bad) m).
Proof.
 intros PTR ACC BAD LOAD GOOD. number_unfold number_overflow_test.
 unfold number_overflow_env;destruct bad.
 - number_branch true;[reflexivity|]. number_set. apply store_done;exact GOOD.
 - number_branch false;[reflexivity|]. number_route;number_set;[exact LOAD|]. number_route.
   number_next;[eapply certified_set_edge;eapply cast_expression_value;
    [apply number_overflow_value;WriteAll.lookup|apply number_bool_cast]|].
   apply store_done;exact GOOD.
Qed.
Definition number_update_env le acc b :=
 PTree.set _result (Vlong(number_machine_update acc b)) (PTree.set _t'3 (Vint(byte_word b)) le).
Lemma number_update_path ge m block ofs acc b le k P :
 le ! _p=Some(Vptr block ofs) -> le ! _result=Some(Vlong(Int64.repr acc)) ->
 Mem.loadv Mint8unsigned m (Vptr block ofs)=Some(Vint(byte_word b)) -> P m ->
 store_path ge P (State f_number number_update k empty_env le m) 4
 (State f_number Sskip k empty_env (number_update_env le acc b) m).
Proof.
 intros PTR ACC LOAD GOOD. number_unfold number_update.
 number_route;number_set;[exact LOAD|]. number_route.
 number_next;[eapply certified_set_edge;apply number_update_value;WriteAll.lookup|].
 apply store_done;exact GOOD.
Qed.
Lemma number_digit_bad_exact b : number_digit_bad b=false <-> decimal_digit_ok b.
Proof.
 unfold number_digit_bad,decimal_digit_ok;rewrite orb_false_iff,!Z.ltb_ge;lia.
Qed.
Lemma number_step_rejected_digit acc b : number_digit_bad b=true -> decimal_step acc b=None.
Proof.
 intros BAD;unfold decimal_step.
 destruct ((48<=?Byte.unsigned b)&&(Byte.unsigned b<=?57)) eqn:DIG;[|reflexivity].
 apply andb_true_iff in DIG;destruct DIG as [LOW HIGH];apply Z.leb_le in LOW;apply Z.leb_le in HIGH.
 assert (OK : number_digit_bad b=false) by (apply number_digit_bad_exact;unfold decimal_digit_ok;lia).
 congruence.
Qed.
Lemma number_step_overflow acc b : 0<=acc<=decimal_max -> number_digit_bad b=false ->
 Int64.ltu (number_machine_threshold b) (Int64.repr acc)=true -> decimal_step acc b=None.
Proof.
 intros ACC DIG OVER;apply number_digit_bad_exact in DIG.
 rewrite number_overflow_test_exact in OVER by assumption.
 unfold decimal_step.
 destruct ((48<=?Byte.unsigned b)&&(Byte.unsigned b<=?57));[|reflexivity].
 destruct (acc<=?(decimal_max-decimal_digit b)/10);[discriminate|reflexivity].
Qed.
Lemma number_step_continue acc b : 0<=acc<=decimal_max -> number_digit_bad b=false ->
 Int64.ltu (number_machine_threshold b) (Int64.repr acc)=false ->
 decimal_step acc b=Some(acc*10+decimal_digit b).
Proof.
 intros ACC DIG OVER;apply number_digit_bad_exact in DIG.
 rewrite number_overflow_test_exact in OVER by assumption.
 apply decimal_step_exact;split;[exact DIG|]. split;[|reflexivity].
 apply decimal_threshold.
 destruct (acc<=?(decimal_max-decimal_digit b)/10) eqn:SIZE;[now apply Z.leb_le|discriminate].
Qed.
