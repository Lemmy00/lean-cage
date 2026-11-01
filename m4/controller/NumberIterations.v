(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.decimal: Exact source parsing, memory behavior and interruption. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Readers Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From LeanCageController Require Import NumberSlice NumberStructure NumberMath NumberWords NumberMemory NumberValues NumberEntry NumberControl NumberStorage.
Open Scope Z_scope.
Definition number_loop_cont k := Kseq number_finish k.
Definition number_checks_cont k := Kseq number_update (Kloop1 number_loop_body number_increment (number_loop_cont k)).
Definition number_checks_env le acc b := number_overflow_env
 (number_digit_env (number_guard_env le b) b) acc b (number_digit_bad b).
Lemma number_checks_path ge m block ofs acc b le k P :
 le ! _p=Some(Vptr block ofs) -> le ! _result=Some(Vlong(Int64.repr acc)) ->
 Mem.loadv Mint8unsigned m (Vptr block ofs)=Some(Vint(byte_word b)) -> b<>Byte.zero -> P m ->
 exists count, store_path ge P (State f_number number_loop (number_loop_cont k) empty_env le m) count
 (State f_number number_reject (number_checks_cont k) empty_env (number_checks_env le acc b) m).
Proof.
 intros PTR ACC LOAD NONZERO GOOD. eexists.
 rewrite number_loop_structure;number_route.
 rewrite number_loop_body_structure at 1;number_route.
 eapply store_path_trans;[apply number_guard_path with (block:=block) (ofs:=ofs);[exact PTR|exact LOAD|exact GOOD]|].
 rewrite number_nonzero_test by exact NONZERO;cbn [negb].
 do 4 number_route.
 eapply store_path_trans;[apply number_digit_path with (block:=block) (ofs:=ofs);[unfold number_guard_env;WriteAll.lookup|exact LOAD|exact GOOD]|].
 number_route.
 eapply store_path_trans;[apply number_overflow_path with (block:=block) (ofs:=ofs) (acc:=acc) (b:=b) (bad:=number_digit_bad b)|].
 - unfold number_digit_env,number_guard_env;destruct(Byte.unsigned b <? 48);WriteAll.lookup.
 - unfold number_digit_env,number_guard_env;destruct(Byte.unsigned b <? 48);WriteAll.lookup.
 - unfold number_digit_env;WriteAll.lookup.
 - exact LOAD.
 - exact GOOD.
 - number_route. apply store_done;exact GOOD.
Qed.
Lemma number_checks_t2 le acc b : (number_checks_env le acc b) ! _t'2 =
 Some(Val.of_bool(number_overflow_flag acc b (number_digit_bad b))).
Proof.
 unfold number_checks_env,number_overflow_env,number_overflow_flag.
 destruct(number_digit_bad b);WriteAll.lookup.
Qed.
Lemma number_checks_registers le acc b :
 (number_checks_env le acc b)!_p=le!_p /\
 (number_checks_env le acc b)!_result=le!_result /\
 (number_checks_env le acc b)!_value=le!_value.
Proof.
 unfold number_checks_env,number_overflow_env,number_digit_env,number_guard_env.
 destruct(number_digit_bad b);destruct(Byte.unsigned b <? 48);repeat split;WriteAll.lookup.
Qed.
Lemma number_rejected_iteration ge m block ofs acc b le k P :
 le ! _p=Some(Vptr block ofs) -> le ! _result=Some(Vlong(Int64.repr acc)) ->
 Mem.loadv Mint8unsigned m (Vptr block ofs)=Some(Vint(byte_word b)) -> b<>Byte.zero -> P m ->
 number_overflow_flag acc b (number_digit_bad b)=true ->
 exists count,store_path ge P (State f_number number_loop (number_loop_cont k) empty_env le m) count
 (Returnstate (Vint Int.mone) (call_cont k) m).
Proof.
 intros PTR ACC LOAD NONZERO GOOD BAD.
 destruct(number_checks_path ge m block ofs acc b le k P PTR ACC LOAD NONZERO GOOD) as [count CHECKS].
 eexists;eapply store_path_trans;[exact CHECKS|].
 pose proof(number_checks_t2 le acc b) as FLAG;rewrite BAD in FLAG.
 number_unfold number_reject.
 number_branch true;[reflexivity|].
 number_next;[apply unchanged_store_edge;eapply edge_return;[WriteAll.expression|reflexivity]|].
 apply store_done;exact GOOD.
Qed.
Definition number_next_env le block ofs acc b :=
 PTree.set _p (Vptr block (Ptrofs.add ofs Ptrofs.one))
 (number_update_env (number_checks_env le acc b) acc b).
Lemma number_successful_iteration ge m block ofs acc b le k P :
 le ! _p=Some(Vptr block ofs) -> le ! _result=Some(Vlong(Int64.repr acc)) ->
 Mem.loadv Mint8unsigned m (Vptr block ofs)=Some(Vint(byte_word b)) -> b<>Byte.zero -> P m ->
 number_overflow_flag acc b (number_digit_bad b)=false ->
 exists count,store_path ge P (State f_number number_loop (number_loop_cont k) empty_env le m) count
 (State f_number number_loop (number_loop_cont k) empty_env (number_next_env le block ofs acc b) m).
Proof.
 intros PTR ACC LOAD NONZERO GOOD BAD.
 destruct(number_checks_path ge m block ofs acc b le k P PTR ACC LOAD NONZERO GOOD) as [count CHECKS].
 eexists;eapply store_path_trans;[exact CHECKS|].
 pose proof(number_checks_t2 le acc b) as FLAG;rewrite BAD in FLAG.
 destruct(number_checks_registers le acc b) as [PTR' [ACC' OUT']].
 number_unfold number_reject.
 number_branch false;[reflexivity|]. number_route.
 eapply store_path_trans;[apply number_update_path with (block:=block) (ofs:=ofs) (acc:=acc) (b:=b);[now rewrite PTR'|now rewrite ACC'|exact LOAD|exact GOOD]|].
 number_route;number_unfold number_increment.
 assert (UPDATED_PTR : (number_update_env (number_checks_env le acc b) acc b)!_p=Some(Vptr block ofs)).
 { unfold number_update_env;repeat rewrite PTree.gso by discriminate;now rewrite PTR'. }
 number_set.
 number_route. apply store_done;exact GOOD.
Qed.
Lemma number_next_registers le block ofs acc b next :
 0<=acc -> decimal_step acc b=Some next ->
 (number_next_env le block ofs acc b)!_p=Some(Vptr block(Ptrofs.add ofs Ptrofs.one)) /\
 (number_next_env le block ofs acc b)!_result=Some(Vlong(Int64.repr next)) /\
 (number_next_env le block ofs acc b)!_value=le!_value.
Proof.
 intros ACC STEP;unfold number_next_env,number_update_env.
 repeat split.
 - WriteAll.lookup.
 - rewrite PTree.gso by discriminate;rewrite PTree.gss.
   rewrite (number_machine_update_exact acc b next ACC STEP);reflexivity.
 - repeat rewrite PTree.gso by discriminate.
   exact (proj2 (proj2 (number_checks_registers le acc b))).
Qed.
