(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.plan: Imported numeric results determine actual native source paths. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata Events Clight.
Require Import Machine Deterministic StoreSteps.
From LeanCageController Require Import NumberStructure NumberMath NumberMemory NumberStorage
 NumberSource NumberSafety NumberAllocation NumberWitnesses.
From LeanCagePlan Require Import PlanCodec.
Import ListNotations.
Open Scope Z_scope.
Definition plan_result bytes := option_map Z.of_nat (plan_parsed bytes).
Theorem plan_source_path ge m block ofs bytes out outofs k :
 number_input m block ofs bytes -> number_output m out outofs ->
 exists count after, number_post m out outofs (plan_result bytes) after /\
 store_path ge (number_memory m out outofs (plan_result bytes))
 (number_initial (Vptr block ofs) (Vptr out outofs) k m) count
 (Returnstate (number_code (plan_result bytes)) (call_cont k) after).
Proof. unfold plan_result;rewrite plan_parser_value;apply number_source_path. Qed.
Theorem plan_source_execution ge cell m block ofs bytes out outofs k :
 number_input m block ofs bytes -> number_output m out outofs ->
 exists count after, number_post m out outofs (plan_result bytes) after /\
 steps ge cell (live(number_initial (Vptr block ofs) (Vptr out outofs) k m))
 (repeat (source_step E0) count) (live(Returnstate (number_code(plan_result bytes)) (call_cont k) after)).
Proof. unfold plan_result;rewrite plan_parser_value;apply number_source_execution. Qed.
Theorem plan_source_return ge cell m block ofs bytes out outofs events value after :
 number_input m block ofs bytes -> number_output m out outofs ->
 steps ge cell (live(number_initial (Vptr block ofs) (Vptr out outofs) Kstop m))
 events (live(Returnstate value Kstop after)) ->
 value=number_code(plan_result bytes) /\ number_post m out outofs (plan_result bytes) after.
Proof. unfold plan_result;rewrite plan_parser_value;apply number_source_return. Qed.
Theorem plan_source_prefix ge cell m block ofs bytes out outofs events target :
 number_input m block ofs bytes -> number_output m out outofs ->
 steps ge cell (live(number_initial (Vptr block ofs) (Vptr out outofs) Kstop m)) events target ->
 number_memory m out outofs (plan_result bytes) (routine_memory target).
Proof. unfold plan_result;rewrite plan_parser_value;apply number_source_prefix. Qed.
Theorem plan_source_progress ge cell m block ofs bytes out outofs events s :
 number_input m block ofs bytes -> number_output m out outofs ->
 steps ge cell (live(number_initial (Vptr block ofs) (Vptr out outofs) Kstop m)) events (live s) ->
 (exists after, s=Returnstate(number_code(plan_result bytes)) Kstop after /\
   number_post m out outofs (plan_result bytes) after) \/
 exists next,step ge cell (live s) (source_step E0) (live next).
Proof. unfold plan_result;rewrite plan_parser_value;apply number_source_progress. Qed.
Theorem plan_source_loss ge cell m block ofs bytes out outofs :
 number_input m block ofs bytes -> number_output m out outofs ->
 exists count after,
 number_post m out outofs (plan_result bytes) after /\
 steps ge cell (live(number_initial (Vptr block ofs) (Vptr out outofs) Kstop m))
 (repeat(source_step E0) count) (live(Returnstate(number_code(plan_result bytes)) Kstop after)) /\
 forall n,(n<=count)%nat -> exists mid,
 steps ge cell (live(number_initial (Vptr block ofs) (Vptr out outofs) Kstop m))
 (repeat(source_step E0) n) (live mid) /\
 steps ge cell (live(number_initial (Vptr block ofs) (Vptr out outofs) Kstop m))
 (repeat(source_step E0) n++[loss_step]) (dead(memory_of mid)) /\
 number_memory m out outofs (plan_result bytes) (memory_of mid).
Proof. unfold plan_result;rewrite plan_parser_value;apply number_source_loss. Qed.
Theorem plan_source_rejection ge cell m block ofs bytes out outofs events target :
 number_input m block ofs bytes -> number_output m out outofs -> plan_parsed bytes=None ->
 steps ge cell (live(number_initial (Vptr block ofs) (Vptr out outofs) Kstop m)) events target ->
 routine_memory target=m.
Proof. rewrite plan_parser_none;apply number_rejection_unchanged. Qed.
Theorem plan_source_success ge cell m block ofs bytes out outofs events after :
 number_input m block ofs bytes -> number_output m out outofs ->
 steps ge cell (live(number_initial (Vptr block ofs) (Vptr out outofs) Kstop m)) events
 (live(Returnstate(Vint Int.zero) Kstop after)) ->
 exists value,plan_parsed bytes=Some value /\ Z.of_nat value<=decimal_max /\
 Mem.load Mint64 after out (Ptrofs.unsigned outofs)=Some(Vlong(Int64.repr(Z.of_nat value))).
Proof.
 intros INPUT OUTPUT RUN.
 destruct(number_success_value ge cell m block ofs bytes out outofs events after INPUT OUTPUT RUN)
 as [value [PARSED [RANGE LOAD]]].
 exists(Z.to_nat value);rewrite Z2Nat.id by lia.
 split;[apply plan_parser_some;rewrite Z2Nat.id by lia;exact PARSED|]. split;[lia|exact LOAD].
Qed.
Theorem plan_overlapping_source base ge cell bytes :
 Forall (fun b => b<>Byte.zero) bytes -> Z.of_nat(length bytes)+9<=Ptrofs.modulus ->
 exists allocated block m count after,
 Mem.alloc base 0 (Z.of_nat(length(number_allocation_bytes bytes)))=(allocated,block) /\
 Mem.storebytes allocated block 0 (map Byte(number_allocation_bytes bytes))=Some m /\
 number_input m block Ptrofs.zero bytes /\ number_output m block Ptrofs.zero /\
 number_post m block Ptrofs.zero (plan_result bytes) after /\
 steps ge cell (live(number_initial (Vptr block Ptrofs.zero) (Vptr block Ptrofs.zero) Kstop m))
 (repeat(source_step E0) count) (live(Returnstate(number_code(plan_result bytes)) Kstop after)).
Proof. unfold plan_result;rewrite plan_parser_value;apply number_overlapping_source. Qed.
Theorem plan_separate_source base ge cell bytes :
 Forall (fun b => b<>Byte.zero) bytes -> Z.of_nat(length bytes)+9<=Ptrofs.modulus ->
 exists allocated block before m out count after,
 Mem.alloc base 0 (Z.of_nat(length(number_allocation_bytes bytes)))=(allocated,block) /\
 Mem.storebytes allocated block 0 (map Byte(number_allocation_bytes bytes))=Some before /\
 Mem.alloc before 0 8=(m,out) /\ block<>out /\
 number_input m block Ptrofs.zero bytes /\ number_output m out Ptrofs.zero /\
 number_post m out Ptrofs.zero (plan_result bytes) after /\
 steps ge cell (live(number_initial (Vptr block Ptrofs.zero) (Vptr out Ptrofs.zero) Kstop m))
 (repeat(source_step E0) count) (live(Returnstate(number_code(plan_result bytes)) Kstop after)).
Proof. unfold plan_result;rewrite plan_parser_value;apply number_separate_source. Qed.
