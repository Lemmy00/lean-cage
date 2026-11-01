(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.decimal: Exact source parsing, memory behavior and interruption. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Deterministic Readers Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From LeanCageController Require Import NumberSlice NumberStructure NumberMath NumberWords NumberMemory NumberValues NumberEntry NumberControl NumberStorage NumberIterations NumberLoop NumberInitial.
Import ListNotations.
Open Scope Z_scope.
Theorem number_source_path ge m block ofs bytes out outofs k :
 number_input m block ofs bytes -> number_output m out outofs ->
 exists count after, number_post m out outofs (decimal_number bytes) after /\
 store_path ge (number_memory m out outofs (decimal_number bytes))
 (number_initial (Vptr block ofs) (Vptr out outofs) k m) count
 (Returnstate (number_code (decimal_number bytes)) (call_cont k) after).
Proof.
 intros INPUT OUTPUT;destruct bytes as [|b bytes].
 - exists 7%nat,m;split;[reflexivity|].
   eapply number_path_implication with (P:=fun after => after=m);
   [intros current SAME;subst;apply number_memory_initial|apply number_empty_source;exact INPUT].
 - destruct(number_started_registers block ofs (Vptr out outofs) b) as [PTR [ACC OUT]].
   destruct(number_loop_source ge m block out outofs k (b::bytes) ofs 0
    (number_started_env block ofs (Vptr out outofs) b) INPUT OUTPUT PTR ACC OUT
    ltac:(unfold decimal_max;lia)) as [count [after [POST RUN]]].
   exists (14+count)%nat,after;split;[exact POST|].
   eapply store_path_trans with (n:=14%nat);[apply number_start_path with (bytes:=bytes);[exact INPUT|apply number_memory_initial]|exact RUN].
Qed.
Theorem number_source_execution ge cell m block ofs bytes out outofs k :
 number_input m block ofs bytes -> number_output m out outofs ->
 exists count after, number_post m out outofs (decimal_number bytes) after /\
 steps ge cell (live(number_initial (Vptr block ofs) (Vptr out outofs) k m))
 (repeat (source_step E0) count) (live(Returnstate (number_code (decimal_number bytes)) (call_cont k) after)).
Proof.
 intros INPUT OUTPUT;destruct(number_source_path ge m block ofs bytes out outofs k INPUT OUTPUT)
 as [count [after [POST RUN]]]. exists count,after;split;[exact POST|].
 eapply store_path_actual;exact RUN.
Qed.
Theorem number_source_return ge cell m block ofs bytes out outofs events value after :
 number_input m block ofs bytes -> number_output m out outofs ->
 steps ge cell (live(number_initial (Vptr block ofs) (Vptr out outofs) Kstop m))
 events (live(Returnstate value Kstop after)) ->
 value=number_code(decimal_number bytes) /\ number_post m out outofs (decimal_number bytes) after.
Proof.
 intros INPUT OUTPUT RUN.
 destruct(number_source_path ge m block ofs bytes out outofs Kstop INPUT OUTPUT)
 as [count [final [POST SCRIPT]]].
 destruct(store_path_return_exact ge cell _ _ _ _ _ _ _ _ SCRIPT RUN) as [VALUE [AFTER EVENTS]].
 subst;auto.
Qed.
Theorem number_source_prefix ge cell m block ofs bytes out outofs events target :
 number_input m block ofs bytes -> number_output m out outofs ->
 steps ge cell (live(number_initial (Vptr block ofs) (Vptr out outofs) Kstop m)) events target ->
 number_memory m out outofs (decimal_number bytes) (routine_memory target).
Proof.
 intros INPUT OUTPUT RUN.
 destruct(number_source_path ge m block ofs bytes out outofs Kstop INPUT OUTPUT)
 as [count [after [POST SCRIPT]]].
 exact (proj1(store_path_prefix_invariant ge cell _ _ _ _ _ _ _ SCRIPT RUN)).
Qed.
Theorem number_source_progress ge cell m block ofs bytes out outofs events s :
 number_input m block ofs bytes -> number_output m out outofs ->
 steps ge cell (live(number_initial (Vptr block ofs) (Vptr out outofs) Kstop m)) events (live s) ->
 (exists after, s=Returnstate (number_code(decimal_number bytes)) Kstop after /\
   number_post m out outofs (decimal_number bytes) after) \/
 exists next,step ge cell (live s) (source_step E0) (live next).
Proof.
 intros INPUT OUTPUT RUN.
 destruct(number_source_path ge m block ofs bytes out outofs Kstop INPUT OUTPUT)
 as [count [after [POST SCRIPT]]].
 destruct(store_path_defined_prefix ge cell _ _ _ _ _ _ _ SCRIPT RUN) as [DONE|NEXT].
 - left;exists after;auto.
 - right;exact NEXT.
Qed.
Theorem number_source_loss ge cell m block ofs bytes out outofs :
 number_input m block ofs bytes -> number_output m out outofs ->
 exists count after,
 number_post m out outofs (decimal_number bytes) after /\
 steps ge cell (live(number_initial (Vptr block ofs) (Vptr out outofs) Kstop m))
 (repeat (source_step E0) count) (live(Returnstate(number_code(decimal_number bytes)) Kstop after)) /\
 forall n,(n<=count)%nat -> exists mid,
 steps ge cell (live(number_initial (Vptr block ofs) (Vptr out outofs) Kstop m))
 (repeat (source_step E0) n) (live mid) /\
 steps ge cell (live(number_initial (Vptr block ofs) (Vptr out outofs) Kstop m))
 (repeat (source_step E0) n++[loss_step]) (dead(memory_of mid)) /\
 number_memory m out outofs (decimal_number bytes) (memory_of mid).
Proof.
 intros INPUT OUTPUT.
 destruct(number_source_path ge m block ofs bytes out outofs Kstop INPUT OUTPUT)
 as [count [after [POST SCRIPT]]].
 exists count,after;split;[exact POST|]. split;[eapply store_path_actual;exact SCRIPT|].
 intros n BOUND;eapply store_path_loss_every_prefix;[exact SCRIPT|exact BOUND].
Qed.
Theorem number_source_finite_bound ge cell m block ofs bytes out outofs :
 number_input m block ofs bytes -> number_output m out outofs ->
 exists count, forall events target,
 steps ge cell (live(number_initial (Vptr block ofs) (Vptr out outofs) Kstop m)) events target ->
 (length events<=S count)%nat.
Proof.
 intros INPUT OUTPUT.
 destruct(number_source_path ge m block ofs bytes out outofs Kstop INPUT OUTPUT)
 as [count [after [POST SCRIPT]]].
 exists count;intros events target RUN.
 exact (proj2(store_path_prefix_invariant ge cell _ _ _ _ _ _ _ SCRIPT RUN)).
Qed.
