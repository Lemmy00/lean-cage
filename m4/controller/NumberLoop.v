(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.decimal: Exact source parsing, memory behavior and interruption. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Readers Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From LeanCageController Require Import NumberSlice NumberStructure NumberMath NumberWords NumberMemory NumberValues NumberEntry NumberControl NumberStorage NumberIterations.
Import ListNotations.
Open Scope Z_scope.
Lemma number_empty_loop_path ge m block ofs out outofs acc le k P after :
 number_input m block ofs [] ->
 le ! _p=Some(Vptr block ofs) -> le ! _result=Some(Vlong(Int64.repr acc)) -> le ! _value=Some(Vptr out outofs) ->
 Mem.storev Mint64 m (Vptr out outofs) (Vlong(Int64.repr acc))=Some after -> P m -> P after ->
 store_path ge P (State f_number number_loop (number_loop_cont k) empty_env le m) 13
 (Returnstate (Vint Int.zero) (call_cont k) after).
Proof.
 intros INPUT PTR ACC OUT STORE GOOD FINAL.
 destruct(number_read_head m block ofs [] Byte.zero [] INPUT eq_refl) as [LOAD _].
 rewrite number_loop_structure;number_route.
 rewrite number_loop_body_structure at 1;number_route.
 eapply store_path_trans with (n:=4%nat) (k:=7%nat);[apply number_guard_path with (block:=block) (ofs:=ofs) (b:=Byte.zero);[exact PTR|exact LOAD|exact GOOD]|].
 change (negb(Int.eq(byte_word Byte.zero) Int.zero)) with false.
 do 3 number_route.
 apply number_finish_path with (out:=out) (ofs:=outofs) (acc:=acc);try assumption;
 unfold number_guard_env;WriteAll.lookup.
Qed.
Theorem number_loop_source ge m block out outofs k : forall bytes ofs acc le,
 number_input m block ofs bytes -> number_output m out outofs ->
 le ! _p=Some(Vptr block ofs) -> le ! _result=Some(Vlong(Int64.repr acc)) -> le ! _value=Some(Vptr out outofs) ->
 0<=acc<=decimal_max ->
 exists count after, number_post m out outofs (decimal_loop acc bytes) after /\
 store_path ge (number_memory m out outofs (decimal_loop acc bytes))
 (State f_number number_loop (number_loop_cont k) empty_env le m) count
 (Returnstate (number_code (decimal_loop acc bytes)) (call_cont k) after).
Proof.
 induction bytes as [|b bytes IH];intros ofs acc le INPUT OUTPUT PTR ACC OUT RANGE.
 - destruct(number_store_exists m out outofs (Int64.repr acc) OUTPUT) as [after STORE].
   exists 13%nat,after;split;[exact STORE|].
   apply number_empty_loop_path with (block:=block) (ofs:=ofs) (out:=out) (outofs:=outofs) (acc:=acc);
   try assumption;[apply number_memory_initial|right;exact STORE].
 - destruct(number_read_head m block ofs (b::bytes) b (bytes++[Byte.zero]) INPUT eq_refl) as [LOAD _].
   pose proof(number_input_head m block ofs b bytes INPUT) as NONZERO.
   destruct(number_digit_bad b) eqn:BAD.
   + pose proof(number_step_rejected_digit acc b BAD) as STEP.
     cbn [decimal_loop];rewrite STEP.
     assert (FLAG : number_overflow_flag acc b (number_digit_bad b)=true).
     { unfold number_overflow_flag;rewrite BAD;reflexivity. }
     destruct(number_rejected_iteration ge m block ofs acc b le k
       (number_memory m out outofs None) PTR ACC LOAD NONZERO
       (number_memory_initial m out outofs None) FLAG) as [count RUN].
     exists count,m;split;[reflexivity|exact RUN].
   + destruct(Int64.ltu (number_machine_threshold b) (Int64.repr acc)) eqn:OVER.
     * pose proof(number_step_overflow acc b RANGE BAD OVER) as STEP.
       cbn [decimal_loop];rewrite STEP.
       assert (FLAG : number_overflow_flag acc b (number_digit_bad b)=true).
       { unfold number_overflow_flag;rewrite BAD,OVER;reflexivity. }
       destruct(number_rejected_iteration ge m block ofs acc b le k
         (number_memory m out outofs None) PTR ACC LOAD NONZERO
         (number_memory_initial m out outofs None) FLAG) as [count RUN].
       exists count,m;split;[reflexivity|exact RUN].
     * pose proof(number_step_continue acc b RANGE BAD OVER) as STEP.
       cbn [decimal_loop];rewrite STEP.
       destruct(number_next_registers le block ofs acc b (acc*10+decimal_digit b) (proj1 RANGE) STEP)
        as [PTR' [ACC' OUT']].
       assert (OUT'' : (number_next_env le block ofs acc b)!_value=Some(Vptr out outofs)) by congruence.
       destruct(IH (Ptrofs.add ofs Ptrofs.one) (acc*10+decimal_digit b)
         (number_next_env le block ofs acc b) (number_input_tail m block ofs b bytes INPUT)
         OUTPUT PTR' ACC' OUT'' (decimal_step_nonnegative acc b _ (proj1 RANGE) STEP))
         as [tail_count [after [POST TAIL]]].
       assert (FLAG : number_overflow_flag acc b (number_digit_bad b)=false).
       { unfold number_overflow_flag;rewrite BAD,OVER;reflexivity. }
       destruct(number_successful_iteration ge m block ofs acc b le k
         (number_memory m out outofs (decimal_loop (acc*10+decimal_digit b) bytes))
         PTR ACC LOAD NONZERO (number_memory_initial _ _ _ _) FLAG) as [count RUN].
       exists (count+tail_count)%nat,after;split;[exact POST|].
       eapply store_path_trans;[exact RUN|exact TAIL].
Qed.
