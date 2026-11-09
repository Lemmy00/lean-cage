(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Uniform source-step bounds for the actual bounded numeric callee. *)
(* Reuses the accepted NumberControl/Iterations/Loop source paths; no Linux time bound. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Readers Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From LeanCageMainNumber Require Import NumberSlice NumberStructure NumberMath NumberWords
  NumberMemory NumberValues NumberEntry NumberControl NumberStorage NumberIterations NumberLoop NumberInitial.
Import ListNotations.
Open Scope Z_scope.

Lemma handoff_number_checks_bound ge m block ofs acc b le k P :
  le ! _p = Some (Vptr block ofs) -> le ! _result = Some (Vlong (Int64.repr acc)) ->
  Mem.loadv Mint8unsigned m (Vptr block ofs) = Some (Vint (byte_word b)) ->
  b <> Byte.zero -> P m ->
  exists count, (count <= 30)%nat /\
    store_path ge P (State f_number number_loop (number_loop_cont k) empty_env le m) count
      (State f_number number_reject (number_checks_cont k) empty_env (number_checks_env le acc b) m).
Proof.
  intros PTR ACC LOAD NONZERO GOOD; eexists; split.
  2: {
    rewrite number_loop_structure; number_route.
    rewrite number_loop_body_structure at 1; number_route.
    eapply store_path_trans;
      [apply number_guard_path with (block:=block) (ofs:=ofs); [exact PTR|exact LOAD|exact GOOD]|].
    rewrite number_nonzero_test by exact NONZERO; cbn [negb].
    do 4 number_route.
    eapply store_path_trans;
      [apply number_digit_path with (block:=block) (ofs:=ofs);
        [unfold number_guard_env; WriteAll.lookup|exact LOAD|exact GOOD]|].
    number_route.
    eapply store_path_trans;
      [apply number_overflow_path with (block:=block) (ofs:=ofs) (acc:=acc) (b:=b)
        (bad:=number_digit_bad b)|].
    - unfold number_digit_env, number_guard_env; destruct (Byte.unsigned b <? 48); WriteAll.lookup.
    - unfold number_digit_env, number_guard_env; destruct (Byte.unsigned b <? 48); WriteAll.lookup.
    - unfold number_digit_env; WriteAll.lookup.
    - exact LOAD.
    - exact GOOD.
    - number_route; apply store_done; exact GOOD.
  }
  destruct (Byte.unsigned b <? 48); destruct (number_digit_bad b); cbn; lia.
Qed.

Lemma handoff_number_rejected_bound ge m block ofs acc b le k P :
  le ! _p = Some (Vptr block ofs) -> le ! _result = Some (Vlong (Int64.repr acc)) ->
  Mem.loadv Mint8unsigned m (Vptr block ofs) = Some (Vint (byte_word b)) ->
  b <> Byte.zero -> P m -> number_overflow_flag acc b (number_digit_bad b) = true ->
  exists count, (count <= 50)%nat /\
    store_path ge P (State f_number number_loop (number_loop_cont k) empty_env le m) count
      (Returnstate (Vint Int.mone) (call_cont k) m).
Proof.
  intros PTR ACC LOAD NONZERO GOOD BAD.
  destruct (handoff_number_checks_bound ge m block ofs acc b le k P PTR ACC LOAD NONZERO GOOD)
    as [count [BOUND CHECKS]].
  exists (count + 2)%nat; split; [lia|].
  eapply store_path_trans; [exact CHECKS|].
  pose proof (number_checks_t2 le acc b) as FLAG; rewrite BAD in FLAG.
  number_unfold number_reject.
  number_branch true; [reflexivity|].
  number_next; [apply unchanged_store_edge; eapply edge_return; [WriteAll.expression|reflexivity]|].
  apply store_done; exact GOOD.
Qed.

Lemma handoff_number_successful_bound ge m block ofs acc b le k P :
  le ! _p = Some (Vptr block ofs) -> le ! _result = Some (Vlong (Int64.repr acc)) ->
  Mem.loadv Mint8unsigned m (Vptr block ofs) = Some (Vint (byte_word b)) ->
  b <> Byte.zero -> P m -> number_overflow_flag acc b (number_digit_bad b) = false ->
  exists count, (count <= 50)%nat /\
    store_path ge P (State f_number number_loop (number_loop_cont k) empty_env le m) count
      (State f_number number_loop (number_loop_cont k) empty_env (number_next_env le block ofs acc b) m).
Proof.
  intros PTR ACC LOAD NONZERO GOOD BAD.
  destruct (handoff_number_checks_bound ge m block ofs acc b le k P PTR ACC LOAD NONZERO GOOD)
    as [count [BOUND CHECKS]].
  exists (count + 9)%nat; split; [lia|].
  eapply store_path_trans; [exact CHECKS|].
  pose proof (number_checks_t2 le acc b) as FLAG; rewrite BAD in FLAG.
  destruct (number_checks_registers le acc b) as [PTR' [ACC' OUT']].
  number_unfold number_reject.
  number_branch false; [reflexivity|]; number_route.
  eapply store_path_trans with (n:=4%nat) (k:=3%nat);
    [apply number_update_path with (block:=block) (ofs:=ofs) (acc:=acc) (b:=b);
      [now rewrite PTR'|now rewrite ACC'|exact LOAD|exact GOOD]|].
  number_route; number_unfold number_increment.
  assert (UPDATED_PTR : (number_update_env (number_checks_env le acc b) acc b)!_p = Some (Vptr block ofs)).
  { unfold number_update_env; repeat rewrite PTree.gso by discriminate; now rewrite PTR'. }
  number_set; number_route; apply store_done; exact GOOD.
Qed.

Theorem handoff_number_loop_bound ge m block out outofs k : forall bytes ofs acc le,
  number_input m block ofs bytes -> number_output m out outofs ->
  le ! _p = Some (Vptr block ofs) -> le ! _result = Some (Vlong (Int64.repr acc)) ->
  le ! _value = Some (Vptr out outofs) -> 0 <= acc <= decimal_max ->
  exists count after, (count <= 100 * length bytes + 50)%nat /\
    number_post m out outofs (decimal_loop acc bytes) after /\
    store_path ge (number_memory m out outofs (decimal_loop acc bytes))
      (State f_number number_loop (number_loop_cont k) empty_env le m) count
      (Returnstate (number_code (decimal_loop acc bytes)) (call_cont k) after).
Proof.
  induction bytes as [|b bytes IH]; intros ofs acc le INPUT OUTPUT PTR ACC OUT RANGE.
  - destruct (number_store_exists m out outofs (Int64.repr acc) OUTPUT) as [after STORE].
    exists 13%nat, after; split; [cbn; lia|]; split; [exact STORE|].
    apply number_empty_loop_path with (block:=block) (ofs:=ofs) (out:=out) (outofs:=outofs) (acc:=acc);
      try assumption; [apply number_memory_initial|right; exact STORE].
  - destruct (number_read_head m block ofs (b::bytes) b (bytes++[Byte.zero]) INPUT eq_refl) as [LOAD _].
    pose proof (number_input_head m block ofs b bytes INPUT) as NONZERO.
    destruct (number_digit_bad b) eqn:BAD.
    + pose proof (number_step_rejected_digit acc b BAD) as STEP; cbn [decimal_loop]; rewrite STEP.
      assert (FLAG : number_overflow_flag acc b (number_digit_bad b) = true).
      { unfold number_overflow_flag; rewrite BAD; reflexivity. }
      destruct (handoff_number_rejected_bound ge m block ofs acc b le k
        (number_memory m out outofs None) PTR ACC LOAD NONZERO (number_memory_initial m out outofs None) FLAG)
        as [count [BOUND RUN]].
      exists count, m; split; [cbn; lia|]; split; [reflexivity|exact RUN].
    + destruct (Int64.ltu (number_machine_threshold b) (Int64.repr acc)) eqn:OVER.
      * pose proof (number_step_overflow acc b RANGE BAD OVER) as STEP; cbn [decimal_loop]; rewrite STEP.
        assert (FLAG : number_overflow_flag acc b (number_digit_bad b) = true).
        { unfold number_overflow_flag; rewrite BAD, OVER; reflexivity. }
        destruct (handoff_number_rejected_bound ge m block ofs acc b le k
          (number_memory m out outofs None) PTR ACC LOAD NONZERO (number_memory_initial m out outofs None) FLAG)
          as [count [BOUND RUN]].
        exists count, m; split; [cbn; lia|]; split; [reflexivity|exact RUN].
      * pose proof (number_step_continue acc b RANGE BAD OVER) as STEP; cbn [decimal_loop]; rewrite STEP.
        destruct (number_next_registers le block ofs acc b (acc*10+decimal_digit b) (proj1 RANGE) STEP)
          as [PTR' [ACC' OUT']].
        assert (OUT'' : (number_next_env le block ofs acc b)!_value = Some (Vptr out outofs)) by congruence.
        destruct (IH (Ptrofs.add ofs Ptrofs.one) (acc*10+decimal_digit b)
          (number_next_env le block ofs acc b) (number_input_tail m block ofs b bytes INPUT)
          OUTPUT PTR' ACC' OUT'' (decimal_step_nonnegative acc b _ (proj1 RANGE) STEP))
          as [tail_count [after [TAIL_BOUND [POST TAIL]]]].
        assert (FLAG : number_overflow_flag acc b (number_digit_bad b) = false).
        { unfold number_overflow_flag; rewrite BAD, OVER; reflexivity. }
        destruct (handoff_number_successful_bound ge m block ofs acc b le k
          (number_memory m out outofs (decimal_loop (acc*10+decimal_digit b) bytes))
          PTR ACC LOAD NONZERO (number_memory_initial _ _ _ _) FLAG) as [count [BOUND RUN]].
        exists (count + tail_count)%nat, after; split; [cbn; lia|]; split; [exact POST|].
        eapply store_path_trans; [exact RUN|exact TAIL].
Qed.

Theorem handoff_number_source_bound ge m block ofs bytes out outofs k :
  number_input m block ofs bytes -> number_output m out outofs ->
  exists count after, (count <= 100 * length bytes + 100)%nat /\
    number_post m out outofs (decimal_number bytes) after /\
    store_path ge (number_memory m out outofs (decimal_number bytes))
      (number_initial (Vptr block ofs) (Vptr out outofs) k m) count
      (Returnstate (number_code (decimal_number bytes)) (call_cont k) after).
Proof.
  intros INPUT OUTPUT; destruct bytes as [|b bytes].
  - exists 7%nat, m; split; [cbn; lia|]; split; [reflexivity|].
    eapply number_path_implication with (P:=fun after => after=m);
      [intros current SAME; subst; apply number_memory_initial|apply number_empty_source; exact INPUT].
  - destruct (number_started_registers block ofs (Vptr out outofs) b) as [PTR [ACC OUT]].
    destruct (handoff_number_loop_bound ge m block out outofs k (b::bytes) ofs 0
      (number_started_env block ofs (Vptr out outofs) b) INPUT OUTPUT PTR ACC OUT
      ltac:(unfold decimal_max; lia)) as [count [after [BOUND [POST RUN]]]].
    exists (14+count)%nat, after; split; [cbn in *; lia|]; split; [exact POST|].
    eapply store_path_trans with (n:=14%nat);
      [apply number_start_path with (bytes:=bytes); [exact INPUT|apply number_memory_initial]|exact RUN].
Qed.
