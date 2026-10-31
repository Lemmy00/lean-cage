(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-native.semantics: Audit a faithful effect interface before claiming simulation. *)
From Coq Require Import ZArith List String Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events
  Ctypes Ctypesdefs Cop Clight.
Require Import Slice.
Import ListNotations.
Open Scope Z_scope.

(* A common candidate stub: arbitrary permitted write outcomes with silent effects.
   Even two successful short transfers suffice to refute this candidate. *)
Theorem silent_short_write_contract_impossible :
  forall (sem : extcall_sem) sg ge args m m1 m2,
  extcall_properties sem sg ->
  sem ge args m E0 (Vlong (Int64.repr 1)) m1 ->
  sem ge args m E0 (Vlong (Int64.repr 2)) m2 -> False.
Proof.
  intros sem sg ge args m m1 m2 PROPERTIES ONE TWO.
  destruct (@ec_determ sem sg PROPERTIES ge args m E0 (Vlong (Int64.repr 1)) m1 E0 (Vlong (Int64.repr 2)) m2 ONE TWO)
    as [_ DETERMINATE].
  destruct (DETERMINATE eq_refl) as [VALUES _].
  pose proof (f_equal (fun v => match v with
    | Vlong n => Int64.unsigned n | _ => 0 end) VALUES) as CONTRADICTION.
  vm_compute in CONTRADICTION; discriminate.
Qed.

(* The live terminal receiver reads arbitrary bytes. A syscall-count trace
   cannot distinguish two writes to the owned input buffer with the same count. *)
Theorem count_only_read_contract_impossible :
  forall (sem : extcall_sem) sg ge args m m1 m2 t result block offset,
  extcall_properties sem sg ->
  sem ge args m t result m1 -> sem ge args m t result m2 ->
  Mem.load Mint8unsigned m1 block offset = Some (Vint Int.zero) ->
  Mem.load Mint8unsigned m2 block offset = Some (Vint Int.one) -> False.
Proof.
  intros sem sg ge args m m1 m2 t result block offset PROPERTIES A B ZERO ONE.
  destruct (@ec_determ sem sg PROPERTIES ge args m t result m1 t result m2 A B)
    as [_ SAME].
  destruct (SAME eq_refl) as [_ MEMORY]. subst m2.
  rewrite ZERO in ONE.
  pose proof (f_equal (fun v => match v with
    | Some (Vint n) => Int.unsigned n | _ => 99 end) ONE) as CONTRADICTION.
  vm_compute in CONTRADICTION; discriminate.
Qed.

(* The actual first write_all source statement is an ordinary silent sequence
   step. Bare Clight does not include an asynchronous process-loss transition. *)
Theorem write_all_first_step_silent : forall ge e le m t next,
  step2 ge (State f_write_all (fn_body f_write_all) Kstop e le m) t next -> t = E0.
Proof.
  intros ge e le m t next H.
  inversion H; reflexivity.
Qed.

Theorem bare_clight_cannot_emit_initial_loss : forall ge e le m next,
  ~ step2 ge (State f_write_all (fn_body f_write_all) Kstop e le m)
      [Event_annot "process_loss" []] next.
Proof.
  intros ge e le m next H.
  pose proof (write_all_first_step_silent _ _ _ _ _ _ H). discriminate.
Qed.

(* Revised bounded effect vocabulary. This records permitted outcomes; it does
   not assume reporting, containment, a Clight simulation or an OS result. *)
Inductive write_effect :=
| transferred (count : Z)
| failed (error : Z)
| zero_transfer
| blocked
| process_loss.

Definition permitted (remaining : Z) (effect : write_effect) : Prop :=
  match effect with
  | transferred n => 0 < n <= remaining
  | failed error => -(2^31) <= error < 2^31
  | zero_transfer | blocked | process_loss => True
  end.

Inductive write_outcome := complete | failure | suspended | lost.
Inductive write_trace : Z -> Z -> list write_effect -> Z -> write_outcome -> Prop :=
| trace_complete : forall offset, write_trace offset 0 [] offset complete
| trace_transfer : forall offset remaining n tail final outcome,
    0 < n <= remaining ->
    write_trace (offset+n) (remaining-n) tail final outcome ->
    write_trace offset remaining (transferred n :: tail) final outcome
| trace_eintr : forall offset remaining tail final outcome,
    0 < remaining -> write_trace offset remaining tail final outcome ->
    write_trace offset remaining (failed 4 :: tail) final outcome
| trace_error : forall offset remaining error,
    0 < remaining -> -(2^31) <= error < 2^31 -> error <> 4 ->
    write_trace offset remaining [failed error] offset failure
| trace_zero : forall offset remaining,
    0 < remaining -> write_trace offset remaining [zero_transfer] offset failure
| trace_blocked : forall offset remaining,
    0 < remaining -> write_trace offset remaining [blocked] offset suspended
| trace_lost : forall offset remaining,
    0 <= remaining -> write_trace offset remaining [process_loss] offset lost
| trace_loss_after_failure : forall offset remaining effects final,
    write_trace offset remaining effects final failure ->
    write_trace offset remaining (effects ++ [process_loss]) final lost.

Theorem write_trace_bounds : forall offset remaining effects final outcome,
  write_trace offset remaining effects final outcome ->
  0 <= remaining -> offset <= final <= offset + remaining.
Proof.
  intros offset remaining effects final outcome H.
  induction H; intros; try lia.
Qed.

Theorem complete_consumes_owned_region : forall offset remaining effects final,
  write_trace offset remaining effects final complete -> final = offset+remaining.
Proof.
  intros offset remaining effects final H.
  remember complete as outcome eqn:E.
  induction H; try discriminate; try lia.
  - specialize (IHwrite_trace E); lia.
  - apply IHwrite_trace; exact E.
Qed.

Theorem short_eintr_witness : write_trace 0 6
  [transferred 2; failed 4; transferred 1; transferred 3] 6 complete.
Proof.
  eapply trace_transfer; [lia|]. eapply trace_eintr; [lia|].
  eapply trace_transfer; [lia|]. eapply trace_transfer; [lia|]. constructor.
Qed.

Theorem error_after_prefix_witness : write_trace 0 6
  [transferred 2; failed 5] 2 failure.
Proof. eapply trace_transfer; [lia|]. apply trace_error; lia. Qed.

Theorem loss_after_prefix_witness : write_trace 0 6
  [transferred 2; process_loss] 2 lost.
Proof. eapply trace_transfer; [lia|]. apply trace_lost; lia. Qed.

(* Deliberately unfinished native connection. The gate verifies that this proof
   attempt fails at the first missing effect edge, not that a proof exists. *)
Check silent_short_write_contract_impossible.
Print Assumptions silent_short_write_contract_impossible.
Check write_all_first_step_silent.
Print Assumptions write_all_first_step_silent.
Check bare_clight_cannot_emit_initial_loss.
Print Assumptions bare_clight_cannot_emit_initial_loss.
Check write_trace_bounds.
Print Assumptions write_trace_bounds.
Check complete_consumes_owned_region.
Print Assumptions complete_consumes_owned_region.
Check short_eintr_witness.
Print Assumptions short_eintr_witness.
Check error_after_prefix_witness.
Print Assumptions error_after_prefix_witness.
Check loss_after_prefix_witness.
Print Assumptions loss_after_prefix_witness.

Check count_only_read_contract_impossible.
Print Assumptions count_only_read_contract_impossible.

Theorem read_outcomes_inhabited : exists initial m0 m1 b,
  Mem.load Mint8unsigned m0 b 0 = Some (Vint Int.zero) /\
  Mem.load Mint8unsigned m1 b 0 = Some (Vint Int.one) /\
  Mem.store Mint8unsigned initial b 0 (Vint Int.zero) = Some m0 /\
  Mem.store Mint8unsigned initial b 0 (Vint Int.one) = Some m1.
Proof.
  destruct (Mem.alloc Mem.empty 0 9) as [m b] eqn:ALLOC.
  assert (ACCESS : Mem.valid_access m Mint8unsigned b 0 Writable).
  { eapply Mem.valid_access_implies.
    - eapply Mem.valid_access_alloc_same; eauto; simpl; try lia.
      apply Z.divide_1_l.
    - constructor. }
  destruct (Mem.valid_access_store m Mint8unsigned b 0 (Vint Int.zero) ACCESS) as [m0 ZERO].
  destruct (Mem.valid_access_store m Mint8unsigned b 0 (Vint Int.one) ACCESS) as [m1 ONE].
  exists m, m0, m1, b. repeat split; try assumption.
  - exact (Mem.load_store_same _ _ _ _ _ _ ZERO).
  - exact (Mem.load_store_same _ _ _ _ _ _ ONE).
Qed.

Theorem unbounded_interruption_prefix : forall n offset remaining,
  0 < remaining -> write_trace offset remaining
    (repeat (failed 4) n ++ [blocked]) offset suspended.
Proof.
  induction n; intros; simpl.
  - constructor; assumption.
  - constructor; auto.
Qed.
Check read_outcomes_inhabited.
Print Assumptions read_outcomes_inhabited.
Check unbounded_interruption_prefix.
Print Assumptions unbounded_interruption_prefix.
