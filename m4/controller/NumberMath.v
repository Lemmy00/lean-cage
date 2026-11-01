(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.decimal: Exact source parsing, memory behavior and interruption. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Integers.
Open Scope Z_scope.
Import ListNotations.
Definition decimal_max := 18446744073709551615.
Definition decimal_digit b := Byte.unsigned b - 48.
Definition decimal_digit_ok b := 48 <= Byte.unsigned b <= 57.
Definition decimal_step acc b :=
 if (48 <=? Byte.unsigned b) && (Byte.unsigned b <=? 57) then
   if acc <=? (decimal_max - decimal_digit b) / 10
   then Some (acc*10+decimal_digit b) else None
 else None.
Fixpoint decimal_loop acc bytes := match bytes with
 | [] => Some acc
 | b::tail => match decimal_step acc b with Some next => decimal_loop next tail | None => None end
 end.
Definition decimal_number bytes := match bytes with [] => None | _ => decimal_loop 0 bytes end.
Fixpoint decimal_fold acc bytes := match bytes with
 | [] => acc | b::tail => decimal_fold (acc*10+decimal_digit b) tail end.
Lemma decimal_threshold acc digit : acc <= (decimal_max-digit)/10 <-> acc*10+digit <= decimal_max.
Proof.
 pose proof (Z.div_mod (decimal_max-digit) 10 ltac:(lia)) as DIV.
 pose proof (Z.mod_pos_bound (decimal_max-digit) 10 ltac:(lia)) as REM.
 nia.
Qed.
Lemma decimal_step_exact acc b next :
 decimal_step acc b = Some next <->
 decimal_digit_ok b /\ acc*10+decimal_digit b <= decimal_max /\ next=acc*10+decimal_digit b.
Proof.
 unfold decimal_step,decimal_digit_ok.
 destruct ((48 <=? Byte.unsigned b) && (Byte.unsigned b <=? 57)) eqn:DIG.
 - apply andb_true_iff in DIG; destruct DIG as [LOW HIGH].
   apply Z.leb_le in LOW;apply Z.leb_le in HIGH.
   destruct (acc <=? (decimal_max-decimal_digit b)/10) eqn:SIZE.
   + apply Z.leb_le in SIZE;apply decimal_threshold in SIZE.
     split;intros H;[inversion H;subst;auto|destruct H as [_ [_ ->]];reflexivity].
   + apply Z.leb_gt in SIZE;split;[discriminate|].
     intros [_ [BOUND _]];apply decimal_threshold in BOUND;lia.
 - split;[discriminate|]. intros [BOUND _].
   assert (E : (48 <=? Byte.unsigned b) && (Byte.unsigned b <=? 57)=true).
   { apply andb_true_iff;split;apply Z.leb_le;tauto. } congruence.
Qed.
Lemma decimal_step_nonnegative acc b next :
 0<=acc -> decimal_step acc b=Some next -> 0<=next<=decimal_max.
Proof. intros ACC STEP;apply decimal_step_exact in STEP;unfold decimal_digit_ok,decimal_digit in *;nia. Qed.
Lemma decimal_fold_increasing acc bytes :
 0<=acc -> Forall decimal_digit_ok bytes -> acc <= decimal_fold acc bytes.
Proof.
 revert acc;induction bytes as [|b bytes IH];intros acc NONNEG DIGITS; [simpl;lia|].
 inversion DIGITS as [|? ? DIG REST];subst.
 cbn [decimal_fold]; unfold decimal_digit_ok,decimal_digit in DIG.
 specialize (IH (acc*10+decimal_digit b) ltac:(unfold decimal_digit;lia) REST).
 unfold decimal_digit in *;lia.
Qed.
Lemma decimal_loop_exact bytes acc : 0<=acc<=decimal_max ->
 (decimal_loop acc bytes = Some (decimal_fold acc bytes) <->
   Forall decimal_digit_ok bytes /\ decimal_fold acc bytes <= decimal_max).
Proof.
 revert acc;induction bytes as [|b bytes IH];intros acc ACC.
 - cbn;split;intros;[split;[constructor|lia]|reflexivity].
 - cbn [decimal_loop decimal_fold]. destruct (decimal_step acc b) as [next|] eqn:STEP.
   + apply decimal_step_exact in STEP; destruct STEP as [DIG [BOUND NEXT]];subst next.
     assert (NONNEG : 0<=acc*10+decimal_digit b) by (unfold decimal_digit_ok,decimal_digit in *;lia).
     rewrite IH by lia;split;intros [D B];split;try assumption.
     * constructor;assumption.
     * inversion D;assumption.
   + split;[discriminate|]. intros [DIGITS FINAL].
     inversion DIGITS as [|? ? DIG REST];subst.
     assert (NONNEG : 0<=acc*10+decimal_digit b) by (unfold decimal_digit_ok,decimal_digit in *;lia).
     pose proof (decimal_fold_increasing (acc*10+decimal_digit b) bytes NONNEG REST) as LOW.
     assert (SOME : decimal_step acc b=Some(acc*10+decimal_digit b)).
     { apply decimal_step_exact;split;[exact DIG|]. split;[lia|reflexivity]. } congruence.
Qed.
Lemma decimal_loop_some bytes acc value :
 0 <= acc <= decimal_max -> decimal_loop acc bytes = Some value ->
 value=decimal_fold acc bytes /\ Forall decimal_digit_ok bytes /\ 0<=value<=decimal_max.
Proof.
 revert acc value;induction bytes as [|b bytes IH];intros acc value ACC RUN.
 - cbn in RUN;inversion RUN;subst;split;[reflexivity|]. split;[constructor|exact ACC].
 - cbn [decimal_loop] in RUN;destruct (decimal_step acc b) as [next|] eqn:STEP;[|discriminate].
   pose proof (decimal_step_nonnegative _ _ _ (proj1 ACC) STEP) as BOUND.
   apply decimal_step_exact in STEP; destruct STEP as [DIG [LIMIT NEXT]];subst next.
   destruct (IH _ _ BOUND RUN) as [VALUE [DIGITS RANGE]].
   split;[exact VALUE|]. split;[constructor;assumption|assumption].
Qed.
Theorem decimal_number_exact bytes value :
 decimal_number bytes = Some value <->
 bytes<>[] /\ Forall decimal_digit_ok bytes /\ value=decimal_fold 0 bytes /\ 0<=value<=decimal_max.
Proof.
 destruct bytes as [|b bytes];[cbn;split;[discriminate|tauto]|].
 unfold decimal_number;split.
 - intros RUN; destruct (decimal_loop_some (b::bytes) 0 value ltac:(unfold decimal_max;lia) RUN)
   as [VALUE [DIGITS RANGE]]. repeat split;try discriminate;tauto.
 - intros [_ [DIGITS [VALUE RANGE]]];subst value.
   apply (proj2 (decimal_loop_exact (b::bytes) 0 ltac:(unfold decimal_max;lia))).
   split;[exact DIGITS|exact (proj2 RANGE)].
Qed.
Definition decimal_bytes := map Byte.repr.
Example decimal_maximum_accepted : decimal_number
 (decimal_bytes [49;56;52;52;54;55;52;52;48;55;51;55;48;57;53;53;49;54;49;53])=Some decimal_max.
Proof. vm_compute;reflexivity. Qed.
Example decimal_overflow_rejected : decimal_number
 (decimal_bytes [49;56;52;52;54;55;52;52;48;55;51;55;48;57;53;53;49;54;49;54])=None.
Proof. vm_compute;reflexivity. Qed.
Example decimal_leading_zeros : decimal_number (decimal_bytes [48;48;48;52;50])=Some 42.
Proof. vm_compute;reflexivity. Qed.
Example decimal_invalid_bytes :
 decimal_number []=None /\ decimal_number (decimal_bytes [45;49])=None /\
 decimal_number (decimal_bytes [43;49])=None /\ decimal_number (decimal_bytes [49;128])=None /\
 decimal_number (decimal_bytes [32;49])=None /\ decimal_number (decimal_bytes [49;58])=None.
Proof. vm_compute;repeat split;reflexivity. Qed.
