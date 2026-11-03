(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-compiled-reporting.certificate: Use the original bounded iterator through a checked equality. *)
From Stdlib Require Import ZArith Lia.
From compcert Require Import Coqlib Iteration.
Require Import BinaryIteration.
Section ITERATION.
Variables A B : Type.
Variable step : A -> (B+A)%type.
Lemma iter_nat_match : forall count s (access:Acc Plt count),
 PrimIter.iter A B step count s access =
 match @BinaryIteration.run_nat A B step (Pos.to_nat count-1) s with
 | inl result => Some result | inr _ => None end.
Proof.
 intro count;induction count using (well_founded_induction Plt_wf).
 intros s access;destruct access as[ACCESS];cbn[PrimIter.iter].
 destruct(peq count 1)as[EQ|NE].
 - subst count;reflexivity.
 - assert(MORE:(1<count)%positive)by lia.
   assert(NATMORE:(1<Pos.to_nat count)%nat)by(apply(proj1(Pos2Nat.inj_lt 1 count));exact MORE).
   assert(PRED:(Pos.to_nat count-1=S(Pos.to_nat(Pos.pred count)-1))%nat).
   { rewrite Pos2Nat.inj_pred by exact MORE;lia. }
   rewrite PRED;cbn[BinaryIteration.run_nat BinaryIteration.followed].
   destruct(step s)as[result|next];[reflexivity|].
   apply H;apply Ppred_Plt;exact NE.
Qed.

Definition binary_bounded (count:positive) (s:A) : option B :=
 if peq count 1 then None else
 match @BinaryIteration.run A B step (Pos.pred count) s with
 | inl result=>Some result | inr _=>None end.

Lemma iter_binary_exact count s (access:Acc Plt count) :
 PrimIter.iter A B step count s access=binary_bounded count s.
Proof.
 rewrite iter_nat_match;unfold binary_bounded.
 destruct(peq count 1)as[EQ|NE];[subst count;reflexivity|].
 rewrite BinaryIteration.run_exact,Pos2Nat.inj_pred by lia.
 replace (Pos.to_nat count-1)%nat with (Nat.pred(Pos.to_nat count)) by lia.
 reflexivity.
Qed.

Definition iterate (s:A) : option B := binary_bounded PrimIter.num_iterations s.

Theorem iterate_exact s : iterate s=PrimIter.iterate A B step s.
Proof.
 unfold iterate,PrimIter.iterate.
 symmetry;apply iter_binary_exact.
Qed.

Theorem iterate_prop (P:A->Prop) (Q:B->Prop)
 (STEP:forall a:A,P a -> match step a with inl b=>Q b | inr a'=>P a' end) :
 forall a b,iterate a=Some b -> P a -> Q b.
Proof.
 intros a b RUN PRE;rewrite iterate_exact in RUN.
 eapply PrimIter.iterate_prop;[exact STEP|exact RUN|exact PRE].
Qed.
End ITERATION.
Global Opaque iterate.
