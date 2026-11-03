(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-compiled-reporting.certificate: Replay the same bounded iteration without proof-dependent recursion. *)
From Stdlib Require Import ZArith List Lia.

Section ITERATION.
Variables A B : Type.
Variable step : A -> (B+A)%type.

Definition followed (first : (B+A)%type) (next : A -> (B+A)%type) :=
 match first with inl result=>inl result | inr state=>next state end.

Fixpoint run (count:positive) (state:A) : (B+A)%type :=
 match count with
 | xH => step state
 | xO half => followed(run half state)(run half)
 | xI half => followed(followed(run half state)(run half))step
 end.

Fixpoint run_nat (count:nat) (state:A) : (B+A)%type :=
 match count with
 | O => inr state
 | S rest => followed(step state)(run_nat rest)
 end.

Lemma followed_assoc first second third :
 followed(followed first second)third=
 followed first(fun state=>followed(second state)third).
Proof. destruct first;reflexivity. Qed.

Lemma run_nat_app first rest state :
 run_nat(first+rest)state=followed(run_nat first state)(run_nat rest).
Proof.
 revert state;induction first;intro state;[reflexivity|].
 cbn[Nat.add run_nat];destruct(step state)as[result|next];cbn[followed];[reflexivity|apply IHfirst].
Qed.

Theorem run_exact count state : run count state=run_nat(Pos.to_nat count)state.
Proof.
 revert state;induction count;intro state;cbn[run].
 - replace (Pos.to_nat(xI count)) with (Pos.to_nat count+Pos.to_nat count+1)%nat
     by(rewrite Pos2Nat.inj_xI;lia).
   rewrite run_nat_app,run_nat_app,<-IHcount.
   unfold followed;destruct(run count state)as[result|next];[reflexivity|].
   rewrite <-IHcount;destruct(run count next)as[result2|next2];cbn[run_nat followed];[reflexivity|].
   destruct(step next2);reflexivity.
 - replace (Pos.to_nat(xO count)) with (Pos.to_nat count+Pos.to_nat count)%nat
     by(rewrite Pos2Nat.inj_xO;lia).
   rewrite run_nat_app,<-IHcount;unfold followed;destruct(run count state);[reflexivity|].
   rewrite <-IHcount;reflexivity.
 - change(step state=run_nat 1 state). cbn[run_nat followed];destruct(step state);reflexivity.
Qed.
End ITERATION.
