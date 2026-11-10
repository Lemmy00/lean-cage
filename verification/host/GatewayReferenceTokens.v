(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: A fixed captured token set separates callback roots from this source pool. *)
From Stdlib Require Import List Bool PeanoNat Lia.
From compcert Require Import Values.
Import ListNotations.

Definition gateway_token_key:Type:=(nat*nat)%type.
Definition gateway_token_key_eq:forall(left right:gateway_token_key),{left=right}+{left<>right}.
Proof. decide equality;apply Nat.eq_dec. Defined.
Local Opaque gateway_token_key_eq.

Record gateway_reference_token:Type:={
  gateway_token_namespace:nat;
  gateway_token_serial:nat;
  gateway_token_pointer:Values.val
}.
Definition gateway_token_identity token:gateway_token_key:=
  (gateway_token_namespace token,gateway_token_serial token).
Local Opaque gateway_token_identity.
Definition gateway_token_captured captured key:bool:=
  existsb(fun selected=>if gateway_token_key_eq selected key then true else false)captured.
Definition gateway_token_selected current captured token:bool:=
  Nat.eqb(gateway_token_namespace token)current||gateway_token_captured captured(gateway_token_identity token).

Fixpoint gateway_token_count current captured(pool:list gateway_reference_token)pointer:nat:=
  match pool with
  |[]=>0
  |token::rest=>
    (if gateway_token_selected current captured token then
      if Val.eq(gateway_token_pointer token)pointer then 1 else 0 else 0)+
    gateway_token_count current captured rest pointer
  end.

Fixpoint gateway_token_take key(pool:list gateway_reference_token):
    option(gateway_reference_token*list gateway_reference_token):=
  match pool with
  |[]=>None
  |token::rest=>if gateway_token_key_eq(gateway_token_identity token)key then Some(token,rest)else
    match gateway_token_take key rest with
    |None=>None|Some(selected,remaining)=>Some(selected,token::remaining)
    end
  end.

Inductive gateway_token_action:=
|gateway_token_keep
|gateway_token_mint(token:gateway_reference_token)
|gateway_token_release(key:gateway_token_key)(pointer:Values.val)
|gateway_token_handoff(key:gateway_token_key)(pointer:Values.val)
|gateway_token_unknown.
Inductive gateway_token_error:=
|gateway_token_occupied|gateway_token_missing|gateway_token_mismatch|gateway_token_unclassified.
Inductive gateway_token_status:=
|gateway_tokens_valid(pool:list gateway_reference_token)
|gateway_tokens_invalid(reason:gateway_token_error).

Definition gateway_token_remove key pointer pool:gateway_token_status:=
  match gateway_token_take key pool with
  |None=>gateway_tokens_invalid gateway_token_missing
  |Some(selected,remaining)=>if Val.eq(gateway_token_pointer selected)pointer then gateway_tokens_valid remaining
      else gateway_tokens_invalid gateway_token_mismatch
  end.
Definition gateway_token_apply action status:gateway_token_status:=
  match status with
  |gateway_tokens_invalid reason=>gateway_tokens_invalid reason
  |gateway_tokens_valid pool=>
    match action with
    |gateway_token_keep=>status
    |gateway_token_mint token=>match gateway_token_take(gateway_token_identity token)pool with
      |None=>gateway_tokens_valid(token::pool)|Some _=>gateway_tokens_invalid gateway_token_occupied end
    |gateway_token_release key pointer|gateway_token_handoff key pointer=>gateway_token_remove key pointer pool
    |gateway_token_unknown=>gateway_tokens_invalid gateway_token_unclassified
    end
  end.
Fixpoint gateway_token_batch actions status:gateway_token_status:=
  match actions with[]=>status|action::rest=>gateway_token_batch rest(gateway_token_apply action status)end.

(* Handoff removes a C-owned credit from this projection; it does not claim a
   physical DecRef. Archive/source-place moves keep the token identity unchanged. *)
Definition gateway_token_foreign current captured action:Prop:=
  match action with
  |gateway_token_keep=>True
  |gateway_token_mint token=>gateway_token_selected current captured token=false
  |gateway_token_release key _|gateway_token_handoff key _=>
    fst key<>current /\gateway_token_captured captured key=false
  |gateway_token_unknown=>False
  end.

Lemma gateway_token_selected_current current captured serial pointer:
  gateway_token_selected current captured
    {|gateway_token_namespace:=current;gateway_token_serial:=serial;gateway_token_pointer:=pointer|}=true.
Proof. unfold gateway_token_selected;cbn;rewrite Nat.eqb_refl;reflexivity. Qed.

Lemma gateway_token_take_identity key pool selected remaining:
  gateway_token_take key pool=Some(selected,remaining)->gateway_token_identity selected=key.
Proof.
  revert selected remaining;induction pool as[|head rest IH];intros selected remaining;cbn;[discriminate|].
  destruct(gateway_token_key_eq(gateway_token_identity head)key)as[SAME|DIFFERENT].
  - intro TAKE;inversion TAKE;subst selected remaining;exact SAME.
  - destruct(gateway_token_take key rest)as[[found others]|]eqn:TAIL;[|discriminate].
    intro TAKE;inversion TAKE;subst selected remaining;eapply IH;reflexivity.
Qed.

Lemma gateway_token_take_count current captured key pool selected remaining pointer:
  gateway_token_take key pool=Some(selected,remaining)->
  gateway_token_count current captured pool pointer=
    (if gateway_token_selected current captured selected then
      if Val.eq(gateway_token_pointer selected)pointer then 1 else 0 else 0)+
      gateway_token_count current captured remaining pointer.
Proof.
  revert selected remaining;induction pool as[|head rest IH];intros selected remaining;cbn;[discriminate|].
  destruct(gateway_token_key_eq(gateway_token_identity head)key)as[SAME|DIFFERENT].
  - intro TAKE;inversion TAKE;subst;reflexivity.
  - destruct(gateway_token_take key rest)as[[found others]|]eqn:TAIL;[|discriminate].
    intro TAKE;inversion TAKE;subst;cbn;rewrite(IH _ _ eq_refl);lia.
Qed.

Theorem gateway_token_mint_selected_count current captured pool token next:
  gateway_token_selected current captured token=true->
  gateway_token_apply(gateway_token_mint token)(gateway_tokens_valid pool)=gateway_tokens_valid next->
  gateway_token_count current captured next(gateway_token_pointer token)=
    S(gateway_token_count current captured pool(gateway_token_pointer token)) /\
  (forall other,other<>gateway_token_pointer token->
    gateway_token_count current captured next other=gateway_token_count current captured pool other).
Proof.
  intros SELECTED;unfold gateway_token_apply.
  destruct(gateway_token_take(gateway_token_identity token)pool);[discriminate|].
  intro APPLY;inversion APPLY;subst;cbn;rewrite SELECTED.
  split.
  - destruct(Val.eq(gateway_token_pointer token)(gateway_token_pointer token));[reflexivity|contradiction].
  - intros other DIFFERENT;destruct(Val.eq(gateway_token_pointer token)other);[congruence|reflexivity].
Qed.

Theorem gateway_token_remove_selected_count current captured key pointer pool next:
  (forall selected,gateway_token_identity selected=key->gateway_token_selected current captured selected=true)->
  gateway_token_remove key pointer pool=gateway_tokens_valid next->
  gateway_token_count current captured pool pointer=S(gateway_token_count current captured next pointer) /\
  (forall other,other<>pointer->gateway_token_count current captured next other=gateway_token_count current captured pool other).
Proof.
  intros SELECTED;unfold gateway_token_remove.
  destruct(gateway_token_take key pool)as[[selected remaining]|]eqn:TAKE;[|discriminate].
  destruct(Val.eq(gateway_token_pointer selected)pointer)as[SAME|DIFFERENT];[|discriminate].
  intro APPLY;inversion APPLY;subst next.
  pose proof(gateway_token_take_identity _ _ _ _ TAKE)as ID.
  split.
  - rewrite(gateway_token_take_count _ _ _ _ _ _ _ TAKE),(SELECTED selected ID),SAME.
    destruct(Val.eq pointer pointer);[reflexivity|contradiction].
  - intros other OTHER;rewrite(gateway_token_take_count _ _ _ _ _ _ _ TAKE),(SELECTED selected ID),SAME.
    destruct(Val.eq pointer other);[congruence|reflexivity].
Qed.

Theorem gateway_token_foreign_count current captured action pool next:
  gateway_token_foreign current captured action->
  gateway_token_apply action(gateway_tokens_valid pool)=gateway_tokens_valid next->
  forall pointer,gateway_token_count current captured next pointer=gateway_token_count current captured pool pointer.
Proof.
  destruct action as[|token|key value|key value|];cbn[gateway_token_foreign gateway_token_apply];intros FOREIGN APPLY pointer.
  - inversion APPLY;reflexivity.
  - destruct(gateway_token_take(gateway_token_identity token)pool);[discriminate|].
    inversion APPLY;subst;cbn;rewrite FOREIGN;reflexivity.
  - unfold gateway_token_remove in APPLY.
    destruct(gateway_token_take key pool)as[[selected remaining]|]eqn:TAKE;[|discriminate].
    destruct(Val.eq(gateway_token_pointer selected)value);[|discriminate].
    inversion APPLY;subst next;rewrite(gateway_token_take_count _ _ _ _ _ _ _ TAKE).
    destruct FOREIGN as[OTHER CAPTURED];pose proof(gateway_token_take_identity _ _ _ _ TAKE)as ID.
    assert(NAMESPACE:gateway_token_namespace selected<>current)by(rewrite<-(f_equal fst ID)in OTHER;exact OTHER).
    assert(TEST:Nat.eqb(gateway_token_namespace selected)current=false)by(apply Nat.eqb_neq;exact NAMESPACE).
    unfold gateway_token_selected;rewrite ID,CAPTURED,TEST;reflexivity.
  - unfold gateway_token_remove in APPLY.
    destruct(gateway_token_take key pool)as[[selected remaining]|]eqn:TAKE;[|discriminate].
    destruct(Val.eq(gateway_token_pointer selected)value);[|discriminate].
    inversion APPLY;subst next;rewrite(gateway_token_take_count _ _ _ _ _ _ _ TAKE).
    destruct FOREIGN as[OTHER CAPTURED];pose proof(gateway_token_take_identity _ _ _ _ TAKE)as ID.
    assert(NAMESPACE:gateway_token_namespace selected<>current)by(rewrite<-(f_equal fst ID)in OTHER;exact OTHER).
    assert(TEST:Nat.eqb(gateway_token_namespace selected)current=false)by(apply Nat.eqb_neq;exact NAMESPACE).
    unfold gateway_token_selected;rewrite ID,CAPTURED,TEST;reflexivity.
  - contradiction.
Qed.

Lemma gateway_token_invalid_batch actions reason:
  gateway_token_batch actions(gateway_tokens_invalid reason)=gateway_tokens_invalid reason.
Proof. induction actions;cbn;assumption||reflexivity. Qed.

Theorem gateway_token_foreign_batch_count current captured actions pool next:
  Forall(gateway_token_foreign current captured)actions->
  gateway_token_batch actions(gateway_tokens_valid pool)=gateway_tokens_valid next->
  forall pointer,gateway_token_count current captured next pointer=gateway_token_count current captured pool pointer.
Proof.
  revert pool;induction actions as[|action rest IH];intros pool FOREIGN APPLY pointer;cbn in APPLY.
  - inversion APPLY;reflexivity.
  - inversion FOREIGN;subst.
    change(gateway_token_batch rest(gateway_token_apply action(gateway_tokens_valid pool))=gateway_tokens_valid next)in APPLY.
    destruct(gateway_token_apply action(gateway_tokens_valid pool))as[middle|reason]eqn:STEP.
    + rewrite(IH middle H2 APPLY pointer);eapply gateway_token_foreign_count;eassumption.
    + rewrite gateway_token_invalid_batch in APPLY;discriminate.
Qed.

Lemma gateway_token_batch_app first second status:
  gateway_token_batch(first++second)status=gateway_token_batch second(gateway_token_batch first status).
Proof. revert status;induction first;intros status;cbn;[reflexivity|apply IHfirst]. Qed.

Theorem gateway_token_valid_batch_cut first second pool final:
  gateway_token_batch(first++second)(gateway_tokens_valid pool)=gateway_tokens_valid final->
  exists middle,gateway_token_batch first(gateway_tokens_valid pool)=gateway_tokens_valid middle /\
    gateway_token_batch second(gateway_tokens_valid middle)=gateway_tokens_valid final.
Proof.
  rewrite gateway_token_batch_app.
  destruct(gateway_token_batch first(gateway_tokens_valid pool))as[middle|reason]eqn:PREFIX.
  - intro SUFFIX;exists middle;split;[reflexivity|exact SUFFIX].
  - rewrite gateway_token_invalid_batch;discriminate.
Qed.
