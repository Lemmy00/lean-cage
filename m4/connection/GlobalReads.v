(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-library.source: Actual global reads needed by reporting routines. *)
From Coq Require Import List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events
  Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps.
Import ListNotations.

Lemma global_read_evaluation : forall (ge : genv) le m id ty b chunk value,
  Genv.find_symbol ge id = Some b -> access_mode ty = By_value chunk ->
  Mem.loadv chunk m (Vptr b Ptrofs.zero) = Some value ->
  eval_expr ge empty_env le m (Evar id ty) value.
Proof.
  intros. eapply eval_Elvalue.
  - apply eval_Evar_global; [reflexivity|eassumption].
  - eapply deref_loc_value; eassumption.
Qed.

Lemma global_read_unique : forall (ge : genv) le m id ty b chunk value,
  Genv.find_symbol ge id = Some b -> access_mode ty = By_value chunk ->
  Mem.loadv chunk m (Vptr b Ptrofs.zero) = Some value ->
  forall other, eval_expr ge empty_env le m (Evar id ty) other -> other = value.
Proof.
  intros ge le m id ty b chunk value SYMBOL MODE LOAD other EV.
  inversion EV; subst.
  match goal with H : eval_lvalue _ _ _ _ _ _ _ _ |- _ => inversion H; subst; cbn in * end;
    try discriminate.
  assert (loc = b) by congruence; subst loc.
  match goal with H : deref_loc _ _ _ _ _ _ |- _ => inversion H; subst end.
  - match goal with H : access_mode _ = By_value _ |- _ => rewrite MODE in H; inversion H; subst end.
    cbn in *; congruence.
  - congruence.
  - congruence.
Qed.

Lemma edge_global_read : forall (ge : genv) f dst id ty b chunk value k le m,
  Genv.find_symbol ge id = Some b -> access_mode ty = By_value chunk ->
  Mem.loadv chunk m (Vptr b Ptrofs.zero) = Some value ->
  edge ge (State f (Sset dst (Evar id ty)) k empty_env le m)
    (State f Sskip k empty_env (PTree.set dst value le) m).
Proof.
  intros ge f dst id ty b chunk value k le m SYMBOL MODE LOAD.
  split; [exact I|]. split.
  - apply step_set. eapply global_read_evaluation; eassumption.
  - split; [reflexivity|]. intros t other STEP; inversion STEP; subst;
      try match goal with H : _ = _ \/ _ = _ |- _ => destruct H; discriminate end.
    match goal with H : eval_expr _ _ _ _ _ _ |- _ =>
      pose proof (global_read_unique _ _ _ _ _ _ _ _ SYMBOL MODE LOAD _ H) as SAME end.
    subst; auto.
Qed.

Lemma bool_int_cast : forall value m,
  sem_cast (Val.of_bool value) tint tint m = Some (Val.of_bool value).
Proof. destruct value; reflexivity. Qed.
