(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-callers.control: Actual caller steps using certified typed expressions. *)
From Coq Require Import List.
From compcert Require Import Coqlib Maps AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess.
Import ListNotations.

Definition argument_values ge e le m args types values :=
  eval_exprlist ge e le m args types values /\
  forall other, eval_exprlist ge e le m args types other -> other = values.
Lemma no_argument_values : forall ge e le m, argument_values ge e le m [] [] [].
Proof. intros; split; [constructor|intros other EV; inversion EV; reflexivity]. Qed.
Lemma cons_argument_values : forall ge e le m a args ty types v w values,
  expression_value ge e le m a v -> sem_cast v (typeof a) ty m = Some w ->
  argument_values ge e le m args types values ->
  argument_values ge e le m (a::args) (ty::types) (w::values).
Proof.
  intros ge e le m a args ty types v w values [REAL UNIQUE] CAST [TAIL TAILUNIQUE].
  split; [econstructor; eassumption|]. intros other EV; inversion EV; subst.
  match goal with E : eval_expr _ _ _ _ _ _ |- _ => pose proof (UNIQUE _ E) as EQ; subst end.
  f_equal; [congruence|eapply TAILUNIQUE; eassumption].
Qed.

Lemma certified_call_edge : forall ge f opt a args k e le m types ty cc vf values fd,
  classify_fun (typeof a) = fun_case_f types ty cc ->
  expression_value ge e le m a vf -> argument_values ge e le m args types values ->
  Genv.find_funct ge vf = Some fd -> type_of_fundef fd = Tfunction types ty cc ->
  store_edge ge (State f (Scall opt a args) k e le m)
    (Callstate fd values (Kcall opt f e le k) m).
Proof.
  intros ge f opt a args k e le m types ty cc vf values fd CLASS [FR FU] [AR AU] FIND TYPE.
  split; [exact I|]. split; [eapply step_call; eassumption|].
  intros t other STEP; inversion STEP; subst;
    try match goal with H : _ = _ \/ _ = _ |- _ => destruct H; discriminate end.
  match goal with H : classify_fun _ = _ |- _ => rewrite CLASS in H; inversion H; subst end.
  match goal with E : eval_expr _ _ _ _ _ _ |- _ => pose proof (FU _ E) as EQ; subst end.
  match goal with E : eval_exprlist _ _ _ _ _ _ _ |- _ => pose proof (AU _ E) as EQ; subst end.
  split; [reflexivity|]. f_equal; congruence.
Qed.

Lemma certified_if_edge : forall ge f a yes no k e le m v b,
  expression_value ge e le m a v -> bool_val v (typeof a) m = Some b ->
  store_edge ge (State f (Sifthenelse a yes no) k e le m)
    (State f (if b then yes else no) k e le m).
Proof.
  intros ge f a yes no k e le m v b [REAL UNIQUE] BOOL.
  split; [exact I|]. split; [eapply step_ifthenelse; eassumption|].
  intros t other STEP; inversion STEP; subst;
    try match goal with H : _ = _ \/ _ = _ |- _ => destruct H; discriminate end.
  match goal with E : eval_expr _ _ _ _ _ _ |- _ => pose proof (UNIQUE _ E) as EQ; subst end.
  assert (b0=b) by congruence; subst; auto.
Qed.

Lemma certified_local_return_edge : forall ge f a k e le m v w after,
  expression_value ge e le m a v -> sem_cast v (typeof a) (fn_return f) m = Some w ->
  Mem.free_list m (blocks_of_env ge e) = Some after ->
  store_edge ge (State f (Sreturn (Some a)) k e le m) (Returnstate w (call_cont k) after).
Proof.
  intros ge f a k e le m v w after [REAL UNIQUE] CAST FREE.
  split; [exact I|]. split; [eapply step_return_1; eassumption|].
  intros t other STEP; inversion STEP; subst;
    try match goal with H : _ = _ \/ _ = _ |- _ => destruct H; discriminate end.
  match goal with E : eval_expr _ _ _ _ _ _ |- _ => pose proof (UNIQUE _ E) as EQ; subst end.
  split; [reflexivity|]. f_equal; congruence.
Qed.
