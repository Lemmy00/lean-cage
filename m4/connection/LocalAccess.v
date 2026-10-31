(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-structures.access: Certified local/field accesses for actual source composition. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events
  Globalenvs Errors Ctypes Ctypesdefs Cop Clight.
Require Import Slice Machine ClightSteps StoreSteps.
Import ListNotations.
Open Scope Z_scope.

Definition expression_value ge e le m a v :=
  eval_expr ge e le m a v /\ forall other, eval_expr ge e le m a other -> other = v.
Definition location_value ge e le m a b ofs :=
  eval_lvalue ge e le m a b ofs Full /\
  forall other pos bf, eval_lvalue ge e le m a other pos bf -> other = b /\ pos = ofs /\ bf = Full.

Lemma old_expression_value : forall ge e le m a v,
  evaluated ge e le m a v -> expression_value ge e le m a v.
Proof. intros; split; eauto using evaluated_sound, evaluated_unique. Qed.

Lemma local_location_value : forall ge e le m id ty b,
  e ! id = Some (b,ty) -> location_value ge e le m (Evar id ty) b Ptrofs.zero.
Proof.
  intros; split; [constructor; assumption|]. intros other pos bf LV; inversion LV; subst; try congruence; split; [congruence|auto].
Qed.

Lemma global_location_value : forall (ge : genv) e le m id ty b,
  e ! id = None -> Genv.find_symbol ge id = Some b ->
  location_value ge e le m (Evar id ty) b Ptrofs.zero.
Proof.
  intros; split; [eapply eval_Evar_global; eassumption|].
  intros other pos bf LV; inversion LV; subst; try congruence; split; [congruence|auto].
Qed.

Lemma pointer_location_value : forall ge e le m a ty b ofs,
  expression_value ge e le m a (Vptr b ofs) -> location_value ge e le m (Ederef a ty) b ofs.
Proof.
  intros ge e le m a ty b ofs [REAL UNIQUE]; split; [constructor; exact REAL|].
  intros other pos bf LV; inversion LV; subst.
  match goal with E : eval_expr _ _ _ _ _ _ |- _ => pose proof (UNIQUE _ E) as EQ; inversion EQ; subst end; auto.
Qed.

Lemma struct_location_value : forall ge e le m a field ty b ofs id co att delta,
  expression_value ge e le m a (Vptr b ofs) -> typeof a = Tstruct id att ->
  (genv_cenv ge) ! id = Some co -> field_offset ge field (co_members co) = OK (delta,Full) ->
  location_value ge e le m (Efield a field ty) b (Ptrofs.add ofs (Ptrofs.repr delta)).
Proof.
  intros ge e le m a field ty b ofs id co att delta [REAL UNIQUE] TY CO FIELD.
  split; [eapply eval_Efield_struct; eassumption|].
  intros other pos bf LV; inversion LV; subst; try congruence.
  match goal with E : eval_expr _ _ _ _ _ _ |- _ => pose proof (UNIQUE _ E) as EQ; inversion EQ; subst end.
  assert (id0=id) by congruence; subst id0. assert (co0=co) by congruence; subst co0.
  assert (delta0=delta) by congruence; subst delta0. assert (bf=Full) by congruence; subst bf; auto.
Qed.

Lemma full_deref_unique : forall ty m b ofs v other,
  deref_loc ty m b ofs Full v -> deref_loc ty m b ofs Full other -> other = v.
Proof.
  intros ty m b ofs v other A B; inversion A; inversion B; subst; try congruence.
Qed.

Lemma location_read_value : forall ge e le m a b ofs v,
  location_value ge e le m a b ofs -> deref_loc (typeof a) m b ofs Full v ->
  expression_value ge e le m a v.
Proof.
  intros ge e le m a b ofs v [REAL UNIQUE] LOAD. split; [eapply eval_Elvalue; eassumption|].
  intros other E. inversion REAL; subst; inversion E; subst;
    match goal with L : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
      destruct (UNIQUE _ _ _ L) as [BL [OFF BF]]; subst end;
    eapply full_deref_unique; eassumption.
Qed.

Lemma full_assignment_unique : forall ge ty m b ofs v a c,
  assign_loc ge ty m b ofs Full v a -> assign_loc ge ty m b ofs Full v c -> a=c.
Proof.
  intros ge ty m b ofs v a c A B; inversion A; inversion B; subst; try congruence.
Qed.

Lemma assignment_source_edge : forall ge f a rhs k e le m b ofs v w after,
  location_value ge e le m a b ofs -> expression_value ge e le m rhs v ->
  sem_cast v (typeof rhs) (typeof a) m = Some w ->
  assign_loc ge (typeof a) m b ofs Full w after ->
  store_edge ge (State f (Sassign a rhs) k e le m) (State f Sskip k e le after).
Proof.
  intros ge f a rhs k e le m b ofs v w after [LR LU] [VR VU] CAST STORE.
  split; [exact I|]. split; [eapply step_assign; eassumption|].
  intros t next STEP; inversion STEP; subst;
    try match goal with H : _ = _ \/ _ = _ |- _ => destruct H; discriminate end.
  match goal with L : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
    destruct (LU _ _ _ L) as [BL [OFF BF]]; subst end.
  match goal with E : eval_expr _ _ _ _ _ _ |- _ => pose proof (VU _ E) as EQ; subst end.
  assert (v0=w) by congruence; subst v0.
  split; [reflexivity|]. f_equal. eapply full_assignment_unique; eassumption.
Qed.

Lemma cast_expression_value : forall ge e le m a ty v w,
  expression_value ge e le m a v -> sem_cast v (typeof a) ty m = Some w ->
  expression_value ge e le m (Ecast a ty) w.
Proof.
  intros ge e le m a ty v w [REAL UNIQUE] CAST. split; [econstructor; eassumption|].
  intros other E; inversion E; subst.
  - match goal with EV : eval_expr _ _ _ _ a _ |- _ => pose proof (UNIQUE _ EV) as EQ; subst end; congruence.
  - match goal with L : eval_lvalue _ _ _ _ _ _ _ _ |- _ => inversion L end.
Qed.

Lemma binary_expression_value : forall ge e le m op a c ty v w result,
  expression_value ge e le m a v -> expression_value ge e le m c w ->
  sem_binary_operation ge op v (typeof a) w (typeof c) m = Some result ->
  expression_value ge e le m (Ebinop op a c ty) result.
Proof.
  intros ge e le m op a c ty v w result [AR AU] [BR BU] OP.
  split; [econstructor; eassumption|]. intros other E; inversion E; subst.
  - match goal with EV : eval_expr _ _ _ _ a _ |- _ => pose proof (AU _ EV) as EQ; subst end.
    match goal with EV : eval_expr _ _ _ _ c _ |- _ => pose proof (BU _ EV) as EQ; subst end; congruence.
  - match goal with L : eval_lvalue _ _ _ _ _ _ _ _ |- _ => inversion L end.
Qed.

Lemma certified_set_edge : forall ge f id a k e le m v,
  expression_value ge e le m a v ->
  store_edge ge (State f (Sset id a) k e le m) (State f Sskip k e (PTree.set id v le) m).
Proof.
  intros ge f id a k e le m v [REAL UNIQUE]. split; [exact I|]. split; [constructor; assumption|].
  intros t next STEP; inversion STEP; subst;
    try match goal with H : _ = _ \/ _ = _ |- _ => destruct H; discriminate end.
  match goal with EV : eval_expr _ _ _ _ _ _ |- _ => pose proof (UNIQUE _ EV) as EQ; subst end; auto.
Qed.

Lemma allocation_unique : forall ge vars e m e1 m1 e2 m2,
  alloc_variables ge e m vars e1 m1 -> alloc_variables ge e m vars e2 m2 -> e1=e2 /\ m1=m2.
Proof.
  intros ge vars e m e1 m1 e2 m2 A; revert e2 m2.
  induction A; intros e2' m2' B; inversion B; subst; auto.
  match goal with
  | A : Mem.alloc ?m ?lo ?hi = (?left, ?bl), B : Mem.alloc ?m ?lo ?hi = (?right, ?br) |- _ =>
    assert (EQ : (left,bl) = (right,br)) by congruence; inversion EQ; subst; eauto
  end.
Qed.

Lemma function_entry_unique : forall ge f args m e1 le1 m1 e2 le2 m2,
  function_entry2 ge f args m e1 le1 m1 -> function_entry2 ge f args m e2 le2 m2 ->
  e1=e2 /\ le1=le2 /\ m1=m2.
Proof.
  intros ge f args m e1 le1 m1 e2 le2 m2 A B; inversion A; inversion B; subst.
  match goal with A : alloc_variables _ _ _ _ _ _, B : alloc_variables _ _ _ _ _ _ |- _ =>
    destruct (allocation_unique _ _ _ _ _ _ _ _ A B); subst end.
  repeat split; congruence.
Qed.

Lemma function_entry_source_edge : forall ge f args k m e le after,
  function_entry2 ge f args m e le after ->
  store_edge ge (Callstate (Internal f) args k m) (State f (fn_body f) k e le after).
Proof.
  intros ge f args k m e le after ENTRY. split; [exact I|]. split; [constructor; assumption|].
  intros t next STEP; inversion STEP; subst.
  match goal with E : function_entry2 _ _ _ _ _ _ _ |- _ =>
    destruct (function_entry_unique _ _ _ _ _ _ _ _ _ _ ENTRY E) as [ENV [TEMPS MEM]]; subst end; auto.
Qed.

Lemma local_void_return_edge : forall ge f k e le m after,
  Mem.free_list m (blocks_of_env ge e) = Some after ->
  store_edge ge (State f (Sreturn None) k e le m) (Returnstate Vundef (call_cont k) after).
Proof.
  intros ge f k e le m after FREE. split; [exact I|]. split; [constructor; assumption|].
  intros t next STEP; inversion STEP; subst;
    try match goal with H : _ = _ \/ _ = _ |- _ => destruct H; discriminate end.
  split; [reflexivity|]. f_equal; congruence.
Qed.
