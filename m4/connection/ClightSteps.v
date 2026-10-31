(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-effects.writeall: Checked symbolic execution of the actual Clight AST. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events
  Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import IO Machine.
Import ListNotations.
Open Scope Z_scope.

(* A proof-producing evaluator for the expression forms used by write_all.
   The soundness AND uniqueness lemmas below connect certificates to every
   actual Clight evaluation, rather than defining a replacement C semantics. *)
Inductive evaluated (ge : genv) (e : env) (le : temp_env) (m : mem) : expr -> val -> Prop :=
| value_int : forall i ty, evaluated ge e le m (Econst_int i ty) (Vint i)
| value_temp : forall id ty v, le ! id = Some v ->
    evaluated ge e le m (Etempvar id ty) v
| value_function : forall id ty b,
    e ! id = None -> Genv.find_symbol ge id = Some b ->
    access_mode ty = By_reference ->
    evaluated ge e le m (Evar id ty) (Vptr b Ptrofs.zero)
| value_load : forall a ty b ofs chunk v,
    evaluated ge e le m a (Vptr b ofs) ->
    access_mode ty = By_value chunk ->
    Mem.loadv chunk m (Vptr b ofs) = Some v ->
    evaluated ge e le m (Ederef a ty) v
| value_unary : forall op a ty v w,
    evaluated ge e le m a v -> sem_unary_operation op v (typeof a) m = Some w ->
    evaluated ge e le m (Eunop op a ty) w
| value_binary : forall op a b ty v w result,
    evaluated ge e le m a v -> evaluated ge e le m b w ->
    sem_binary_operation ge op v (typeof a) w (typeof b) m = Some result ->
    evaluated ge e le m (Ebinop op a b ty) result
| value_cast : forall a ty v w,
    evaluated ge e le m a v -> sem_cast v (typeof a) ty m = Some w ->
    evaluated ge e le m (Ecast a ty) w.

Lemma evaluated_sound : forall ge e le m a v,
  evaluated ge e le m a v -> eval_expr ge e le m a v.
Proof.
  intros ge e le m a v H; induction H; try solve [econstructor; eauto].
  - eapply eval_Elvalue; [eapply eval_Evar_global; eauto|].
    apply deref_loc_reference; assumption.
  - eapply eval_Elvalue; [eapply eval_Ederef; eauto|].
    eapply deref_loc_value; eauto.
Qed.

Lemma evaluated_unique : forall ge e le m a v,
  evaluated ge e le m a v -> forall w, eval_expr ge e le m a w -> w = v.
Proof.
  intros ge e le m a v H; induction H; intros other EV; inversion EV; subst;
    try match goal with H : eval_lvalue _ _ _ _ _ _ _ _ |- _ => inversion H; subst end;
    try congruence.
  all: repeat match goal with
    | IH : forall w, eval_expr ?ge ?e ?le ?m ?a w -> w = ?v,
      H : eval_expr ?ge ?e ?le ?m ?a ?w |- _ =>
        let EQ := fresh "EQ" in pose proof (IH _ H) as EQ; clear H; subst
    end; try congruence.
  all: repeat match goal with H : Vptr _ _ = Vptr _ _ |- _ => inversion H; clear H; subst end.
  all: match goal with H : deref_loc _ _ _ _ _ _ |- _ => inversion H; subst; cbn in * end.
  all: try congruence.
  match goal with A : access_mode _ = By_value _, B : access_mode _ = By_value _ |- _ =>
    rewrite A in B; inversion B; subst; congruence end.
Qed.

Inductive arguments (ge : genv) (e : env) (le : temp_env) (m : mem) :
    list expr -> list type -> list val -> Prop :=
| arguments_nil : arguments ge e le m [] [] []
| arguments_cons : forall a rest ty types v w values,
    evaluated ge e le m a v -> sem_cast v (typeof a) ty m = Some w ->
    arguments ge e le m rest types values ->
    arguments ge e le m (a :: rest) (ty :: types) (w :: values).

Lemma arguments_sound : forall ge e le m args types values,
  arguments ge e le m args types values -> eval_exprlist ge e le m args types values.
Proof. intros; induction H; econstructor; eauto using evaluated_sound. Qed.

Lemma arguments_unique : forall ge e le m args types values,
  arguments ge e le m args types values ->
  forall other, eval_exprlist ge e le m args types other -> other = values.
Proof.
  intros ge e le m args types values H; induction H; intros other EV; inversion EV; subst; auto.
  match goal with EV : eval_expr _ _ _ _ _ _ |- _ =>
    pose proof (evaluated_unique _ _ _ _ _ _ H _ EV); subst end.
  f_equal; [congruence|eauto].
Qed.

(* Each certificate has a defined real step and determines every real step
   from the source. Memory is unchanged along these purely internal paths. *)
Definition edge (ge : genv) (s next : Clight.state) : Prop :=
  internal_state s /\ step2 ge s E0 next /\ memory_of next = memory_of s /\
  (forall t other, step2 ge s t other -> t = E0 /\ other = next).

Inductive path (ge : genv) : Clight.state -> Clight.state -> Prop :=
| path_done : forall s, path ge s s
| path_next : forall s mid last, edge ge s mid -> path ge mid last -> path ge s last.

Lemma path_memory : forall ge s last, path ge s last -> memory_of last = memory_of s.
Proof. intros ge s last H; induction H; auto. destruct H as [_ [_ [M _]]]; congruence. Qed.

Lemma path_step : forall ge s last t next,
  path ge s last -> s <> last -> step2 ge s t next ->
  t = E0 /\ path ge next last.
Proof.
  intros ge s last t next P NE S; inversion P; subst; [contradiction|].
  destruct H as [_ [_ [_ UNIQUE]]]. destruct (UNIQUE _ _ S); subst; auto.
Qed.

Lemma path_progress : forall ge s last,
  path ge s last -> s <> last -> exists next, edge ge s next /\ path ge next last.
Proof. intros ge s last H NE; inversion H; subst; [contradiction|eauto]. Qed.

Lemma edge_set : forall ge f id a k e le m v,
  evaluated ge e le m a v ->
  edge ge (State f (Sset id a) k e le m)
    (State f Sskip k e (PTree.set id v le) m).
Proof.
  intros; split; [exact I|]. split; [apply step_set; eauto using evaluated_sound|].
  split; [reflexivity|]. intros t other S; inversion S; subst;
    try match goal with H : _ = _ \/ _ = _ |- _ => destruct H; discriminate end.
  match goal with EV : eval_expr _ _ _ _ _ _ |- _ =>
    pose proof (evaluated_unique _ _ _ _ _ _ H _ EV); subst end; auto.
Qed.

Lemma edge_if : forall ge f a yes no k e le m v b,
  evaluated ge e le m a v -> bool_val v (typeof a) m = Some b ->
  edge ge (State f (Sifthenelse a yes no) k e le m)
    (State f (if b then yes else no) k e le m).
Proof.
  intros; split; [exact I|]. split; [eapply step_ifthenelse; eauto using evaluated_sound|].
  split; [reflexivity|]. intros t other S; inversion S; subst;
    try match goal with H : _ = _ \/ _ = _ |- _ => destruct H; discriminate end.
  match goal with EV : eval_expr _ _ _ _ _ _ |- _ =>
    pose proof (evaluated_unique _ _ _ _ _ _ H _ EV); subst end.
  assert (b0 = b) by congruence; subst; auto.
Qed.

Lemma edge_call : forall ge f opt a args k e le m types ty cc vf values fd,
  classify_fun (typeof a) = fun_case_f types ty cc ->
  evaluated ge e le m a vf -> arguments ge e le m args types values ->
  Genv.find_funct ge vf = Some fd -> type_of_fundef fd = Tfunction types ty cc ->
  edge ge (State f (Scall opt a args) k e le m)
    (Callstate fd values (Kcall opt f e le k) m).
Proof.
  intros; split; [exact I|]. split; [eapply step_call; eauto using evaluated_sound, arguments_sound|].
  split; [reflexivity|]. intros t other S; inversion S; subst;
    try match goal with H : _ = _ \/ _ = _ |- _ => destruct H; discriminate end.
  match goal with A : classify_fun _ = _, B : classify_fun _ = _ |- _ => rewrite A in B; inversion B; subst end.
  match goal with EV : eval_expr _ _ _ _ _ _ |- _ =>
    pose proof (evaluated_unique _ _ _ _ _ _ H0 _ EV); subst end.
  match goal with EV : eval_exprlist _ _ _ _ _ _ _ |- _ =>
    pose proof (arguments_unique _ _ _ _ _ _ _ H1 _ EV); subst end.
  split; [reflexivity|]. f_equal; congruence.
Qed.

Lemma edge_return : forall ge f a k le m v w,
  evaluated ge empty_env le m a v -> sem_cast v (typeof a) (fn_return f) m = Some w ->
  edge ge (State f (Sreturn (Some a)) k empty_env le m)
    (Returnstate w (call_cont k) m).
Proof.
  intros; split; [exact I|]. split.
  - eapply step_return_1; eauto using evaluated_sound.
  - split; [reflexivity|]. intros t other S; inversion S; subst;
    try match goal with H : _ = _ \/ _ = _ |- _ => destruct H; discriminate end.
    match goal with EV : eval_expr _ _ _ _ _ _ |- _ =>
      pose proof (evaluated_unique _ _ _ _ _ _ H _ EV); subst end.
    match goal with H : Mem.free_list _ (blocks_of_env _ empty_env) = _ |- _ => simpl in H; inversion H; subst end.
    split; [reflexivity|]. f_equal; congruence.
Qed.

(* Structural steps are checked by constructor and inversion, without an
   unproved interpreter or tactic oracle. *)
Ltac structural_edge :=
  split; [exact I|]; split; [solve [econstructor; eauto]|];
  split; [reflexivity|]; intros ? ? S; inversion S; subst; simpl in *;
  try contradiction; auto;
  match goal with H : _ = _ \/ _ = _ |- _ => destruct H; discriminate end.

Lemma edge_seq : forall ge f a b k e le m,
  edge ge (State f (Ssequence a b) k e le m) (State f a (Kseq b k) e le m).
Proof. intros; structural_edge. Qed.
Lemma edge_skip_seq : forall ge f a k e le m,
  edge ge (State f Sskip (Kseq a k) e le m) (State f a k e le m).
Proof. intros; structural_edge. Qed.
Lemma edge_continue_seq : forall ge f a k e le m,
  edge ge (State f Scontinue (Kseq a k) e le m) (State f Scontinue k e le m).
Proof. intros; structural_edge. Qed.
Lemma edge_break_seq : forall ge f a k e le m,
  edge ge (State f Sbreak (Kseq a k) e le m) (State f Sbreak k e le m).
Proof. intros; structural_edge. Qed.
Lemma edge_loop : forall ge f a b k e le m,
  edge ge (State f (Sloop a b) k e le m) (State f a (Kloop1 a b k) e le m).
Proof. intros; structural_edge. Qed.
Lemma edge_skip_loop1 : forall ge f a b k e le m,
  edge ge (State f Sskip (Kloop1 a b k) e le m) (State f b (Kloop2 a b k) e le m).
Proof. intros; structural_edge. Qed.
Lemma edge_continue_loop1 : forall ge f a b k e le m,
  edge ge (State f Scontinue (Kloop1 a b k) e le m) (State f b (Kloop2 a b k) e le m).
Proof. intros; structural_edge. Qed.
Lemma edge_break_loop1 : forall ge f a b k e le m,
  edge ge (State f Sbreak (Kloop1 a b k) e le m) (State f Sskip k e le m).
Proof. intros; structural_edge. Qed.
Lemma edge_skip_loop2 : forall ge f a b k e le m,
  edge ge (State f Sskip (Kloop2 a b k) e le m) (State f (Sloop a b) k e le m).
Proof. intros; structural_edge. Qed.
Lemma edge_returnstate : forall ge v opt f e le k m,
  edge ge (Returnstate v (Kcall opt f e le k) m)
    (State f Sskip k e (set_opttemp opt v le) m).
Proof. intros; structural_edge. Qed.

Lemma path_trans : forall ge a b c, path ge a b -> path ge b c -> path ge a c.
Proof. intros ge a b c AB BC; induction AB; eauto using path_next. Qed.

Lemma machine_edge_cases : forall ge cell s next ev target,
  edge ge s next -> Machine.step ge cell (live s) ev target ->
  (ev = source_step E0 /\ target = live next) \/
  (ev = loss_step /\ target = dead (memory_of s)).
Proof.
  intros ge cell s next ev target [IN [REAL [MEM UNIQUE]]] STEP.
  inversion STEP; subst; try contradiction.
  - destruct (UNIQUE _ _ H1); subst; auto.
  - match goal with B : boundary _ _ _ |- _ => inversion B; subst end. contradiction.
  - auto.
Qed.

Lemma path_machine_steps : forall ge cell s last,
  path ge s last -> exists events, steps ge cell (live s) events (live last).
Proof.
  intros ge cell s last P; induction P.
  - exists []; constructor.
  - destruct IHP as [events RUN]. exists (source_step E0 :: events).
    destruct H as [IN [S _]]. econstructor; [apply internal; eassumption|exact RUN].
Qed.

Lemma path_source_steps : forall ge cell a b,
  path ge a b -> exists n, steps ge cell (live a) (repeat (source_step E0) n) (live b).
Proof.
  intros ge cell a b P; induction P.
  - exists 0%nat; constructor.
  - destruct IHP as [n RUN]. exists (S n). cbn. econstructor; [|exact RUN].
    destruct H as [IN [STEP _]]. apply internal; assumption.
Qed.
