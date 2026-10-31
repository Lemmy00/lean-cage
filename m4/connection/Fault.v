(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-library.source: Complete maintained fault selector under owned strings. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events
  Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Slice IO Machine ClightSteps WriteAll Deterministic StoreSteps GlobalReads
  Library LibraryMachine LibraryPreservation LibraryControl.
Import ListNotations.
Open Scope Z_scope.

Definition fault_symbols (ge : genv) := exists b,
  Genv.find_symbol ge _strcmp = Some b /\ Genv.find_funct ge (Vptr b Ptrofs.zero) = Some strcmp_definition.
Definition mode_pointer (ge : genv) m mode := exists b,
  Genv.find_symbol ge _mode = Some b /\
  Mem.loadv Mint64 m (Vptr b Ptrofs.zero) = Some (address_value mode).
Definition fault_input ge m mode name xs ys :=
  mode_pointer ge m mode /\ c_string m mode xs /\ c_string m name ys.
Definition fault_value xs ys :=
  match compare_bytes xs ys with Eq => Vint Int.one | _ => Vint Int.zero end.
Definition fault_initial name k m := Callstate (Internal f_fault) [address_value name] k m.
Definition fault_return := Sreturn (Some
  (Ebinop Oeq (Etempvar _t'1 tint) (Econst_int Int.zero tint) tint)).
Definition fault_call := Scall (Some _t'1)
  (Evar _strcmp (Tfunction [tptr tschar; tptr tschar] tint cc_default))
  [Etempvar _t'2 (tptr tschar); Etempvar _name (tptr tschar)].
Definition fault_env name := PTree.set _name (address_value name) (create_undef_temps (fn_temps f_fault)).
Definition fault_loaded_env mode name := PTree.set _t'2 (address_value mode) (fault_env name).
Definition fault_cont mode name k :=
  Kcall (Some _t'1) f_fault empty_env (fault_loaded_env mode name) (Kseq fault_return k).
Definition fault_compare_state mode name k m :=
  Callstate strcmp_definition [address_value mode; address_value name] (fault_cont mode name k) m.

Theorem actual_fault_symbols : fault_symbols (Clight.globalenv Slice.prog).
Proof. eexists; split; vm_compute; reflexivity. Qed.

Theorem source_fault_body : fn_body f_fault =
  Ssequence (Ssequence (Sset _t'2 (Evar _mode (tptr tschar))) fault_call) fault_return.
Proof. reflexivity. Qed.

Lemma fault_entry : forall ge name k m,
  edge ge (fault_initial name k m)
    (State f_fault (fn_body f_fault) k empty_env (fault_env name) m).
Proof.
  intros. split; [exact I|]. split.
  - apply step_internal_function. constructor.
    + constructor.
    + repeat constructor; simpl; tauto.
    + unfold list_disjoint, var_names; cbn; intros a b [A|A] [B|[B|B]];
        try contradiction; subst; discriminate.
    + constructor.
    + reflexivity.
  - split; [reflexivity|]. intros t other STEP; inversion STEP; subst.
    match goal with H : function_entry2 _ _ _ _ _ _ _ |- _ => inversion H; subst end.
    match goal with H : alloc_variables _ _ _ _ _ _ |- _ => inversion H; subst end.
    match goal with H : bind_parameter_temps _ _ _ = _ |- _ => cbn in H; inversion H; subst end.
    auto.
Qed.

Ltac fault_next := eapply store_next; [reflexivity|apply unchanged_store_edge|].
Ltac fault_route := fault_next; [WriteAll.structural|].

Theorem fault_to_comparison : forall ge m mode name k,
  fault_symbols ge -> mode_pointer ge m mode ->
  store_path ge (fun after => after = m) (fault_initial name k m) 6
    (fault_compare_state mode name k m).
Proof.
  intros ge m mode name k [fb [SYMBOL FUNCTION]] [mb [MODE LOAD]].
  fault_next; [apply fault_entry|]. rewrite source_fault_body.
  fault_route. fault_route. fault_next.
  - eapply edge_global_read; [exact MODE|reflexivity|exact LOAD].
  - fault_route. fault_next.
    + unfold fault_call, fault_compare_state, fault_cont, fault_loaded_env.
      eapply edge_call; [reflexivity| | |exact FUNCTION|reflexivity].
      * eapply value_function; [reflexivity|exact SYMBOL|reflexivity].
      * repeat econstructor; unfold fault_env; try WriteAll.lookup; reflexivity.
    + apply store_done; reflexivity.
Qed.

Theorem fault_after_comparison : forall ge m mode name k value,
  store_path ge (fun after => after = m)
    (Returnstate (Vint value) (fault_cont mode name k) m) 3
    (Returnstate (Val.of_bool (Int.eq value Int.zero)) (call_cont k) m).
Proof.
  intros ge m mode name k value. unfold fault_cont, fault_return, fault_loaded_env, fault_env.
  fault_route. fault_route. fault_next.
  - eapply edge_return; [WriteAll.expression|apply bool_int_cast].
  - apply store_done; reflexivity.
Qed.

Lemma strcmp_fault_value : forall m mode name xs ys value,
  c_string m mode xs -> c_string m name ys -> strcmp_result m mode name value ->
  Val.of_bool (Int.eq value Int.zero) = fault_value xs ys.
Proof.
  intros m mode name xs ys value LEFT RIGHT RESULT.
  pose proof (strcmp_zero_iff _ _ _ _ _ _ LEFT RIGHT RESULT) as ZERO.
  unfold fault_value. destruct (compare_bytes xs ys) eqn:CMP.
  - apply compare_bytes_equal in CMP. rewrite (proj2 ZERO CMP); reflexivity.
  - assert (NE : Int.eq value Int.zero = false).
    { destruct (Int.eq value Int.zero) eqn:VALUE; [|reflexivity].
      pose proof (proj1 ZERO eq_refl) as SAME. apply compare_bytes_equal in SAME; congruence. }
    rewrite NE; reflexivity.
  - assert (NE : Int.eq value Int.zero = false).
    { destruct (Int.eq value Int.zero) eqn:VALUE; [|reflexivity].
      pose proof (proj1 ZERO eq_refl) as SAME. apply compare_bytes_equal in SAME; congruence. }
    rewrite NE; reflexivity.
Qed.

Theorem fault_source_certificate : forall ge cell m mode name xs ys,
  fault_symbols ge -> fault_input ge m mode name xs ys ->
  control_certificate ge cell (fun after => after = m)
    (fun value after => value = fault_value xs ys /\ after = m) 10 (fault_initial name Kstop m).
Proof.
  intros ge cell m mode name xs ys SYMBOLS [MODE [LEFT RIGHT]].
  eapply control_source_path with (count := 6%nat) (remaining := 4%nat).
  - apply fault_to_comparison; [exact SYMBOLS|exact MODE].
  - unfold fault_compare_state. eapply control_strcmp; [reflexivity|exact LEFT|exact RIGHT|].
    intros value RESULT. eapply control_source_path with (count := 3%nat) (remaining := 0%nat).
    + apply fault_after_comparison.
    + apply control_return; [reflexivity|]. split; [|reflexivity].
      eapply strcmp_fault_value; eassumption.
Qed.

Theorem fault_return_exact : forall cell m mode name xs ys events actual after,
  fault_input (Clight.globalenv Slice.prog) m mode name xs ys ->
  library_steps (Clight.globalenv Slice.prog) cell (live (fault_initial name Kstop m)) events
    (live (Returnstate actual Kstop after)) ->
  actual = fault_value xs ys /\ after = m.
Proof.
  intros. exact (control_all_returns _ _ _ _ _ _ _ _ _
    (fault_source_certificate _ cell _ _ _ _ _ actual_fault_symbols H) H0).
Qed.

Theorem fault_all_prefixes : forall cell m mode name xs ys events target,
  fault_input (Clight.globalenv Slice.prog) m mode name xs ys ->
  library_steps (Clight.globalenv Slice.prog) cell (live (fault_initial name Kstop m)) events target ->
  routine_memory target = m /\ (control_cost events <= 11)%nat.
Proof.
  intros. pose proof (fault_source_certificate _ cell _ _ _ _ _ actual_fault_symbols H) as CERT.
  destruct (control_all_prefixes _ _ _ _ _ _ CERT _ _ H0) as [MEM [BOUND _]]. auto.
Qed.

Theorem fault_defined_prefix : forall cell m mode name xs ys events s,
  fault_input (Clight.globalenv Slice.prog) m mode name xs ys ->
  library_steps (Clight.globalenv Slice.prog) cell (live (fault_initial name Kstop m)) events (live s) ->
  s = Returnstate (fault_value xs ys) Kstop m \/
  exists ev target, control_progress ev /\ library_step (Clight.globalenv Slice.prog) cell (live s) ev target.
Proof.
  intros. pose proof (fault_source_certificate _ cell _ _ _ _ _ actual_fault_symbols H) as CERT.
  destruct (control_defined_prefix _ _ _ _ _ _ _ _ CERT H0)
    as [[value [after [STATE [VALUE MEM]]]]|PROGRESS]; subst; auto.
Qed.

Lemma library_steps_trans : forall ge cell a b c first second,
  library_steps ge cell a first b -> library_steps ge cell b second c ->
  library_steps ge cell a (first ++ second) c.
Proof. intros ge cell a b c first second AB BC; induction AB; cbn; eauto using library_steps_cons. Qed.

Theorem fault_success_after_waits : forall cell m mode name xs ys k n,
  fault_input (Clight.globalenv Slice.prog) m mode name xs ys ->
  exists events,
    library_steps (Clight.globalenv Slice.prog) cell (live (fault_initial name k m)) events
      (live (Returnstate (fault_value xs ys) (call_cont k) m)) /\
    (length events = n + 10)%nat /\ control_cost events = 10%nat.
Proof.
  intros cell m mode name xs ys k n [MODE [LEFT RIGHT]].
  destruct (strcmp_progress m mode name) as [value RESULT]; [exists xs, ys; auto|].
  assert (SAME : Val.of_bool (Int.eq value Int.zero) = fault_value xs ys)
    by (eapply strcmp_fault_value; eassumption).
  exists (map original_event (repeat (source_step E0) 6) ++ repeat library_wait n ++
    strcmp_returned mode name value :: map original_event (repeat (source_step E0) 3)).
  split.
  - eapply library_steps_trans.
    + apply original_runs_preserved. eapply store_path_actual.
      apply fault_to_comparison; [exact actual_fault_symbols|exact MODE].
    + assert (TAIL : library_steps (Clight.globalenv Slice.prog) cell
        (live (fault_compare_state mode name k m))
        (strcmp_returned mode name value :: map original_event (repeat (source_step E0) 3))
        (live (Returnstate (fault_value xs ys) (call_cont k) m))).
      { econstructor; [apply strcmp_step; exact RESULT|].
        rewrite <- SAME. apply original_runs_preserved; eapply store_path_actual; apply fault_after_comparison. }
      induction n; cbn; [exact TAIL|]. econstructor; [|exact IHn].
      apply library_wait_step; apply strcmp_ready. exists xs, ys; auto.
  - split.
    + rewrite !app_length, !map_length, !repeat_length; cbn; lia.
    + unfold control_cost. rewrite !filter_app; cbn. induction n; cbn; auto.
Qed.
