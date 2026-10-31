(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-effects.errno: Universal checked source normalization, including all TLS reads. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events
  Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Slice IO Machine ClightSteps WriteAll Deterministic.
Import ListNotations.
Open Scope Z_scope.

Definition initialized_errno (cell : tls) (m : mem) (error : int) : Prop :=
  0 <= tls_offset cell /\ tls_offset cell + 4 <= Ptrofs.modulus /\
  Mem.valid_access m Mint32 (tls_block cell) (tls_offset cell) Writable /\
  Mem.load Mint32 m (tls_block cell) (tls_offset cell) = Some (Vint error).

Definition positive error := Int.lt Int.zero error.
Definition bounded error := negb (Int.lt (Int.repr 4095) error).
Definition normalize error :=
  if positive error then (if bounded error then error else Int.repr 5) else Int.repr 5.

Definition query dst := Scall (Some dst)
  (Evar ___errno_location (Tfunction [] (tptr tint) cc_default)) [].
Definition load dst src := Sset dst (Ederef (Etempvar src (tptr tint)) tint).
Definition upper := Ssequence (query _t'3)
  (Ssequence (load _t'8 _t'3)
    (Sset _t'2 (Ecast (Ebinop Ole (Etempvar _t'8 tint)
      (Econst_int (Int.repr 4095) tint) tint) tbool))).
Definition lower := Ssequence (query _t'1)
  (Ssequence (load _t'7 _t'1)
    (Sifthenelse (Ebinop Ogt (Etempvar _t'7 tint)
      (Econst_int Int.zero tint) tint) upper (Sset _t'2 (Econst_int Int.zero tint)))).
Definition accepted := Ssequence (query _t'5)
  (Ssequence (load _t'6 _t'5) (Sset _t'4 (Ecast (Etempvar _t'6 tint) tint))).
Definition choose := Sifthenelse (Etempvar _t'2 tint) accepted
  (Sset _t'4 (Ecast (Econst_int (Int.repr 5) tint) tint)).
Definition result := Sreturn (Some (Etempvar _t'4 tint)).

Theorem source_error_number_body : fn_body f_error_number =
  Ssequence (Ssequence lower choose) result.
Proof. reflexivity. Qed.

Definition initial k m := Callstate (Internal f_error_number) [] k m.

Lemma entry : forall ge k m,
  edge ge (initial k m)
    (State f_error_number (fn_body f_error_number) k empty_env
      (create_undef_temps (fn_temps f_error_number)) m).
Proof.
  intros. split; [exact I|]. split.
  - apply step_internal_function. constructor.
    + constructor.
    + cbn; repeat constructor; simpl; intuition discriminate.
    + unfold list_disjoint, var_names, f_error_number; simpl; tauto.
    + constructor.
    + reflexivity.
  - split; [reflexivity|]. intros t other STEP; inversion STEP; subst.
    match goal with H : function_entry2 _ _ _ _ _ _ _ |- _ => inversion H; subst end.
    match goal with H : alloc_variables _ _ _ _ _ _ |- _ => inversion H; subst end.
    match goal with H : bind_parameter_temps _ _ _ = _ |- _ => cbn in H; inversion H; subst end.
    auto.
Qed.

Lemma errno_certain : forall ge cell k m error,
  initialized_errno cell m error ->
  certain_step ge cell
    (Callstate (External errno_function [] (tptr tint) cc_default) [] k m) errno_step
    (Returnstate (Vptr (tls_block cell) (Ptrofs.repr (tls_offset cell))) k m).
Proof.
  intros ge cell k m error [LO [HI [ACCESS LOAD]]].
  split; [right; reflexivity|]. split; [apply errno_address; assumption|].
  split; [reflexivity|]. intros ev target STEP; inversion STEP; subst; auto;
    try contradiction;
    try match goal with H : boundary _ _ _ |- _ => inversion H end.
Qed.

Lemma errno_load : forall cell m error,
  initialized_errno cell m error ->
  Mem.loadv Mint32 m (Vptr (tls_block cell) (Ptrofs.repr (tls_offset cell))) = Some (Vint error).
Proof.
  intros cell m error [LO [HI [ACCESS LOAD]]]. unfold Mem.loadv.
  rewrite Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; lia).
  destruct (zle (tls_offset cell + size_chunk Mint32) Ptrofs.modulus);
    [exact LOAD|simpl in *; lia].
Qed.

Ltac next_internal := eapply execution_next; [apply internal_certain|].
Ltac route_errno := next_internal; [structural|].
Ltac set_errno := next_internal; [eapply edge_set; expression|].
Ltac branch_errno choice := next_internal;
  [eapply edge_if with (b := choice); [expression|]|].
Ltac call_errno symbol function :=
  next_internal;
  [eapply edge_call; [reflexivity| |apply arguments_nil|exact function|reflexivity];
    eapply value_function; [reflexivity|exact symbol|reflexivity]|].
Ltac load_errno loadproof := next_internal;
  [eapply edge_set; eapply value_load; [expression|reflexivity|exact loadproof]|].
Ltac return_errno := next_internal;
  [eapply edge_return; [expression|reflexivity]|constructor].

(* Counts are numbers of machine steps, not wall-clock/Linux guarantees. *)
Definition source_length error : nat :=
  if positive error then (if bounded error then 34%nat else 26%nat) else 18%nat.

Definition source_queries error : nat :=
  if positive error then (if bounded error then 3%nat else 2%nat) else 1%nat.
Fixpoint query_count (events : list event) : nat :=
  match events with
  | [] => 0%nat
  | errno_step :: rest => S (query_count rest)
  | _ :: rest => query_count rest
  end.

Theorem source_execution : forall ge cell m error k,
  symbols ge -> initialized_errno cell m error ->
  exists events, execution ge cell (initial k m) events
      (Returnstate (Vint (normalize error)) (call_cont k) m) /\
    length events = source_length error /\ query_count events = source_queries error.
Proof.
  intros ge cell m error k [_ [eb [ES EF]]] OWN.
  pose proof (errno_load _ _ _ OWN) as LOAD.
  unfold normalize, source_length, source_queries.
  destruct (positive error) eqn:POS; [destruct (bounded error) eqn:BOUND|];
    eexists; split.
  - next_internal; [apply entry|]. rewrite source_error_number_body.
    unfold lower, upper, choose, accepted, result, query, load.
    route_errno. route_errno. route_errno. call_errno ES EF.
    eapply execution_next; [eapply errno_certain; exact OWN|].
    route_errno. route_errno. route_errno. load_errno LOAD. route_errno.
    branch_errno true.
    { change (bool_val (Val.of_bool (positive error)) tint m = Some true).
      rewrite POS; reflexivity. }
    route_errno. call_errno ES EF.
    eapply execution_next; [eapply errno_certain; exact OWN|].
    route_errno. route_errno. route_errno. load_errno LOAD. route_errno.
    next_internal.
    { eapply edge_set with (v := Vint Int.one). eapply value_cast.
      - eapply value_binary; [expression|expression|reflexivity].
      - change (sem_cast (Val.of_bool (bounded error)) tint tbool m = Some (Vint Int.one)).
        rewrite BOUND; reflexivity. }
    route_errno. branch_errno true; [reflexivity|].
    route_errno. call_errno ES EF.
    eapply execution_next; [eapply errno_certain; exact OWN|].
    route_errno. route_errno. route_errno. load_errno LOAD. route_errno.
    set_errno. route_errno. return_errno.
  - split; reflexivity.
  - next_internal; [apply entry|]. rewrite source_error_number_body.
    unfold lower, upper, choose, accepted, result, query, load.
    route_errno. route_errno. route_errno. call_errno ES EF.
    eapply execution_next; [eapply errno_certain; exact OWN|].
    route_errno. route_errno. route_errno. load_errno LOAD. route_errno.
    branch_errno true.
    { change (bool_val (Val.of_bool (positive error)) tint m = Some true).
      rewrite POS; reflexivity. }
    route_errno. call_errno ES EF.
    eapply execution_next; [eapply errno_certain; exact OWN|].
    route_errno. route_errno. route_errno. load_errno LOAD. route_errno.
    next_internal.
    { eapply edge_set with (v := Vint Int.zero). eapply value_cast.
      - eapply value_binary; [expression|expression|reflexivity].
      - change (sem_cast (Val.of_bool (bounded error)) tint tbool m = Some (Vint Int.zero)).
        rewrite BOUND; reflexivity. }
    route_errno. branch_errno false; [reflexivity|].
    set_errno. route_errno. return_errno.
  - split; reflexivity.
  - next_internal; [apply entry|]. rewrite source_error_number_body.
    unfold lower, upper, choose, accepted, result, query, load.
    route_errno. route_errno. route_errno. call_errno ES EF.
    eapply execution_next; [eapply errno_certain; exact OWN|].
    route_errno. route_errno. route_errno. load_errno LOAD. route_errno.
    branch_errno false.
    { change (bool_val (Val.of_bool (positive error)) tint m = Some false).
      rewrite POS; reflexivity. }
    set_errno. route_errno. branch_errno false; [reflexivity|].
    set_errno. route_errno. return_errno.
  - split; reflexivity.
Qed.

Theorem normalize_signed : forall error,
  normalize error =
    if (0 <? Int.signed error) && (Int.signed error <=? 4095)
    then error else Int.repr 5.
Proof.
  intros error. unfold normalize, positive, bounded, Int.lt.
  change ((if (if zlt 0 (Int.signed error) then true else false)
    then (if negb (if zlt 4095 (Int.signed error) then true else false)
          then error else Int.repr 5) else Int.repr 5) =
    (if (0 <? Int.signed error) && (Int.signed error <=? 4095)
     then error else Int.repr 5)).
  destruct (zlt 0 (Int.signed error)); destruct (zlt 4095 (Int.signed error));
    destruct (0 <? Int.signed error) eqn:LO;
    destruct (Int.signed error <=? 4095) eqn:HI;
    try apply Z.ltb_lt in LO; try apply Z.ltb_ge in LO;
    try apply Z.leb_le in HI; try apply Z.leb_gt in HI; cbn; try reflexivity; lia.
Qed.

Theorem normalize_range : forall error, 1 <= Int.signed (normalize error) <= 4095.
Proof.
  intros. rewrite normalize_signed.
  destruct ((0 <? Int.signed error) && (Int.signed error <=? 4095)) eqn:VALID.
  - apply Bool.andb_true_iff in VALID. destruct VALID as [LO HI].
    apply Z.ltb_lt in LO. apply Z.leb_le in HI. lia.
  - change (1 <= 5 <= 4095); lia.
Qed.

Theorem normalized_boundaries :
  map (fun z => Int.signed (normalize (Int.repr z)))
    [-2147483648; -1; 0; 1; 4095; 4096; 2147483647] = [5; 5; 5; 1; 4095; 5; 5].
Proof. vm_compute; reflexivity. Qed.

Theorem allocated_errno : forall base error,
  exists allocated b m,
    Mem.alloc base 0 4 = (allocated, b) /\
    Mem.store Mint32 allocated b 0 (Vint error) = Some m /\
    initialized_errno {| tls_block := b; tls_offset := 0 |} m error.
Proof.
  intros base error. destruct (Mem.alloc base 0 4) as [allocated b] eqn:ALLOC.
  assert (ACCESS : Mem.valid_access allocated Mint32 b 0 Writable).
  { eapply Mem.valid_access_implies.
    - eapply Mem.valid_access_alloc_same; eauto; cbn; try lia. exists 0; reflexivity.
    - constructor. }
  destruct (Mem.valid_access_store _ _ _ _ (Vint error) ACCESS) as [m STORE].
  exists allocated, b, m. split; [reflexivity|]. split; [exact STORE|].
  unfold initialized_errno; cbn. split; [lia|].
  split; [change (4 <= 18446744073709551616); lia|]. split.
  - eapply Mem.store_valid_access_1; eauto.
  - pose proof (Mem.load_store_same _ _ _ _ _ _ STORE) as LOAD.
    exact LOAD.
Qed.

(* Public statements use the exact generated global environment, not a
   premise that supplies a desired execution or a desired returned result. *)
Theorem error_number_success_exists : forall cell m error k,
  initialized_errno cell m error ->
  exists events, steps (Clight.globalenv Slice.prog) cell (live (initial k m)) events
      (live (Returnstate (Vint (normalize error)) (call_cont k) m)) /\
    length events = source_length error /\ query_count events = source_queries error.
Proof.
  intros. destruct (source_execution _ _ _ _ k actual_program_symbols H) as [events [RUN COUNTS]].
  exists events; split; [apply execution_actual; exact RUN|exact COUNTS].
Qed.

Theorem error_number_return_exact : forall cell m error events value after,
  initialized_errno cell m error ->
  steps (Clight.globalenv Slice.prog) cell (live (initial Kstop m)) events
    (live (Returnstate value Kstop after)) ->
  value = Vint (normalize error) /\ after = m /\
  length events = source_length error /\ query_count events = source_queries error.
Proof.
  intros cell m error events value after OWN RUN.
  destruct (source_execution _ _ _ _ Kstop actual_program_symbols OWN) as [schedule [SCRIPT COUNTS]].
  destruct (execution_return_exact _ _ _ _ _ _ _ _ _ SCRIPT RUN) as [VALUE [MEM EVENTS]].
  subst; auto.
Qed.

Theorem error_number_defined_prefix : forall cell m error events s,
  initialized_errno cell m error ->
  steps (Clight.globalenv Slice.prog) cell (live (initial Kstop m)) events (live s) ->
  s = Returnstate (Vint (normalize error)) Kstop m \/
    exists ev next, routine_event ev /\
      step (Clight.globalenv Slice.prog) cell (live s) ev (live next).
Proof.
  intros cell m error events s OWN RUN.
  destruct (source_execution _ _ _ _ Kstop actual_program_symbols OWN) as [schedule [SCRIPT _]].
  eapply execution_prefix_defined; eassumption.
Qed.

Theorem error_number_all_prefixes : forall cell m error events target,
  initialized_errno cell m error ->
  steps (Clight.globalenv Slice.prog) cell (live (initial Kstop m)) events target ->
  routine_memory target = m /\ Forall allowed_event events /\
    (length events <= S (source_length error))%nat.
Proof.
  intros cell m error events target OWN RUN.
  destruct (source_execution _ _ _ _ Kstop actual_program_symbols OWN)
    as [schedule [SCRIPT [LENGTH QUERIES]]].
  split; [eapply execution_preserves_memory; eassumption|].
  split; [eapply execution_events; eassumption|].
  rewrite <- LENGTH. eapply execution_length_bound; eassumption.
Qed.

Theorem error_number_at_most_35_steps : forall cell m error events target,
  initialized_errno cell m error ->
  steps (Clight.globalenv Slice.prog) cell (live (initial Kstop m)) events target ->
  (length events <= 35)%nat.
Proof.
  intros. destruct (error_number_all_prefixes _ _ _ _ _ H H0) as [_ [_ LENGTH]].
  unfold source_length in LENGTH. destruct (positive error), (bounded error); lia.
Qed.

Theorem error_number_loss_every_prefix : forall cell m error,
  initialized_errno cell m error ->
  exists schedule,
    steps (Clight.globalenv Slice.prog) cell (live (initial Kstop m)) schedule
      (live (Returnstate (Vint (normalize error)) Kstop m)) /\
    length schedule = source_length error /\
    forall n, exists mid,
      steps (Clight.globalenv Slice.prog) cell (live (initial Kstop m))
        (firstn n schedule) (live mid) /\
      steps (Clight.globalenv Slice.prog) cell (live (initial Kstop m))
        (firstn n schedule ++ [loss_step]) (dead m).
Proof.
  intros cell m error OWN.
  destruct (source_execution _ _ _ _ Kstop actual_program_symbols OWN)
    as [schedule [SCRIPT [LENGTH QUERIES]]].
  exists schedule. split; [apply execution_actual; exact SCRIPT|].
  split; [exact LENGTH|]. intro n. exact (execution_loss_every_prefix _ _ _ _ _ n SCRIPT).
Qed.

Theorem arbitrary_errno_source_witness : forall (base : mem) (error : int),
  exists cell m events,
    initialized_errno cell m error /\
    steps (Clight.globalenv Slice.prog) cell (live (initial Kstop m)) events
      (live (Returnstate (Vint (normalize error)) Kstop m)).
Proof.
  intros base error. destruct (allocated_errno base error) as [allocated [b [m [_ [_ OWN]]]]].
  destruct (error_number_success_exists _ _ _ Kstop OWN) as [events [RUN _]].
  eauto.
Qed.
