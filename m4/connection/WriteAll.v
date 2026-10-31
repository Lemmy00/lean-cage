(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-effects.writeall: Universal source-level write_all connection. *)
From Coq Require Import ZArith List String Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events
  Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Slice IO Machine ClightSteps.
Import ListNotations.
Open Scope Z_scope.

Definition write_call := Scall (Some _t'1)
  (Evar _write (Tfunction [tint; tptr tvoid; tulong] tlong cc_default))
  [Etempvar _fd tint; Etempvar _p (tptr tuchar); Etempvar _count tulong].
Definition save_count := Sset _n (Etempvar _t'1 tlong).
Definition errno_call := Scall (Some _t'3)
  (Evar ___errno_location (Tfunction [] (tptr tint) cc_default)) [].
Definition errno_load := Ssequence
  (Sset _t'4 (Ederef (Etempvar _t'3 (tptr tint)) tint))
  (Sset _t'2 (Ecast (Ebinop Oeq (Etempvar _t'4 tint)
    (Econst_int (Int.repr 4) tint) tint) tbool)).
Definition errno_test := Sifthenelse
  (Ebinop Olt (Etempvar _n tlong) (Econst_int Int.zero tint) tint)
  (Ssequence errno_call errno_load) (Sset _t'2 (Econst_int Int.zero tint)).
Definition continue_test := Sifthenelse (Etempvar _t'2 tint) Scontinue Sskip.
Definition failure_test := Sifthenelse
  (Ebinop Ole (Etempvar _n tlong) (Econst_int Int.zero tint) tint)
  (Sreturn (Some (Eunop Oneg (Econst_int Int.one tint) tint))) Sskip.
Definition advance := Ssequence
  (Sset _p (Ebinop Oadd (Etempvar _p (tptr tuchar)) (Etempvar _n tlong) (tptr tuchar)))
  (Sset _count (Ebinop Osub (Etempvar _count tulong)
    (Ecast (Etempvar _n tlong) tulong) tulong)).
Definition tail := Ssequence (Ssequence errno_test continue_test) (Ssequence failure_test advance).
Definition body := Ssequence (Ssequence write_call save_count) tail.
Definition loop_test := Ssequence (Sifthenelse (Etempvar _count tulong) Sskip Sbreak) body.
Definition loop := Sloop loop_test Sskip.
Definition return_zero := Sreturn (Some (Econst_int Int.zero tint)).
Definition loop_cont := Kseq return_zero Kstop.
Definition body_cont := Kloop1 loop_test Sskip loop_cont.
Definition write_cont le := Kcall (Some _t'1) f_write_all empty_env le
  (Kseq save_count (Kseq tail body_cont)).
Definition errno_cont le := Kcall (Some _t'3) f_write_all empty_env le
  (Kseq errno_load (Kseq continue_test (Kseq (Ssequence failure_test advance) body_cont))).

Theorem source_write_all_body : fn_body f_write_all =
  Ssequence (Sset _p (Etempvar _data (tptr tvoid))) (Ssequence loop return_zero).
Proof. reflexivity. Qed.

Definition symbols (ge : genv) : Prop :=
  (exists b, Genv.find_symbol ge _write = Some b /\
     Genv.find_funct ge (Vptr b Ptrofs.zero) =
       Some (External (io_function writing) [tint; tptr tvoid; tulong] tlong cc_default)) /\
  (exists b, Genv.find_symbol ge ___errno_location = Some b /\
     Genv.find_funct ge (Vptr b Ptrofs.zero) =
       Some (External errno_function [] (tptr tint) cc_default)).

Definition suffix (q : request) (sent : Z) : request :=
  {| operation := writing; descriptor := descriptor q;
     buffer_block := buffer_block q; buffer_offset := buffer_offset q + sent;
     requested := requested q - sent; errno_block := errno_block q;
     errno_offset := errno_offset q |}.

Definition registers (q : request) (sent : Z) (le : temp_env) : Prop :=
  le ! _fd = Some (Vint (descriptor q)) /\
  le ! _p = Some (Vptr (buffer_block q) (Ptrofs.repr (buffer_offset q + sent))) /\
  le ! _count = Some (Vlong (Int64.repr (requested q - sent))).

Definition write_state q sent le m :=
  Callstate (External (io_function writing) [tint; tptr tvoid; tulong] tlong cc_default)
    (request_args (suffix q sent)) (write_cont le) m.
Definition errno_state le m :=
  Callstate (External errno_function [] (tptr tint) cc_default) [] (errno_cont le) m.
Definition loop_state le m := State f_write_all loop loop_cont empty_env le m.

Ltac lookup := cbn [set_opttemp]; repeat first [rewrite PTree.gss | rewrite PTree.gso by discriminate];
  first [reflexivity | eassumption].
Ltac expression := first [apply value_int | eapply value_temp; lookup
  | eapply value_binary; [expression|expression|]
  | eapply value_unary; [expression|]
  | eapply value_cast; [expression|]
  | eapply value_load; [expression|reflexivity|] ]; try reflexivity.
Ltac structural := first [apply edge_seq | apply edge_skip_seq | apply edge_loop
  | apply edge_skip_loop1 | apply edge_skip_loop2 | apply edge_break_seq
  | apply edge_break_loop1 | apply edge_continue_seq | apply edge_continue_loop1
  | apply edge_returnstate].
Ltac route := eapply path_next; [structural|].
Ltac set_value := eapply path_next; [eapply edge_set; expression|].
Ltac branch choice := eapply path_next; [eapply edge_if with (b := choice); [expression|]|].

Lemma int64_nonzero : forall n, 0 < n <= 160 -> Int64.eq (Int64.repr n) Int64.zero = false.
Proof.
  intros n N. apply Int64.eq_false. intro EQ.
  apply (f_equal Int64.unsigned) in EQ.
  rewrite Int64.unsigned_repr in EQ; [change (n = 0) in EQ; lia|].
  change (0 <= n <= 18446744073709551615); lia.
Qed.

Lemma loop_to_write : forall ge q sent le m,
  symbols ge -> registers q sent le -> 0 < requested q - sent <= 160 ->
  path ge (loop_state le m) (write_state q sent le m).
Proof.
  intros ge q sent le m [[wb [WS WF]] ES] [FD [P COUNT]] BOUND.
  unfold loop_state, loop, loop_test, body, body_cont, loop_cont, write_state,
    write_cont, write_call, suffix, request_args; simpl.
  route. route. branch true.
  { cbn. rewrite int64_nonzero by assumption. reflexivity. }
  route. route. route.
  eapply path_next.
  - eapply edge_call; [reflexivity| | |exact WF|reflexivity].
    + eapply value_function; [reflexivity|exact WS|reflexivity].
    + repeat first [apply arguments_nil | eapply arguments_cons; [expression|reflexivity|]].
  - constructor.
Qed.

Lemma loop_to_return : forall ge q sent le m,
  registers q sent le -> requested q = sent ->
  path ge (loop_state le m) (Returnstate (Vint Int.zero) Kstop m).
Proof.
  intros ge q sent le m [FD [P COUNT]] EQ.
  rewrite EQ, Z.sub_diag in COUNT.
  unfold loop_state, loop, loop_test, loop_cont, return_zero.
  route. route. branch false; [reflexivity|].
  route. route. route. eapply path_next.
  - eapply edge_return; [expression|reflexivity].
  - constructor.
Qed.

Definition after_write le r := PTree.set _n (Vlong (returned r))
  (PTree.set _t'1 (Vlong (returned r)) le).

Lemma returned_nonnegative : forall r,
  (forall error, r <> failure error) -> 0 <= Int64.signed (returned r) ->
  Int64.lt (returned r) Int64.zero = false.
Proof.
  intros r NE B. unfold Int64.lt. change ((if zlt (Int64.signed (returned r)) 0 then true else false) = false).
  destruct (zlt _ _); [lia|reflexivity].
Qed.

Lemma write_to_errno : forall ge q sent le m error,
  symbols ge -> registers q sent le ->
  path ge (Returnstate (Vlong (returned (failure error))) (write_cont le) m)
    (errno_state (after_write le (failure error)) m).
Proof.
  intros ge q sent le m error [WS [eb [ES EF]]] [FD [P COUNT]].
  unfold write_cont, errno_state, errno_cont, after_write, tail, errno_test, errno_call.
  route. route. set_value. route. route. route. branch true; [reflexivity|].
  route. eapply path_next.
  - eapply edge_call; [reflexivity| |constructor|exact EF|reflexivity].
    eapply value_function; [reflexivity|exact ES|reflexivity].
  - constructor.
Qed.

Lemma signed_small : forall z, 0 <= z <= 160 -> Int64.signed (Int64.repr z) = z.
Proof. intros; apply Int64.signed_repr. change (-9223372036854775808 <= z <= 9223372036854775807); lia. Qed.
Lemma unsigned_small : forall z, 0 <= z <= 160 -> Int64.unsigned (Int64.repr z) = z.
Proof. intros; apply Int64.unsigned_repr. change (0 <= z <= 18446744073709551615); lia. Qed.
Lemma nonnegative_lt : forall z, 0 <= z <= 160 -> Int64.lt (Int64.repr z) Int64.zero = false.
Proof.
  intros z B; unfold Int64.lt. rewrite signed_small by assumption.
  change ((if zlt z 0 then true else false) = false). destruct (zlt z 0); [lia|reflexivity].
Qed.
Lemma positive_le : forall z, 0 < z <= 160 -> Int64.cmp Cle (Int64.repr z) Int64.zero = false.
Proof.
  intros z B; unfold Int64.cmp, Int64.lt. rewrite signed_small by lia.
  change (negb (if zlt 0 z then true else false) = false). destruct (zlt 0 z); [reflexivity|lia].
Qed.

Lemma pointer_advance : forall ge b ofs n m,
  0 <= ofs < Ptrofs.modulus -> 0 <= n <= 160 ->
  sem_binary_operation ge Oadd (Vptr b (Ptrofs.repr ofs)) (tptr tuchar)
    (Vlong (Int64.repr n)) tlong m = Some (Vptr b (Ptrofs.repr (ofs+n))).
Proof.
  intros ge b ofs n m OFS N.
  change (Some (Vptr b (Ptrofs.add (Ptrofs.repr ofs)
    (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 (Int64.repr n))))) = Some (Vptr b (Ptrofs.repr (ofs+n)))).
  unfold Ptrofs.of_int64. rewrite unsigned_small by assumption.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one.
  unfold Ptrofs.add. rewrite Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; lia).
  rewrite Ptrofs.unsigned_repr by (change (0 <= n <= 18446744073709551615); lia).
  reflexivity.
Qed.

Lemma count_decrease : forall count n,
  0 <= n <= count -> count <= 160 ->
  Int64.sub (Int64.repr count) (Int64.repr n) = Int64.repr (count-n).
Proof.
  intros count n B C. unfold Int64.sub. repeat rewrite unsigned_small by lia. reflexivity.
Qed.

Lemma write_positive_to_loop : forall ge q sent le m bytes error,
  registers q sent le -> 0 < Z.of_nat (length bytes) <= requested q - sent ->
  requested q - sent <= 160 -> 0 <= buffer_offset q + sent < Ptrofs.modulus ->
  exists next_le, registers q (sent + Z.of_nat (length bytes)) next_le /\
    path ge (Returnstate (Vlong (returned (transfer bytes error))) (write_cont le) m)
      (loop_state next_le m).
Proof.
  intros ge q sent le m bytes error [FD [P COUNT]] SIZE BOUND OFFSET.
  eexists; split; [|].
  2: {
    unfold write_cont, loop_state, tail, errno_test, continue_test, failure_test, advance.
    route. route. set_value. route. route. route. branch false.
    { change (bool_val (Val.of_bool (Int64.lt (Int64.repr (Z.of_nat (length bytes))) Int64.zero)) tint m = Some false).
      rewrite nonnegative_lt by lia. reflexivity. }
    set_value. route. branch false; [reflexivity|].
    route. route. branch false.
    { change (bool_val (Val.of_bool (Int64.cmp Cle (Int64.repr (Z.of_nat (length bytes))) Int64.zero)) tint m = Some false).
      rewrite positive_le by lia. reflexivity. }
    route. route.
    eapply path_next; [eapply edge_set; eapply value_binary; [expression|expression|apply pointer_advance; lia]|].
    route. set_value. route. route. constructor.
  }
  unfold registers; cbn [set_opttemp].
  split; [lookup|]. split.
  - repeat rewrite PTree.gso by discriminate. rewrite PTree.gss.
    f_equal. f_equal. f_equal. lia.
  - rewrite PTree.gss. cbn [returned]. rewrite count_decrease by lia.
    f_equal. f_equal. f_equal. lia.
Qed.

Lemma write_zero_to_return : forall ge le m error,
  path ge (Returnstate (Vlong (returned (zero error))) (write_cont le) m)
    (Returnstate (Vint Int.mone) Kstop m).
Proof.
  intros. unfold write_cont, tail, errno_test, continue_test, failure_test.
  route. route. set_value. route. route. route. branch false; [reflexivity|].
  set_value. route. branch false; [reflexivity|].
  route. route. branch true; [reflexivity|].
  eapply path_next; [eapply edge_return; [expression|reflexivity]|]. constructor.
Qed.

Definition errno_loaded le q error := PTree.set _t'4 (Vint error)
  (PTree.set _t'3 (Vptr (errno_block q) (Ptrofs.repr (errno_offset q))) le).

Lemma errno_eintr_to_loop : forall ge q sent le m,
  registers q sent le -> le ! _n = Some (Vlong Int64.mone) ->
  Mem.loadv Mint32 m (Vptr (errno_block q) (Ptrofs.repr (errno_offset q))) = Some (Vint (Int.repr 4)) ->
  exists next_le, registers q sent next_le /\
    path ge (Returnstate (Vptr (errno_block q) (Ptrofs.repr (errno_offset q))) (errno_cont le) m)
      (loop_state next_le m).
Proof.
  intros ge q sent le m [FD [P COUNT]] N LOAD.
  eexists; split.
  2: {
    unfold errno_cont, errno_load, continue_test, loop_state.
    route. route. route.
    eapply path_next; [eapply edge_set; eapply value_load; [expression|reflexivity|exact LOAD]|].
    route. set_value. route. branch true; [reflexivity|].
    route. route. route. constructor.
  }
  unfold registers; repeat split; lookup.
Qed.

Lemma errno_error_to_return : forall ge q le m error,
  le ! _n = Some (Vlong Int64.mone) -> error <> Int.repr 4 ->
  Mem.loadv Mint32 m (Vptr (errno_block q) (Ptrofs.repr (errno_offset q))) = Some (Vint error) ->
  path ge (Returnstate (Vptr (errno_block q) (Ptrofs.repr (errno_offset q))) (errno_cont le) m)
    (Returnstate (Vint Int.mone) Kstop m).
Proof.
  intros ge q le m error N NE LOAD.
  unfold errno_cont, errno_load, continue_test, failure_test.
  route. route. route.
  eapply path_next; [eapply edge_set; eapply value_load; [expression|reflexivity|exact LOAD]|].
  route.
  eapply path_next.
  - eapply edge_set with (v := Vint Int.zero); eapply value_cast; [eapply value_binary; [expression|expression|reflexivity]|].
    change (sem_cast (Val.of_bool (Int.eq error (Int.repr 4))) tint tbool m = Some (Vint Int.zero)).
    rewrite Int.eq_false by assumption. reflexivity.
  - route. branch false; [reflexivity|]. route. route. branch true; [reflexivity|].
    eapply path_next; [eapply edge_return; [expression|reflexivity]|]. constructor.
Qed.

Definition initial_env q := PTree.set _count (Vlong (Int64.repr (requested q)))
  (PTree.set _data (Vptr (buffer_block q) (Ptrofs.repr (buffer_offset q)))
    (PTree.set _fd (Vint (descriptor q)) (create_undef_temps (fn_temps f_write_all)))).
Definition initial_state q m :=
  Callstate (Internal f_write_all)
    [Vint (descriptor q); Vptr (buffer_block q) (Ptrofs.repr (buffer_offset q));
     Vlong (Int64.repr (requested q))] Kstop m.

Lemma write_all_entry : forall ge q m,
  edge ge (initial_state q m)
    (State f_write_all (fn_body f_write_all) Kstop empty_env (initial_env q) m).
Proof.
  intros; split; [exact I|]. split.
  - apply step_internal_function. constructor.
    + constructor.
    + cbn; repeat constructor; simpl; intuition discriminate.
    + unfold list_disjoint, var_names, f_write_all; simpl.
      intros x y X Y. repeat destruct X as [X|X]; try contradiction; subst x;
        repeat destruct Y as [Y|Y]; try contradiction; subst y; discriminate.
    + constructor.
    + reflexivity.
  - split; [reflexivity|]. intros t other S; inversion S; subst.
    match goal with ENTRY : function_entry2 _ _ _ _ _ _ _ |- _ => inversion ENTRY; subst end.
    match goal with ALLOC : alloc_variables _ _ _ _ _ _ |- _ => inversion ALLOC; subst end.
    match goal with BIND : bind_parameter_temps _ _ _ = _ |- _ => cbn in BIND; inversion BIND; subst end.
    auto.
Qed.

Lemma initial_to_loop : forall ge q m,
  exists le, registers q 0 le /\ path ge (initial_state q m) (loop_state le m).
Proof.
  intros; eexists; split.
  2: {
    eapply path_next; [apply write_all_entry|]. rewrite source_write_all_body.
    route. set_value. route. route. constructor.
  }
  unfold registers, initial_env; rewrite Z.add_0_r, Z.sub_0_r; repeat split; lookup.
Qed.

Theorem actual_program_symbols : symbols (Clight.globalenv Slice.prog).
Proof.
  split; eexists; split; vm_compute; reflexivity.
Qed.

Require Import WriteMemory.
Definition cell_of q := {| tls_block := errno_block q; tls_offset := errno_offset q |}.

Lemma suffix_errno : forall q sent m error m',
  errno_change (suffix q sent) m error m' -> errno_change q m error m'.
Proof. intros q sent m error m' H; inversion H; subst; constructor; assumption. Qed.

Lemma suffix_owned : forall q done rest m,
  write_owned q (done ++ rest) m -> rest <> [] ->
  owned (suffix q (Z.of_nat (length done))) m.
Proof.
  intros q done rest m [OP [OWN [LEN LOAD]]] NE.
  destruct OWN as [SIZE [OFFSET [WRAP [EO [EW [ACCESS [SEP BUF]]]]]]].
  assert (RLEN : 0 < Z.of_nat (length rest)).
  { destruct rest; [contradiction|simpl; lia]. }
  rewrite app_length, Nat2Z.inj_add in LEN.
  unfold owned, suffix; simpl.
  split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact EO|]. split; [exact EW|]. split; [exact ACCESS|]. split.
  - unfold separated, suffix; simpl. unfold separated in SEP. intuition lia.
  - exists rest. split; [lia|].
    replace (requested q - Z.of_nat (length done)) with (Z.of_nat (length rest)) by lia.
    apply load_suffix. replace (Z.of_nat (length (done ++ rest))) with (requested q) by (rewrite app_length, Nat2Z.inj_add; lia).
    exact LOAD.
Qed.

Lemma write_effect_preserves : forall q done rest m r m',
  write_owned q (done ++ rest) m ->
  io_return (suffix q (Z.of_nat (length done))) m r m' ->
  write_owned q (done ++ rest) m'.
Proof.
  intros q done rest m r m' OWN E. inversion E; subst; try discriminate.
  all: eapply write_owned_errno; [exact OWN|]; eapply suffix_errno; eauto.
Qed.

Lemma write_effect_prefix : forall q done rest m bytes error m',
  write_owned q (done ++ rest) m ->
  io_return (suffix q (Z.of_nat (length done))) m (transfer bytes error) m' ->
  exists remaining, rest = bytes ++ remaining.
Proof.
  intros q done rest m bytes error m' [OP [OWN [LEN LOAD]]] E.
  inversion E; subst; try discriminate.
  assert (L : requested q - Z.of_nat (length done) = Z.of_nat (length rest)).
  { rewrite app_length, Nat2Z.inj_add in LEN; lia. }
  eapply load_prefix; [|eassumption|].
  - apply load_suffix. rewrite LEN. exact LOAD.
  - cbn in *. lia.
Qed.

Lemma errno_loadv : forall q m error,
  owned q m -> Mem.load Mint32 m (errno_block q) (errno_offset q) = Some (Vint error) ->
  Mem.loadv Mint32 m (Vptr (errno_block q) (Ptrofs.repr (errno_offset q))) = Some (Vint error).
Proof.
  intros q m error [_ [_ [_ [EO [EW _]]]]] LOAD.
  unfold Mem.loadv. rewrite Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; lia).
  destruct (zle (errno_offset q + size_chunk Mint32) Ptrofs.modulus); [exact LOAD|simpl in *; lia].
Qed.

Lemma request_injective : forall q q' m,
  owned q m -> owned q' m -> operation q = operation q' ->
  errno_block q = errno_block q' -> errno_offset q = errno_offset q' ->
  request_args q = request_args q' -> q = q'.
Proof.
  intros [op fd b ofs n eb eo] [op' fd' b' ofs' n' eb' eo'] m
    [N [O REST]] [N' [O' REST']] OP EB EO ARGS.
  cbn in *. unfold request_args in ARGS; cbn in ARGS. inversion ARGS; subst.
  change (Ptrofs.unsigned (Ptrofs.repr ofs) = Ptrofs.unsigned (Ptrofs.repr ofs')) in H2.
  repeat rewrite Ptrofs.unsigned_repr in H2 by (unfold Ptrofs.max_unsigned; lia).
  change (Int64.unsigned (Int64.repr n) = Int64.unsigned (Int64.repr n')) in H3.
  repeat rewrite unsigned_small in H3 by lia.
  subst; reflexivity.
Qed.

Lemma write_boundary_unique : forall q sent le m q',
  owned (suffix q sent) m -> owned q' m ->
  boundary (cell_of q) (write_state q sent le m) q' -> q' = suffix q sent.
Proof.
  intros q sent le m q' OWN OWN' B.
  inversion B; subst.
  assert (OP : operation q' = writing).
  { destruct (operation q'); [discriminate|reflexivity]. }
  eapply request_injective; [exact OWN'|exact OWN|exact OP| | |].
  1,2: cbn in *; congruence.
  change (Ptrofs.unsigned (Ptrofs.repr (buffer_offset q')) =
    Ptrofs.unsigned (Ptrofs.repr (buffer_offset q + sent))) in H3.
  apply (f_equal Ptrofs.repr) in H3. repeat rewrite Ptrofs.repr_unsigned in H3.
  change (Int64.unsigned (Int64.repr (requested q')) =
    Int64.unsigned (Int64.repr (requested q - sent))) in H4.
  apply (f_equal Int64.repr) in H4. repeat rewrite Int64.repr_unsigned in H4.
  unfold request_args, suffix; cbn; congruence.
Qed.

Lemma write_machine_cases : forall ge q sent le m ev target,
  owned (suffix q sent) m ->
  Machine.step ge (cell_of q) (live (write_state q sent le m)) ev target ->
  (exists r m', io_return (suffix q sent) m r m' /\
     ev = io_step (suffix q sent) r /\
     target = live (Returnstate (Vlong (returned r)) (write_cont le) m')) \/
  (ev = wait_step /\ target = live (write_state q sent le m)) \/
  (ev = loss_step /\ target = dead m) \/
  (exists bytes error m', io_return (suffix q sent) m (transfer bytes error) m' /\
     ev = partial_loss (suffix q sent) bytes error /\ target = dead m').
Proof.
  intros ge q sent le m ev target OWN STEP.
  inversion STEP; subst; try contradiction.
  2: right; left; auto.
  2: right; right; left; auto.
  all: assert (OP : operation q0 = writing) by (destruct (operation q0); [discriminate|reflexivity]).
  all: assert (Q : q0 = suffix q sent).
  1,3: (
    match goal with B : boundary _ _ _ |- _ => inversion B; subst end;
    eapply request_injective; [match goal with E : io_return _ _ _ _ |- _ => inversion E; eassumption end|exact OWN|exact OP|assumption|assumption|];
    change (Ptrofs.unsigned (Ptrofs.repr (buffer_offset q0)) =
      Ptrofs.unsigned (Ptrofs.repr (buffer_offset q + sent))) in H3;
    apply (f_equal Ptrofs.repr) in H3; repeat rewrite Ptrofs.repr_unsigned in H3;
    change (Int64.unsigned (Int64.repr (requested q0)) =
      Int64.unsigned (Int64.repr (requested q - sent))) in H4;
    apply (f_equal Int64.repr) in H4; repeat rewrite Int64.repr_unsigned in H4;
    unfold request_args, suffix; cbn; congruence
  ).
  - subst q0. left. eauto 8.
  - subst q0. right; right; right; eauto 8.
Qed.

Definition failed_reply (last : option reply) : Prop :=
  (exists error, last = Some (zero error)) \/
  (exists error, last = Some (failure error) /\ error <> Int.repr 4).

Inductive endpoint (q : request) (input done : list Byte.int) (last : option reply) : Clight.state -> Prop :=
| ready_to_write : forall rest le m,
    input = done ++ rest -> rest <> [] -> write_owned q input m ->
    registers q (Z.of_nat (length done)) le ->
    endpoint q input done last (write_state q (Z.of_nat (length done)) le m)
| ready_for_errno : forall rest le m error,
    input = done ++ rest -> rest <> [] -> write_owned q input m ->
    registers q (Z.of_nat (length done)) le ->
    le ! _n = Some (Vlong Int64.mone) ->
    last = Some (failure error) ->
    Mem.load Mint32 m (errno_block q) (errno_offset q) = Some (Vint error) ->
    endpoint q input done last (errno_state le m)
| finished_success : forall m,
    input = done -> write_owned q input m ->
    endpoint q input done last (Returnstate (Vint Int.zero) Kstop m)
| finished_failure : forall rest m,
    input = done ++ rest -> rest <> [] -> write_owned q input m -> failed_reply last ->
    endpoint q input done last (Returnstate (Vint Int.mone) Kstop m).

Definition routed ge q input done last s :=
  exists final, path ge s final /\ endpoint q input done last final.

Inductive invariant ge q input done last : machine -> Prop :=
| invariant_live : forall s, routed ge q input done last s -> invariant ge q input done last (live s)
| invariant_dead : forall m rest,
    input = done ++ rest -> write_owned q input m -> invariant ge q input done last (dead m).

Definition emitted (ev : event) : list Byte.int :=
  match ev with io_step _ (transfer bytes _) | partial_loss _ bytes _ => bytes | _ => [] end.
Definition last_update (last : option reply) (ev : event) : option reply :=
  match ev with io_step _ r => Some r | _ => last end.
Definition emitted_trace (events : list event) := flat_map emitted events.

Lemma endpoint_facts : forall q input done last s,
  endpoint q input done last s -> write_owned q input (memory_of s) /\
  exists rest, input = done ++ rest.
Proof.
  intros; inversion H; subst; split; try assumption; eauto.
  exists []; symmetry; apply app_nil_r.
Qed.

Lemma routed_facts : forall ge q input done last s,
  routed ge q input done last s -> write_owned q input (memory_of s) /\
  exists rest, input = done ++ rest.
Proof.
  intros ge q input done last s [final [PATH END]].
  pose proof (path_memory _ _ _ PATH) as EQ.
  pose proof (endpoint_facts _ _ _ _ _ END); congruence.
Qed.

Lemma routed_extend : forall ge q input done last a b,
  path ge a b -> routed ge q input done last b -> routed ge q input done last a.
Proof. intros ge q input done last a b AB [c [BC END]]; exists c; split; eauto using path_trans. Qed.

Lemma loop_routed : forall ge q input done rest last le m,
  symbols ge -> input = done ++ rest -> write_owned q input m ->
  registers q (Z.of_nat (length done)) le ->
  routed ge q input done last (loop_state le m).
Proof.
  intros ge q input done rest last le m SYM EQ OWN REGS.
  pose proof OWN as [OP [O [LEN LOAD]]]. pose proof O as [SIZE _].
  destruct rest as [|x rest].
  - exists (Returnstate (Vint Int.zero) Kstop m); split.
    + eapply loop_to_return; [exact REGS|]. rewrite app_nil_r in EQ; subst; lia.
    + apply finished_success; [rewrite app_nil_r in EQ; exact EQ|exact OWN].
  - exists (write_state q (Z.of_nat (length done)) le m); split.
    + apply loop_to_write; auto. subst input. rewrite app_length, Nat2Z.inj_add in LEN; cbn in LEN; lia.
    + eapply ready_to_write; eauto; discriminate.
Qed.

Lemma write_return_routed : forall ge q input done rest le m r m',
  symbols ge -> input = done ++ rest -> rest <> [] -> write_owned q input m ->
  registers q (Z.of_nat (length done)) le ->
  io_return (suffix q (Z.of_nat (length done))) m r m' ->
  routed ge q input (done ++ emitted (io_step (suffix q (Z.of_nat (length done))) r)) (Some r)
    (Returnstate (Vlong (returned r)) (write_cont le) m').
Proof.
  intros ge q input done rest le m r m' SYM EQ NE OWN REGS EFFECT.
  assert (PRESERVED : write_owned q input m').
  { subst input; eapply write_effect_preserves; eauto. }
  destruct r as [bytes error|error|error].
  - cbn [emitted].
    destruct (write_effect_prefix q done rest m bytes error m') as [remaining PREFIX];
      [rewrite <- EQ; exact OWN|exact EFFECT|].
    pose proof OWN as [OP [O [LEN LOAD]]].
    destruct O as [SIZE [OFS [WRAP _]]].
    assert (COUNT : 0 < Z.of_nat (length bytes) <= requested q - Z.of_nat (length done)).
    { inversion EFFECT; subst; try discriminate; assumption. }
    assert (BOUNDS : 0 <= Z.of_nat (length done) < requested q).
    { rewrite EQ, app_length, Nat2Z.inj_add in LEN. destruct rest; [contradiction|cbn in LEN; lia]. }
    destruct (write_positive_to_loop ge q (Z.of_nat (length done)) le m' bytes error REGS COUNT)
      as [next_le [NEXT PATH]]; try lia.
    eapply routed_extend; [exact PATH|]. eapply loop_routed with (rest := remaining); eauto.
    + rewrite <- app_assoc. rewrite <- PREFIX. exact EQ.
    + rewrite app_length, Nat2Z.inj_add. exact NEXT.
  - cbn [emitted]; rewrite app_nil_r.
    exists (errno_state (after_write le (failure error)) m'); split.
    + eapply write_to_errno; eauto.
    + eapply ready_for_errno with (rest := rest) (error := error); eauto.
      * unfold registers, after_write. destruct REGS as [FD [P COUNT]]; repeat split; lookup.
      * unfold after_write; apply PTree.gss.
      * eapply failure_errno in EFFECT. exact EFFECT.
  - cbn [emitted]; rewrite app_nil_r.
    exists (Returnstate (Vint Int.mone) Kstop m'); split.
    + apply write_zero_to_return.
    + eapply finished_failure; eauto. left; eauto.
Qed.

Lemma errno_return_routed : forall ge q input done rest last le m error,
  symbols ge -> input = done ++ rest -> rest <> [] -> write_owned q input m ->
  registers q (Z.of_nat (length done)) le -> le ! _n = Some (Vlong Int64.mone) ->
  last = Some (failure error) ->
  Mem.load Mint32 m (errno_block q) (errno_offset q) = Some (Vint error) ->
  routed ge q input done last
    (Returnstate (Vptr (errno_block q) (Ptrofs.repr (errno_offset q))) (errno_cont le) m).
Proof.
  intros ge q input done rest last le m error SYM EQ NE OWN REGS N LAST LOAD.
  assert (LOADV : Mem.loadv Mint32 m (Vptr (errno_block q) (Ptrofs.repr (errno_offset q))) = Some (Vint error)).
  { apply errno_loadv; [apply OWN|exact LOAD]. }
  destruct (Int.eq_dec error (Int.repr 4)) as [EINTR|FAIL].
  - subst error. destruct (errno_eintr_to_loop ge q (Z.of_nat (length done)) le m REGS N LOADV)
      as [next_le [NEXT PATH]].
    eapply routed_extend; [exact PATH|]. eapply loop_routed; eauto.
  - exists (Returnstate (Vint Int.mone) Kstop m); split.
    + eapply errno_error_to_return; eauto.
    + eapply finished_failure; eauto. right; eauto.
Qed.

Lemma errno_machine_cases : forall ge q le m ev target,
  Machine.step ge (cell_of q) (live (errno_state le m)) ev target ->
  (ev = errno_step /\ target = live
    (Returnstate (Vptr (errno_block q) (Ptrofs.repr (errno_offset q))) (errno_cont le) m)) \/
  (ev = loss_step /\ target = dead m).
Proof.
  intros ge q le m ev target STEP; inversion STEP; subst; try contradiction; try solve [auto].
  all: try match goal with B : boundary _ _ _ |- _ => inversion B; subst end.
  all: match goal with H : context [operation ?q] |- _ => destruct (operation q); discriminate end.
Qed.

Lemma terminal_machine_cases : forall ge cell v m ev target,
  Machine.step ge cell (live (Returnstate v Kstop m)) ev target ->
  ev = loss_step /\ target = dead m.
Proof.
  intros ge cell v m ev target STEP; inversion STEP; subst; auto.
  - match goal with S : step2 _ _ _ _ |- _ => inversion S end.
  - match goal with B : boundary _ _ _ |- _ => inversion B end.
Qed.

Lemma endpoint_step : forall ge q input done last s ev target,
  symbols ge -> endpoint q input done last s ->
  Machine.step ge (cell_of q) (live s) ev target ->
  invariant ge q input (done ++ emitted ev) (last_update last ev) target.
Proof.
  intros ge q input done last s ev target SYM END STEP.
  inversion END as [rest le m EQ NE OWN REGS|rest le m error EQ NE OWN REGS N LAST LOAD|
                    m EQ OWN|rest m EQ NE OWN FAIL]; subst s.
  - assert (SUFFIX : owned (suffix q (Z.of_nat (length done))) m).
    { apply suffix_owned with (rest := rest); [rewrite <- EQ; exact OWN|exact NE]. }
    destruct (write_machine_cases _ _ _ _ _ _ _ SUFFIX STEP)
      as [[r [m' [EFFECT [EVENT TARGET]]]]|[[EVENT TARGET]|[[EVENT TARGET]|[bytes [error [m' [EFFECT [EVENT TARGET]]]]]]]];
      subst ev target; cbn [emitted last_update]; try rewrite app_nil_r.
    + apply invariant_live. eapply write_return_routed; eauto.
    + apply invariant_live. exists (write_state q (Z.of_nat (length done)) le m); split; [constructor|exact END].
    + eapply invariant_dead; eauto.
    + destruct (write_effect_prefix q done rest m bytes error m') as [remaining PREFIX];
        [rewrite <- EQ; exact OWN|exact EFFECT|].
      eapply invariant_dead with (rest := remaining).
      * rewrite <- app_assoc, <- PREFIX; exact EQ.
      * rewrite EQ; eapply write_effect_preserves; [rewrite <- EQ; exact OWN|exact EFFECT].
  - destruct (errno_machine_cases _ _ _ _ _ _ STEP) as [[EVENT TARGET]|[EVENT TARGET]];
      subst ev target; cbn [emitted last_update]; rewrite app_nil_r.
    + apply invariant_live. eapply errno_return_routed; eauto.
    + eapply invariant_dead; eauto.
  - destruct (terminal_machine_cases _ _ _ _ _ _ STEP) as [EVENT TARGET]; subst ev target.
    cbn [emitted last_update]; rewrite app_nil_r.
    eapply invariant_dead with (rest := []); [rewrite app_nil_r; exact EQ|exact OWN].
  - destruct (terminal_machine_cases _ _ _ _ _ _ STEP) as [EVENT TARGET]; subst ev target.
    cbn [emitted last_update]; rewrite app_nil_r. eapply invariant_dead; eauto.
Qed.

Theorem write_all_invariant_step : forall ge q input done last s ev target,
  symbols ge -> invariant ge q input done last s ->
  Machine.step ge (cell_of q) s ev target ->
  invariant ge q input (done ++ emitted ev) (last_update last ev) target.
Proof.
  intros ge q input done last s ev target SYM INV STEP.
  inversion INV as [live_s ROUTED|m rest EQ OWN]; subst s.
  - destruct ROUTED as [final [PATH END]].
    inversion PATH as [|a mid b EDGE REST]; subst.
    + eapply endpoint_step; eauto.
    + destruct (machine_edge_cases _ _ _ _ _ _ EDGE STEP) as [[EVENT TARGET]|[EVENT TARGET]];
        subst ev target; cbn [emitted last_update]; rewrite app_nil_r.
      * apply invariant_live. exists final; auto.
      * destruct (routed_facts ge q input done last live_s) as [OWN [rest EQ]].
        { exists final; auto. }
        eapply invariant_dead; eauto.
  - inversion STEP.
Qed.

Definition ordinary (ev : event) : Prop :=
  match ev with source_step _ | io_step _ _ | errno_step => True | _ => False end.

Lemma endpoint_progress : forall ge q input done last s,
  endpoint q input done last s ->
  (exists v m, s = Returnstate (Vint v) Kstop m) \/
  (exists ev target, ordinary ev /\ Machine.step ge (cell_of q) (live s) ev target).
Proof.
  intros ge q input done last s END; inversion END; subst; try solve [left; eauto].
  - right. assert (OWN : owned (suffix q (Z.of_nat (length done))) m).
    { eapply suffix_owned; eauto. }
    exists (io_step (suffix q (Z.of_nat (length done))) (zero None)),
      (live (Returnstate (Vlong Int64.zero) (write_cont le) m)); split; [exact I|].
    eapply effect with (q := suffix q (Z.of_nat (length done))) (r := zero None); [constructor; reflexivity|]. apply zero_return_exists; exact OWN.
  - right. exists errno_step,
      (live (Returnstate (Vptr (errno_block q) (Ptrofs.repr (errno_offset q))) (errno_cont le) m)); split; [exact I|].
    apply errno_address.
    all: match goal with H : write_owned _ _ _ |- _ => destruct H as [_ [[_ [_ [_ [EO [EW [ACCESS _]]]]]] _]] end; assumption.
Qed.

Theorem write_all_invariant_progress : forall ge q input done last s,
  invariant ge q input done last (live s) ->
  (exists v m, s = Returnstate (Vint v) Kstop m) \/
  (exists ev target, ordinary ev /\ Machine.step ge (cell_of q) (live s) ev target).
Proof.
  intros ge q input done last s INV; inversion INV; subst.
  match goal with H : routed _ _ _ _ _ _ |- _ => destruct H as [final [PATH END]] end.
  inversion PATH; subst.
  - eapply endpoint_progress; eauto.
  - right. exists (source_step E0), (live mid); split; [exact I|].
    apply internal; destruct H as [IN [STEP _]]; assumption.
Qed.

Lemma invariant_initial : forall ge q input m,
  symbols ge -> write_owned q input m -> invariant ge q input [] None (live (initial_state q m)).
Proof.
  intros ge q input m SYM OWN.
  destruct (initial_to_loop ge q m) as [le [REGS PATH]].
  apply invariant_live. eapply routed_extend; [exact PATH|]. eapply loop_routed with (rest := input); eauto.
Qed.

Theorem write_all_invariant_runs : forall ge q input s events target,
  steps ge (cell_of q) s events target -> symbols ge ->
  forall done last, invariant ge q input done last s ->
  invariant ge q input (done ++ emitted_trace events) (fold_left last_update events last) target.
Proof.
  intros ge q input s events target RUN; induction RUN; intros SYM done previous INV.
  - cbn; rewrite app_nil_r; exact INV.
  - specialize (IHRUN SYM (done ++ emitted e) (last_update previous e)).
    cbn [emitted_trace flat_map fold_left]. rewrite app_assoc.
    apply IHRUN. eapply write_all_invariant_step; eauto.
Qed.

Definition machine_memory (s : machine) : mem :=
  match s with live s => memory_of s | dead m => m end.

Lemma invariant_facts : forall ge q input done last s,
  invariant ge q input done last s ->
  write_owned q input (machine_memory s) /\ exists rest, input = done ++ rest.
Proof.
  intros ge q input done last s INV; inversion INV; subst.
  - apply routed_facts in H; exact H.
  - split; [assumption|eauto].
Qed.

Lemma terminal_path : forall ge v m final,
  path ge (Returnstate v Kstop m) final -> final = Returnstate v Kstop m.
Proof.
  intros ge v m final P; inversion P; subst; auto.
  destruct H as [_ [STEP _]]. inversion STEP.
Qed.

Theorem write_all_prefix_safety : forall q input m events target,
  write_owned q input m ->
  steps (Clight.globalenv Slice.prog) (cell_of q) (live (initial_state q m)) events target ->
  write_owned q input (machine_memory target) /\
  exists remaining, input = emitted_trace events ++ remaining.
Proof.
  intros q input m events target OWN RUN.
  pose proof (write_all_invariant_runs _ _ _ _ _ _ RUN actual_program_symbols [] None
    (invariant_initial _ _ _ _ actual_program_symbols OWN)) as INV.
  apply invariant_facts in INV. exact INV.
Qed.

Theorem write_all_defined_prefix : forall q input m events s,
  write_owned q input m ->
  steps (Clight.globalenv Slice.prog) (cell_of q) (live (initial_state q m)) events (live s) ->
  (exists v after, s = Returnstate (Vint v) Kstop after) \/
  (exists ev target, ordinary ev /\
     Machine.step (Clight.globalenv Slice.prog) (cell_of q) (live s) ev target).
Proof.
  intros q input m events s OWN RUN. eapply write_all_invariant_progress.
  eapply write_all_invariant_runs; [exact RUN|exact actual_program_symbols|].
  apply invariant_initial; [exact actual_program_symbols|exact OWN].
Qed.

Theorem write_all_return_exact : forall q input m events v after,
  write_owned q input m ->
  steps (Clight.globalenv Slice.prog) (cell_of q) (live (initial_state q m)) events
    (live (Returnstate v Kstop after)) ->
  (v = Vint Int.zero /\ emitted_trace events = input) \/
  (v = Vint Int.mone /\ failed_reply (fold_left last_update events None) /\
    emitted_trace events <> input).
Proof.
  intros q input m events v after OWN RUN.
  pose proof (write_all_invariant_runs _ _ _ _ _ _ RUN actual_program_symbols [] None
    (invariant_initial _ _ _ _ actual_program_symbols OWN)) as INV.
  inversion INV; subst.
  match goal with H : routed _ _ _ _ _ _ |- _ => destruct H as [final [PATH END]] end.
  apply terminal_path in PATH; subst final. inversion END; subst; cbn in *.
  - left; auto.
  - right; split; [reflexivity|]. split; [assumption|].
    intro EQ. apply (f_equal (@List.length Byte.int)) in EQ.
    rewrite app_length in EQ. destruct rest; [contradiction|cbn in EQ; lia].
Qed.

Theorem write_all_loss_is_terminal : forall q input m events after ev target,
  write_owned q input m ->
  steps (Clight.globalenv Slice.prog) (cell_of q) (live (initial_state q m)) events (dead after) ->
  ~ Machine.step (Clight.globalenv Slice.prog) (cell_of q) (dead after) ev target.
Proof. intros; eapply dead_cannot_resume. Qed.

Lemma steps_trans : forall ge cell a b c first second,
  steps ge cell a first b -> steps ge cell b second c ->
  steps ge cell a (first ++ second) c.
Proof. intros ge cell a b c first second A B; induction A; cbn; eauto using steps_cons. Qed.

Lemma suffix_zero : forall q, operation q = writing -> suffix q 0 = q.
Proof. intros [op fd b ofs count eb eo] OP; cbn in OP; subst op; unfold suffix; cbn; rewrite Z.add_0_r, Z.sub_0_r; reflexivity. Qed.

Theorem write_all_success_exists : forall q input m,
  write_owned q input m ->
  exists events, steps (Clight.globalenv Slice.prog) (cell_of q)
    (live (initial_state q m)) events (live (Returnstate (Vint Int.zero) Kstop m)) /\
    emitted_trace events = input.
Proof.
  intros q input m OWN.
  pose proof OWN as [OP [O [LEN LOAD]]]. pose proof O as [SIZE [OFS [WRAP _]]].
  destruct (initial_to_loop (Clight.globalenv Slice.prog) q m) as [le [REGS INIT]].
  assert (RUN : exists events, steps (Clight.globalenv Slice.prog) (cell_of q)
    (live (initial_state q m)) events (live (Returnstate (Vint Int.zero) Kstop m))).
  { destruct input as [|x input].
    - assert (END : path (Clight.globalenv Slice.prog) (loop_state le m) (Returnstate (Vint Int.zero) Kstop m)).
      { apply loop_to_return with (q := q) (sent := 0); [exact REGS|cbn in LEN; lia]. }
      eapply path_machine_steps. eapply path_trans; eauto.
    - assert (POS : 0 < Z.of_nat (length (x :: input)) <= requested q) by (cbn in LEN; cbn; lia).
      assert (WR : path (Clight.globalenv Slice.prog) (loop_state le m) (write_state q 0 le m)).
      { apply loop_to_write; [exact actual_program_symbols|exact REGS|lia]. }
      assert (EFFECT : io_return (suffix q 0) m (transfer (x :: input) None) m).
      { rewrite suffix_zero by exact OP. apply write_returns; auto; try constructor. rewrite LEN; exact LOAD. }
      destruct (write_positive_to_loop (Clight.globalenv Slice.prog) q 0 le m (x :: input) None REGS)
        as [next_le [NEXT AFTER]]; try lia.
      assert (END : path (Clight.globalenv Slice.prog) (loop_state next_le m) (Returnstate (Vint Int.zero) Kstop m)).
      { eapply loop_to_return; [exact NEXT|lia]. }
      destruct (path_machine_steps _ (cell_of q) _ _ (path_trans _ _ _ _ INIT WR)) as [before BEFORE].
      destruct (path_machine_steps _ (cell_of q) _ _ (path_trans _ _ _ _ AFTER END)) as [after AFTER_RUN].
      exists (before ++ io_step (suffix q 0) (transfer (x :: input) None) :: after).
      eapply steps_trans; [exact BEFORE|]. econstructor; [|exact AFTER_RUN].
      eapply effect with (q := suffix q 0); [constructor; reflexivity|exact EFFECT]. }
  destruct RUN as [events RUN]. exists events; split; [exact RUN|].
  destruct (write_all_return_exact _ _ _ _ _ _ OWN RUN) as [[_ EQ]|[BAD _]]; [exact EQ|discriminate].
Qed.
