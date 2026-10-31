(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-effects.writeall: Constructive real-source success, error, retry and loss. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Ctypes Ctypesdefs Clight.
Require Import Slice IO Machine ClightSteps WriteMemory WriteAll.
Import ListNotations.
Open Scope Z_scope.

Theorem arbitrary_write_ownership : forall (base : mem) (bytes : list Byte.int),
  Z.of_nat (length bytes) <= 160 -> exists q m, write_owned q bytes m.
Proof.
  intros base bytes SIZE.
  destruct (Mem.alloc base 0 (Z.of_nat (length bytes))) as [mb b] eqn:BUF.
  destruct (Mem.alloc mb 0 4) as [me eb] eqn:ERR.
  assert (NE : b <> eb).
  { pose proof (Mem.alloc_result _ _ _ _ _ BUF).
    pose proof (Mem.alloc_result _ _ _ _ _ ERR).
    pose proof (Mem.nextblock_alloc _ _ _ _ _ BUF); subst; lia. }
  assert (EA : Mem.valid_access me Mint32 eb 0 Writable).
  { eapply Mem.valid_access_implies.
    - eapply Mem.valid_access_alloc_same; eauto; cbn; try lia. exists 0; reflexivity.
    - constructor. }
  assert (BA : Mem.range_perm me b 0 (0 + Z.of_nat (length (map Byte bytes))) Cur Writable).
  { rewrite map_length. intros i I. eapply Mem.perm_alloc_1; eauto.
    eapply Mem.perm_implies; [eapply Mem.perm_alloc_2; eauto; lia|constructor]. }
  destruct (Mem.range_perm_storebytes _ _ _ _ BA) as [m STORE].
  exists {| operation := writing; descriptor := Int.one;
    buffer_block := b; buffer_offset := 0; requested := Z.of_nat (length bytes);
    errno_block := eb; errno_offset := 0 |}, m.
  assert (LOAD : Mem.loadbytes m b 0 (Z.of_nat (length bytes)) = Some (map Byte bytes)).
  { rewrite <- (map_length Byte bytes). eapply Mem.loadbytes_storebytes_same; eauto. }
  split; [reflexivity|]. split; [|auto]. unfold owned; cbn.
  split; [lia|]. split; [change (0 <= 0 < 18446744073709551616); lia|].
  split; [change (Z.of_nat (length bytes) <= 18446744073709551616); lia|].
  split; [lia|]. split; [change (4 <= 18446744073709551616); lia|]. split.
  - eapply Mem.storebytes_valid_access_1; eauto.
  - split; [unfold separated; cbn; auto|]. exists bytes; auto.
Qed.

Definition replies (events : list event) : list reply :=
  flat_map (fun ev => match ev with io_step _ r => [r] | _ => [] end) events.
Lemma replies_app : forall a b, replies (a ++ b) = replies a ++ replies b.
Proof. intros; apply flat_map_app. Qed.
Lemma replies_internal : forall n, replies (repeat (source_step E0) n) = [].
Proof. induction n; cbn; auto. Qed.

Lemma loop_success_exists : forall ge q done rest le m,
  symbols ge -> write_owned q (done ++ rest) m -> registers q (Z.of_nat (length done)) le ->
  exists events, steps ge (cell_of q) (live (loop_state le m)) events
    (live (Returnstate (Vint Int.zero) Kstop m)).
Proof.
  intros ge q done rest le m SYM OWN REGS.
  pose proof OWN as [OP [O [LEN LOAD]]]. pose proof O as [SIZE [OFS [WRAP _]]].
  destruct rest as [|x rest].
  - apply path_machine_steps. eapply loop_to_return; [exact REGS|rewrite app_nil_r in LEN; lia].
  - assert (BOUND : 0 < Z.of_nat (length (x :: rest)) <= requested q - Z.of_nat (length done)).
    { rewrite app_length, Nat2Z.inj_add in LEN; cbn in *; lia. }
    assert (SENT : 0 <= Z.of_nat (length done) < requested q).
    { rewrite app_length, Nat2Z.inj_add in LEN; cbn in *; lia. }
    pose proof (loop_to_write ge q (Z.of_nat (length done)) le m SYM REGS ltac:(lia)) as BEFORE.
    assert (EFFECT : io_return (suffix q (Z.of_nat (length done))) m (transfer (x :: rest) None) m).
    { apply write_returns.
      - eapply suffix_owned; eauto; discriminate.
      - reflexivity.
      - exact BOUND.
      - apply load_suffix. rewrite LEN; exact LOAD.
      - constructor. }
    destruct (write_positive_to_loop ge q (Z.of_nat (length done)) le m (x :: rest) None REGS BOUND)
      as [next_le [NEXT AFTER]]; try lia.
    assert (END : path ge (loop_state next_le m) (Returnstate (Vint Int.zero) Kstop m)).
    { eapply loop_to_return; [exact NEXT|rewrite app_length, Nat2Z.inj_add in LEN; lia]. }
    destruct (path_machine_steps _ (cell_of q) _ _ BEFORE) as [before B].
    destruct (path_machine_steps _ (cell_of q) _ _ (path_trans _ _ _ _ AFTER END)) as [after A].
    exists (before ++ io_step (suffix q (Z.of_nat (length done))) (transfer (x :: rest) None) :: after).
    eapply steps_trans; [exact B|]. econstructor; [|exact A].
    eapply effect with (q := suffix q (Z.of_nat (length done))); [constructor; reflexivity|exact EFFECT].
Qed.

Lemma one_eintr_retry : forall ge q input le m,
  symbols ge -> write_owned q input m -> input <> [] -> registers q 0 le ->
  exists events next_le after,
    steps ge (cell_of q) (live (loop_state le m)) events (live (loop_state next_le after)) /\
    write_owned q input after /\ registers q 0 next_le /\ replies events = [failure (Int.repr 4)].
Proof.
  intros ge q input le m SYM OWN NE REGS.
  pose proof OWN as [OP [O [LEN LOAD]]]. pose proof O as [SIZE _].
  assert (POS : 0 < requested q) by (destruct input; [contradiction|cbn in LEN; lia]).
  pose proof (loop_to_write ge q 0 le m SYM REGS ltac:(lia)) as BEFORE.
  destruct (error_return_exists (suffix q 0) m (Int.repr 4)) as [after EFFECT].
  { rewrite suffix_zero by exact OP; exact O. }
  assert (AFTER_OWN : write_owned q input after).
  { replace input with ([] ++ input) by reflexivity. eapply write_effect_preserves; eauto. }
  pose proof (write_to_errno ge q 0 le after (Int.repr 4) SYM REGS) as MIDDLE.
  assert (REGS' : registers q 0 (after_write le (failure (Int.repr 4)))).
  { unfold registers, after_write. destruct REGS as [FD [P COUNT]]; repeat split; lookup. }
  assert (N : (after_write le (failure (Int.repr 4))) ! _n = Some (Vlong Int64.mone)) by apply PTree.gss.
  assert (ERRNO : Mem.loadv Mint32 after (Vptr (errno_block q) (Ptrofs.repr (errno_offset q))) = Some (Vint (Int.repr 4))).
  { apply errno_loadv; [apply AFTER_OWN|]. eapply failure_errno in EFFECT; exact EFFECT. }
  destruct (errno_eintr_to_loop ge q 0 (after_write le (failure (Int.repr 4))) after REGS' N ERRNO)
    as [next_le [NEXT AFTER]].
  destruct (path_source_steps _ (cell_of q) _ _ BEFORE) as [b B].
  destruct (path_source_steps _ (cell_of q) _ _ MIDDLE) as [c C].
  destruct (path_source_steps _ (cell_of q) _ _ AFTER) as [a A].
  exists (repeat (source_step E0) b ++ io_step (suffix q 0) (failure (Int.repr 4)) ::
    (repeat (source_step E0) c ++ errno_step :: repeat (source_step E0) a)), next_le, after.
  split.
  - eapply steps_trans; [exact B|]. econstructor.
    + eapply effect with (q := suffix q 0); [constructor; reflexivity|exact EFFECT].
    + eapply steps_trans; [exact C|]. econstructor; [|exact A].
      apply errno_address.
      all: destruct AFTER_OWN as [_ [[_ [_ [_ [EO [EW [ACCESS _]]]]]] _]]; assumption.
  - split; [exact AFTER_OWN|]. split; [exact NEXT|].
    rewrite replies_app, replies_internal; cbn. rewrite replies_app, replies_internal; cbn.
    rewrite replies_internal; reflexivity.
Qed.

Theorem arbitrary_eintr_retries : forall n ge q input le m,
  symbols ge -> write_owned q input m -> input <> [] -> registers q 0 le ->
  exists events next_le after,
    steps ge (cell_of q) (live (loop_state le m)) events (live (loop_state next_le after)) /\
    write_owned q input after /\ registers q 0 next_le /\
    replies events = repeat (failure (Int.repr 4)) n.
Proof.
  induction n as [|n IH]; intros ge q input le m SYM OWN NE REGS.
  - exists [], le, m; split; [constructor|auto].
  - destruct (one_eintr_retry _ _ _ _ _ SYM OWN NE REGS) as [before [mid [m' [B [O [R REPLIES]]]]]].
    destruct (IH _ _ _ _ _ SYM O NE R) as [after [final [m'' [A [O' [R' REPLIES']]]]]].
    exists (before ++ after), final, m''; split; [eapply steps_trans; eauto|].
    split; [exact O'|]. split; [exact R'|]. rewrite replies_app, REPLIES, REPLIES'; reflexivity.
Qed.

Theorem source_retries_then_success : forall n q input m,
  write_owned q input m -> input <> [] ->
  exists before after middle final,
    steps (Clight.globalenv Slice.prog) (cell_of q) (live (initial_state q m)) before (live middle) /\
    replies before = repeat (failure (Int.repr 4)) n /\
    steps (Clight.globalenv Slice.prog) (cell_of q) (live middle) after
      (live (Returnstate (Vint Int.zero) Kstop final)) /\
    emitted_trace (before ++ after) = input.
Proof.
  intros n q input m OWN NE.
  destruct (initial_to_loop (Clight.globalenv Slice.prog) q m) as [le [REGS INIT]].
  destruct (path_source_steps _ (cell_of q) _ _ INIT) as [count INIT_RUN].
  destruct (arbitrary_eintr_retries n _ _ _ _ _ actual_program_symbols OWN NE REGS)
    as [retry [next_le [final [RETRY [O [R REPLIES]]]]]].
  destruct (loop_success_exists (Clight.globalenv Slice.prog) q [] input next_le final actual_program_symbols O R)
    as [after AFTER].
  exists (repeat (source_step E0) count ++ retry), after, (loop_state next_le final), final.
  assert (BEFORE : steps (Clight.globalenv Slice.prog) (cell_of q) (live (initial_state q m))
    (repeat (source_step E0) count ++ retry) (live (loop_state next_le final))) by (eapply steps_trans; eauto).
  split; [exact BEFORE|]. split; [rewrite replies_app, replies_internal; exact REPLIES|].
  split; [exact AFTER|].
  assert (RUN := steps_trans _ _ _ _ _ _ _ BEFORE AFTER).
  destruct (write_all_return_exact _ _ _ _ _ _ OWN RUN) as [[_ EQ]|[BAD _]]; [exact EQ|discriminate].
Qed.

Theorem source_short_write_then_success : forall q first rest m,
  write_owned q (first ++ rest) m -> first <> [] -> rest <> [] ->
  exists before after middle,
    steps (Clight.globalenv Slice.prog) (cell_of q) (live (initial_state q m)) before (live middle) /\
    replies before = [transfer first None] /\
    steps (Clight.globalenv Slice.prog) (cell_of q) (live middle) after
      (live (Returnstate (Vint Int.zero) Kstop m)) /\
    emitted_trace (before ++ after) = first ++ rest.
Proof.
  intros q first rest m OWN FIRST REST.
  pose proof OWN as [OP [O [LEN LOAD]]]. pose proof O as [SIZE [OFS _]].
  assert (POS : 0 < Z.of_nat (length first) < requested q).
  { rewrite app_length, Nat2Z.inj_add in LEN. destruct first, rest; cbn in *; try contradiction; lia. }
  destruct (initial_to_loop (Clight.globalenv Slice.prog) q m) as [le [REGS INIT]].
  pose proof (loop_to_write _ q 0 le m actual_program_symbols REGS ltac:(lia)) as BEFORE.
  assert (EFFECT : io_return (suffix q 0) m (transfer first None) m).
  { rewrite suffix_zero by exact OP. apply write_returns; auto; try constructor; try lia.
    apply load_first with (rest := rest). rewrite LEN; exact LOAD. }
  destruct (write_positive_to_loop (Clight.globalenv Slice.prog) q 0 le m first None REGS)
    as [next_le [NEXT AFTER]]; try lia.
  destruct (loop_success_exists (Clight.globalenv Slice.prog) q first rest next_le m actual_program_symbols OWN NEXT)
    as [after END].
  destruct (path_source_steps _ (cell_of q) _ _ (path_trans _ _ _ _ INIT BEFORE)) as [b B].
  destruct (path_source_steps _ (cell_of q) _ _ AFTER) as [a A].
  set (before := repeat (source_step E0) b ++ io_step (suffix q 0) (transfer first None) :: repeat (source_step E0) a).
  assert (RUN : steps (Clight.globalenv Slice.prog) (cell_of q) (live (initial_state q m)) before (live (loop_state next_le m))).
  { unfold before. eapply steps_trans; [exact B|]. econstructor; [|exact A].
    eapply effect with (q := suffix q 0); [constructor; reflexivity|exact EFFECT]. }
  exists before, after, (loop_state next_le m). split; [exact RUN|]. split.
  - unfold before. rewrite replies_app, replies_internal; cbn; rewrite replies_internal; reflexivity.
  - split; [exact END|]. pose proof (steps_trans _ _ _ _ _ _ _ RUN END) as ALL.
    destruct (write_all_return_exact _ _ _ _ _ _ OWN ALL) as [[_ EQ]|[BAD _]]; [exact EQ|discriminate].
Qed.

Theorem source_error_return : forall q input m error,
  write_owned q input m -> input <> [] -> error <> Int.repr 4 ->
  exists events after, steps (Clight.globalenv Slice.prog) (cell_of q)
    (live (initial_state q m)) events (live (Returnstate (Vint Int.mone) Kstop after)) /\
    replies events = [failure error].
Proof.
  intros q input m error OWN NE FAIL.
  pose proof OWN as [OP [O [LEN LOAD]]]. pose proof O as [SIZE _].
  assert (POS : 0 < requested q) by (destruct input; [contradiction|cbn in LEN; lia]).
  destruct (initial_to_loop (Clight.globalenv Slice.prog) q m) as [le [REGS INIT]].
  pose proof (loop_to_write _ q 0 le m actual_program_symbols REGS ltac:(lia)) as BEFORE.
  destruct (error_return_exists (suffix q 0) m error) as [after EFFECT].
  { rewrite suffix_zero by exact OP; exact O. }
  assert (AFTER_OWN : write_owned q input after).
  { replace input with ([] ++ input) by reflexivity. eapply write_effect_preserves; eauto. }
  pose proof (write_to_errno _ q 0 le after error actual_program_symbols REGS) as MIDDLE.
  assert (N : (after_write le (failure error)) ! _n = Some (Vlong Int64.mone)) by apply PTree.gss.
  assert (ERRNO : Mem.loadv Mint32 after (Vptr (errno_block q) (Ptrofs.repr (errno_offset q))) = Some (Vint error)).
  { apply errno_loadv; [apply AFTER_OWN|]. eapply failure_errno in EFFECT; exact EFFECT. }
  pose proof (errno_error_to_return (Clight.globalenv Slice.prog) q (after_write le (failure error)) after error N FAIL ERRNO) as END.
  destruct (path_source_steps _ (cell_of q) _ _ (path_trans _ _ _ _ INIT BEFORE)) as [b B].
  destruct (path_source_steps _ (cell_of q) _ _ MIDDLE) as [c C].
  destruct (path_source_steps _ (cell_of q) _ _ END) as [a A].
  exists (repeat (source_step E0) b ++ io_step (suffix q 0) (failure error) ::
    (repeat (source_step E0) c ++ errno_step :: repeat (source_step E0) a)), after.
  split.
  - eapply steps_trans; [exact B|]. econstructor.
    + eapply effect with (q := suffix q 0); [constructor; reflexivity|exact EFFECT].
    + eapply steps_trans; [exact C|]. econstructor; [|exact A]. apply errno_address.
      all: destruct AFTER_OWN as [_ [[_ [_ [_ [EO [EW [ACCESS _]]]]]] _]]; assumption.
  - rewrite replies_app, replies_internal; cbn. rewrite replies_app, replies_internal; cbn.
    rewrite replies_internal; reflexivity.
Qed.

Theorem source_zero_return : forall q input m,
  write_owned q input m -> input <> [] ->
  exists events, steps (Clight.globalenv Slice.prog) (cell_of q)
    (live (initial_state q m)) events (live (Returnstate (Vint Int.mone) Kstop m)) /\
    replies events = [zero None].
Proof.
  intros q input m OWN NE.
  pose proof OWN as [OP [O [LEN LOAD]]]. pose proof O as [SIZE _].
  assert (POS : 0 < requested q) by (destruct input; [contradiction|cbn in LEN; lia]).
  destruct (initial_to_loop (Clight.globalenv Slice.prog) q m) as [le [REGS INIT]].
  pose proof (loop_to_write _ q 0 le m actual_program_symbols REGS ltac:(lia)) as BEFORE.
  destruct (path_source_steps _ (cell_of q) _ _ (path_trans _ _ _ _ INIT BEFORE)) as [b B].
  destruct (path_source_steps (Clight.globalenv Slice.prog) (cell_of q) _ _ (write_zero_to_return _ le m None)) as [a A].
  exists (repeat (source_step E0) b ++ io_step (suffix q 0) (zero None) :: repeat (source_step E0) a); split.
  - eapply steps_trans; [exact B|]. econstructor; [|exact A].
    eapply effect with (q := suffix q 0) (r := zero None); [constructor; reflexivity|].
    apply zero_return_exists. rewrite suffix_zero by exact OP; exact O.
  - rewrite replies_app, replies_internal; cbn; rewrite replies_internal; reflexivity.
Qed.

Lemma emitted_internal : forall n, emitted_trace (repeat (source_step E0) n) = [].
Proof. induction n; cbn; auto. Qed.
Lemma emitted_wait : forall n, emitted_trace (repeat wait_step n) = [].
Proof. induction n; cbn; auto. Qed.

Lemma replies_wait : forall n, replies (repeat wait_step n) = [].
Proof. induction n; cbn; auto. Qed.

Theorem source_wait_then_partial_loss : forall n q first rest m,
  write_owned q (first ++ rest) m -> first <> [] ->
  exists events, steps (Clight.globalenv Slice.prog) (cell_of q)
    (live (initial_state q m)) events (dead m) /\
    emitted_trace events = first /\ replies events = [] /\
    exists before, events = repeat (source_step E0) before ++
      (repeat wait_step n ++ [partial_loss (suffix q 0) first None]).
Proof.
  intros n q first rest m OWN NE.
  pose proof OWN as [OP [O [LEN LOAD]]]. pose proof O as [SIZE _].
  assert (POS : 0 < Z.of_nat (length first) <= requested q).
  { rewrite app_length, Nat2Z.inj_add in LEN. destruct first; [contradiction|].
    change (Z.of_nat (S (length first)) + Z.of_nat (length rest) = requested q) in LEN.
    change (0 < Z.of_nat (S (length first)) <= requested q).
    rewrite Nat2Z.inj_succ in *; lia. }
  assert (SUFFIX : owned (suffix q 0) m) by (rewrite suffix_zero by exact OP; exact O).
  destruct (initial_to_loop (Clight.globalenv Slice.prog) q m) as [le [REGS INIT]].
  pose proof (loop_to_write _ q 0 le m actual_program_symbols REGS ltac:(lia)) as BEFORE.
  destruct (path_source_steps _ (cell_of q) _ _ (path_trans _ _ _ _ INIT BEFORE)) as [b B].
  assert (EFFECT : io_return (suffix q 0) m (transfer first None) m).
  { rewrite suffix_zero by exact OP. apply write_returns; auto; try constructor.
    apply load_first with (rest := rest). rewrite LEN; exact LOAD. }
  assert (WAIT : steps (Clight.globalenv Slice.prog) (cell_of q) (live (write_state q 0 le m))
    (repeat wait_step n ++ [partial_loss (suffix q 0) first None]) (dead m)).
  { induction n; cbn.
    - econstructor; [|constructor]. eapply lose_during_io with (q := suffix q 0); [constructor; reflexivity|exact EFFECT].
    - econstructor; [|exact IHn]. eapply waiting with (q := suffix q 0); [eapply at_io with (q := suffix q 0); reflexivity|exact SUFFIX]. }
  exists (repeat (source_step E0) b ++ (repeat wait_step n ++ [partial_loss (suffix q 0) first None])); split.
  - eapply steps_trans; eauto.
  - split.
    + unfold emitted_trace at 1. rewrite flat_map_app. fold (emitted_trace (repeat (source_step E0) b)).
      rewrite emitted_internal. cbn. rewrite flat_map_app. fold (emitted_trace (repeat wait_step n)).
      rewrite emitted_wait; cbn; apply app_nil_r.
    + split.
      * rewrite replies_app, replies_internal; cbn. rewrite replies_app.
        rewrite replies_wait; reflexivity.
      * exists b; reflexivity.
Qed.
