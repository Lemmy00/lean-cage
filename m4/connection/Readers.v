(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-effects.readers: All source prefixes of the maintained frame readers. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events
  Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Slice Codec Machine ClightSteps WriteAll Deterministic ErrorNumber.
Import ListNotations.
Open Scope Z_scope.

Definition initial f block ofs k m :=
  Callstate (Internal f) [Vptr block ofs] k m.

Lemma reader_entry : forall ge f block ofs k m,
  f = f_get32 \/ f = f_get64 ->
  edge ge (initial f block ofs k m)
    (State f (fn_body f) k empty_env
      (PTree.set _p (Vptr block ofs) (create_undef_temps (fn_temps f))) m).
Proof.
  intros ge f block ofs k m READER. destruct READER; subst f;
    split; [exact I| |exact I|]; split.
  1,3: apply step_internal_function; constructor;
    [constructor|repeat constructor; simpl; tauto|
     unfold list_disjoint, var_names; simpl; intros x y [X|X] [Y|[Y|[Y|Y]]];
       try contradiction; subst; discriminate|constructor|reflexivity].
  all: split; [reflexivity|]; intros t other STEP; inversion STEP; subst;
    match goal with H : function_entry2 _ _ _ _ _ _ _ |- _ => inversion H; subst end;
    match goal with H : alloc_variables _ _ _ _ _ _ |- _ => inversion H; subst end;
    match goal with H : bind_parameter_temps _ _ _ = _ |- _ => cbn in H; inversion H; subst end;
    auto.
Qed.

Definition loads32 m block ofs a b c d :=
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 0))) = Some (Vint a) /\
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 1))) = Some (Vint b) /\
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 2))) = Some (Vint c) /\
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 3))) = Some (Vint d).
Definition loads64 m block ofs a b c d e f g h :=
  loads32 m block ofs a b c d /\
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 4))) = Some (Vint e) /\
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 5))) = Some (Vint f) /\
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 6))) = Some (Vint g) /\
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 7))) = Some (Vint h).

(* Unroll only the literal four/eight iterations in the actual source. Each
   certificate checks evaluation, real transition and uniqueness of that step. *)
Ltac reader_load := next_internal;
  [eapply edge_set; eapply value_load; [WriteAll.expression|reflexivity|];
    cbn; match goal with |- context [Ptrofs.mul ?x ?y] =>
      let product := eval vm_compute in (Ptrofs.mul x y) in
      change (Ptrofs.mul x y) with product end; eassumption|].
Ltac reader_iteration :=
  route_errno; route_errno; branch_errno true; [reflexivity|];
  route_errno; route_errno; reader_load; route_errno; set_errno;
  route_errno; set_errno; route_errno.
Ltac reader_end :=
  route_errno; route_errno; branch_errno false; [reflexivity|];
  route_errno; route_errno; route_errno; return_errno.

Theorem get32_execution : forall ge cell m block ofs a b c d k,
  loads32 m block ofs a b c d ->
  exists events, execution ge cell (initial f_get32 block ofs k m) events
    (Returnstate (Vint (get32_word a b c d)) (call_cont k) m) /\
    length events = 59%nat /\ events = repeat (source_step E0) 59.
Proof.
  intros ge cell m block ofs a b c d k [A [B [C D]]]. eexists; split.
  - next_internal; [apply reader_entry; auto|]. unfold f_get32; simpl fn_body.
    route_errno; set_errno; route_errno; route_errno; route_errno; set_errno; route_errno.
    do 4 reader_iteration. reader_end.
  - split; reflexivity.
Qed.

Theorem get64_execution : forall ge cell m block ofs a b c d e f g h k,
  loads64 m block ofs a b c d e f g h ->
  exists events, execution ge cell (initial f_get64 block ofs k m) events
    (Returnstate (Vlong (get64_word a b c d e f g h)) (call_cont k) m) /\
    length events = 103%nat /\ events = repeat (source_step E0) 103.
Proof.
  intros ge cell m block ofs a b c d e f g h k [[A [B [C D]]] [E [F [G H]]]].
  eexists; split.
  - next_internal; [apply reader_entry; auto|]. unfold f_get64; simpl fn_body.
    route_errno; set_errno; route_errno; route_errno; route_errno; set_errno; route_errno.
    do 8 reader_iteration. reader_end.
  - split; reflexivity.
Qed.

(* The independent input contract is initialized readable bytes and no address
   wrap. The expected value is an expression over those bytes, not an assumed
   execution or an assumed returned result. *)
Inductive reader_input m block ofs : function -> val -> nat -> Prop :=
| input32 : forall a b c d,
    Ptrofs.unsigned ofs + 4 <= Ptrofs.modulus -> loads32 m block ofs a b c d ->
    reader_input m block ofs f_get32 (Vint (get32_word a b c d)) 59
| input64 : forall a b c d e f g h,
    Ptrofs.unsigned ofs + 8 <= Ptrofs.modulus -> loads64 m block ofs a b c d e f g h ->
    reader_input m block ofs f_get64 (Vlong (get64_word a b c d e f g h)) 103.

Theorem reader_execution : forall ge cell m block ofs f value count k,
  reader_input m block ofs f value count ->
  execution ge cell (initial f block ofs k m) (repeat (source_step E0) count)
    (Returnstate value (call_cont k) m).
Proof.
  intros ge cell m block ofs f value count k INPUT; destruct INPUT.
  - destruct (get32_execution ge cell m block ofs a b c d k H0) as [events [RUN [_ EVENTS]]].
    subst; assumption.
  - destruct (get64_execution ge cell m block ofs a b c d e f g h k H0) as [events [RUN [_ EVENTS]]].
    subst; assumption.
Qed.

Theorem reader_success_exists : forall cell m block ofs f value count k,
  reader_input m block ofs f value count ->
  steps (Clight.globalenv Slice.prog) cell (live (initial f block ofs k m))
    (repeat (source_step E0) count) (live (Returnstate value (call_cont k) m)).
Proof. intros; apply execution_actual; apply reader_execution; assumption. Qed.

Theorem reader_return_exact : forall cell m block ofs f value count events actual after,
  reader_input m block ofs f value count ->
  steps (Clight.globalenv Slice.prog) cell (live (initial f block ofs Kstop m)) events
    (live (Returnstate actual Kstop after)) ->
  actual = value /\ after = m /\ events = repeat (source_step E0) count.
Proof.
  intros. eapply execution_return_exact;
    [exact (reader_execution _ cell _ _ _ _ _ _ Kstop H)|exact H0].
Qed.

Lemma firstn_repeat : forall (A : Type) (x : A) n count,
  firstn n (repeat x count) = repeat x (Nat.min n count).
Proof. intros A x n; induction n; destruct count; cbn; auto; f_equal; auto. Qed.

Theorem reader_all_prefixes : forall cell m block ofs f value count events target,
  reader_input m block ofs f value count ->
  steps (Clight.globalenv Slice.prog) cell (live (initial f block ofs Kstop m)) events target ->
  routine_memory target = m /\ (length events <= S count)%nat /\
  ((exists n s, (n <= count)%nat /\ events = repeat (source_step E0) n /\ target = live s) \/
   (exists n, (n <= count)%nat /\ events = repeat (source_step E0) n ++ [loss_step] /\ target = dead m)).
Proof.
  intros cell m block ofs f value count events target INPUT RUN.
  pose proof (reader_execution (Clight.globalenv Slice.prog) cell _ _ _ _ _ _ Kstop INPUT) as SCRIPT.
  split; [eapply execution_preserves_memory; eassumption|]. split.
  { rewrite <- (repeat_length (source_step E0) count). eapply execution_length_bound; eassumption. }
  destruct (execution_classifies_all _ _ _ _ _ _ SCRIPT _ _ RUN)
    as [[rest [s [TARGET [SCHED TAIL]]]]|[before [rest [SCHED [EVENTS TARGET]]]]].
  - left. exists (length events), s. assert (BOUND : (length events <= count)%nat).
    { apply (f_equal (@length event)) in SCHED. rewrite repeat_length, app_length in SCHED; lia. }
    split; [exact BOUND|].
    split; [|assumption].
    apply (f_equal (firstn (length events))) in SCHED.
    rewrite firstn_app, firstn_all, Nat.sub_diag, app_nil_r, firstn_repeat in SCHED.
    rewrite Nat.min_l in SCHED by exact BOUND. symmetry; assumption.
  - right. exists (length before). assert (BOUND : (length before <= count)%nat).
    { apply (f_equal (@length event)) in SCHED. rewrite repeat_length, app_length in SCHED; lia. }
    split; [exact BOUND|]. split; [|exact TARGET].
    apply (f_equal (firstn (length before))) in SCHED.
    rewrite firstn_app, firstn_all, Nat.sub_diag, app_nil_r, firstn_repeat in SCHED.
    rewrite Nat.min_l in SCHED by exact BOUND. congruence.
Qed.

Theorem reader_defined_prefix : forall cell m block ofs f value count events s,
  reader_input m block ofs f value count ->
  steps (Clight.globalenv Slice.prog) cell (live (initial f block ofs Kstop m)) events (live s) ->
  s = Returnstate value Kstop m \/
    exists next, step (Clight.globalenv Slice.prog) cell (live s) (source_step E0) (live next).
Proof.
  intros cell m block ofs f value count events s INPUT RUN.
  pose proof (reader_execution (Clight.globalenv Slice.prog) cell _ _ _ _ _ _ Kstop INPUT) as SCRIPT.
  destruct (execution_classifies_all _ _ _ _ _ _ SCRIPT _ _ RUN)
    as [[rest [s' [TARGET [SCHED TAIL]]]]|[before [rest [_ [_ TARGET]]]]]; try discriminate.
  inversion TARGET; subst s'.
  inversion TAIL; subst; [left; reflexivity|]. right.
  destruct H as [_ [REAL _]]. exists next.
  assert (EVENT : ev = source_step E0).
  { assert (IN : In ev (repeat (source_step E0) count)).
    { rewrite SCHED. apply in_or_app; right; left; reflexivity. }
    apply repeat_spec in IN; assumption. }
  subst; exact REAL.
Qed.

Theorem reader_loss_every_prefix : forall cell m block ofs f value count n,
  reader_input m block ofs f value count -> (n <= count)%nat ->
  exists mid,
    steps (Clight.globalenv Slice.prog) cell (live (initial f block ofs Kstop m))
      (repeat (source_step E0) n) (live mid) /\
    steps (Clight.globalenv Slice.prog) cell (live (initial f block ofs Kstop m))
      (repeat (source_step E0) n ++ [loss_step]) (dead m).
Proof.
  intros cell m block ofs f value count n INPUT BOUND.
  pose proof (reader_execution (Clight.globalenv Slice.prog) cell _ _ _ _ _ _ Kstop INPUT) as SCRIPT.
  pose proof (execution_loss_every_prefix _ _ _ _ _ n SCRIPT) as LOSS.
  rewrite firstn_repeat, Nat.min_l in LOSS by exact BOUND. exact LOSS.
Qed.

Require Import WriteMemory.
Definition byte_word (byte : Byte.int) := Int.repr (Byte.unsigned byte).

Lemma decode_byte : forall byte, decode_val Mint8unsigned [Byte byte] = Vint (byte_word byte).
Proof.
  intros byte. change (Vint (Int.zero_ext 8 (Int.repr (Byte.unsigned byte + 256 * 0))) =
    Vint (byte_word byte)). rewrite Z.mul_0_r, Z.add_0_r.
  f_equal. rewrite <- (Int.repr_unsigned (Int.zero_ext 8 (Int.repr (Byte.unsigned byte)))).
  rewrite Int.zero_ext_mod by (change (0 <= 8 < 32); lia).
  pose proof (Byte.unsigned_range byte) as RANGE.
  change (0 <= Byte.unsigned byte < 256) in RANGE.
  rewrite Int.unsigned_repr by (change (0 <= Byte.unsigned byte <= 4294967295); lia).
  change (Int.repr (Byte.unsigned byte mod 256) = byte_word byte).
  rewrite Z.mod_small; [reflexivity|exact RANGE].
Qed.

Lemma load_byte : forall m block before byte after,
  Z.of_nat (length before) + 1 <= Ptrofs.modulus ->
  Mem.loadbytes m block 0 (Z.of_nat (length (before ++ byte :: after))) =
    Some (map Byte (before ++ byte :: after)) ->
  Mem.loadv Mint8unsigned m
    (Vptr block (Ptrofs.add Ptrofs.zero (Ptrofs.repr (Z.of_nat (length before))))) =
    Some (Vint (byte_word byte)).
Proof.
  intros m block before byte after BOUND LOAD.
  pose proof (load_suffix _ _ _ _ _ LOAD) as SUFFIX. rewrite Z.add_0_l in SUFFIX.
  pose proof (load_first m block (Z.of_nat (length before)) [byte] after SUFFIX) as SINGLE.
  assert (SAME : Mem.load Mint8unsigned m block (Z.of_nat (length before)) =
    Some (Vint (byte_word byte))).
  { rewrite <- decode_byte. eapply Mem.loadbytes_load; [exact SINGLE|apply Z.divide_1_l]. }
  rewrite Ptrofs.add_zero_l. unfold Mem.loadv.
  rewrite Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; lia).
  destruct (zle (Z.of_nat (length before) + size_chunk Mint8unsigned) Ptrofs.modulus);
    [exact SAME|cbn in *; lia].
Qed.

Theorem allocated_bytes : forall base (bytes : list Byte.int),
  exists allocated block m,
    Mem.alloc base 0 (Z.of_nat (length bytes)) = (allocated, block) /\
    Mem.storebytes allocated block 0 (map Byte bytes) = Some m /\
    Mem.loadbytes m block 0 (Z.of_nat (length bytes)) = Some (map Byte bytes).
Proof.
  intros base bytes.
  destruct (Mem.alloc base 0 (Z.of_nat (length bytes))) as [allocated block] eqn:ALLOC.
  assert (ACCESS : Mem.range_perm allocated block 0
    (0 + Z.of_nat (length (map Byte bytes))) Cur Writable).
  { rewrite map_length. intros i RANGE. eapply Mem.perm_implies.
    - eapply Mem.perm_alloc_2; eauto; lia.
    - constructor. }
  destruct (Mem.range_perm_storebytes _ _ _ _ ACCESS) as [m STORE].
  exists allocated, block, m. split; [reflexivity|]. split; [exact STORE|].
  rewrite <- (map_length Byte bytes). eapply Mem.loadbytes_storebytes_same; eauto.
Qed.

Theorem arbitrary_get32_input : forall (base : mem) a b c d,
  exists m block, reader_input m block Ptrofs.zero f_get32
    (Vint (get32_word (byte_word a) (byte_word b) (byte_word c) (byte_word d))) 59.
Proof.
  intros base a b c d. destruct (allocated_bytes base [a;b;c;d])
    as [allocated [block [m [_ [_ LOAD]]]]].
  exists m, block. apply input32; [change (0 + 4 <= 18446744073709551616); lia|].
  unfold loads32; repeat split.
  - exact (load_byte m block [] a [b;c;d] ltac:(change Ptrofs.modulus with 18446744073709551616; cbn; lia) LOAD).
  - exact (load_byte m block [a] b [c;d] ltac:(change Ptrofs.modulus with 18446744073709551616; cbn; lia) LOAD).
  - exact (load_byte m block [a;b] c [d] ltac:(change Ptrofs.modulus with 18446744073709551616; cbn; lia) LOAD).
  - exact (load_byte m block [a;b;c] d [] ltac:(change Ptrofs.modulus with 18446744073709551616; cbn; lia) LOAD).
Qed.

Theorem arbitrary_get64_input : forall (base : mem) a b c d e f g h,
  exists m block, reader_input m block Ptrofs.zero f_get64
    (Vlong (get64_word (byte_word a) (byte_word b) (byte_word c) (byte_word d)
      (byte_word e) (byte_word f) (byte_word g) (byte_word h))) 103.
Proof.
  intros base a b c d e f g h. destruct (allocated_bytes base [a;b;c;d;e;f;g;h])
    as [allocated [block [m [_ [_ LOAD]]]]].
  exists m, block. apply input64; [change (0 + 8 <= 18446744073709551616); lia|].
  unfold loads64, loads32; repeat split.
  - exact (load_byte m block [] a [b;c;d;e;f;g;h] ltac:(change Ptrofs.modulus with 18446744073709551616; cbn; lia) LOAD).
  - exact (load_byte m block [a] b [c;d;e;f;g;h] ltac:(change Ptrofs.modulus with 18446744073709551616; cbn; lia) LOAD).
  - exact (load_byte m block [a;b] c [d;e;f;g;h] ltac:(change Ptrofs.modulus with 18446744073709551616; cbn; lia) LOAD).
  - exact (load_byte m block [a;b;c] d [e;f;g;h] ltac:(change Ptrofs.modulus with 18446744073709551616; cbn; lia) LOAD).
  - exact (load_byte m block [a;b;c;d] e [f;g;h] ltac:(change Ptrofs.modulus with 18446744073709551616; cbn; lia) LOAD).
  - exact (load_byte m block [a;b;c;d;e] f [g;h] ltac:(change Ptrofs.modulus with 18446744073709551616; cbn; lia) LOAD).
  - exact (load_byte m block [a;b;c;d;e;f] g [h] ltac:(change Ptrofs.modulus with 18446744073709551616; cbn; lia) LOAD).
  - exact (load_byte m block [a;b;c;d;e;f;g] h [] ltac:(change Ptrofs.modulus with 18446744073709551616; cbn; lia) LOAD).
Qed.
