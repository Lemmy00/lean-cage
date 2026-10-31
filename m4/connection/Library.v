(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-library.memory: Independent byte ownership and local library contracts. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Values Memory Memdata.
Require Import IO WriteMemory WriteBytes.
Import ListNotations.
Open Scope Z_scope.

Record address := { address_block : block; address_offset : Z }.
Definition address_value p := Vptr (address_block p) (Ptrofs.repr (address_offset p)).
Definition span_bounds p (bytes : list Byte.int) :=
  0 <= address_offset p < Ptrofs.modulus /\
  address_offset p + Z.of_nat (length bytes) <= Ptrofs.modulus /\
  Z.of_nat (length bytes) <= Int64.max_unsigned.
Definition readable_bytes m p bytes := span_bounds p bytes /\
  Mem.loadbytes m (address_block p) (address_offset p) (Z.of_nat (length bytes)) =
    Some (map Byte bytes).
Definition c_string m p bytes := Forall (fun b => b <> Byte.zero) bytes /\
  readable_bytes m p (bytes ++ [Byte.zero]).

Fixpoint compare_bytes (left right : list Byte.int) : Datatypes.comparison :=
  match left, right with
  | [], [] => Eq
  | [], _ :: _ => Lt
  | _ :: _, [] => Gt
  | a :: xs, b :: ys =>
      match Z.compare (Byte.unsigned a) (Byte.unsigned b) with
      | Eq => compare_bytes xs ys | other => other end
  end.

Lemma byte_unsigned_injective : forall a b, Byte.unsigned a = Byte.unsigned b -> a = b.
Proof.
  intros a b SAME. rewrite <- (Byte.repr_unsigned a), <- (Byte.repr_unsigned b).
  rewrite SAME; reflexivity.
Qed.

Theorem compare_bytes_equal : forall left right,
  compare_bytes left right = Eq <-> left = right.
Proof.
  induction left as [|a xs IH]; destruct right as [|b ys]; cbn;
    try solve [split; [discriminate|discriminate]]; [tauto|].
  destruct (Z.compare (Byte.unsigned a) (Byte.unsigned b)) eqn:ORDER.
  - apply Z.compare_eq_iff in ORDER. apply byte_unsigned_injective in ORDER; subst b.
    rewrite IH. split; [congruence|intros EQ; inversion EQ; reflexivity].
  - split; [discriminate|]. intros EQ; inversion EQ; subst.
    rewrite Z.compare_refl in ORDER; discriminate.
  - split; [discriminate|]. intros EQ; inversion EQ; subst.
    rewrite Z.compare_refl in ORDER; discriminate.
Qed.

Definition comparison_result order value :=
  match order with Eq => value = Int.zero | Lt => Int.signed value < 0 | Gt => 0 < Int.signed value end.
Definition comparison_value order :=
  match order with Eq => Int.zero | Lt => Int.mone | Gt => Int.one end.

Theorem comparison_result_exists : forall order,
  comparison_result order (comparison_value order).
Proof. destruct order; cbn [comparison_result comparison_value]; [reflexivity| |]; vm_compute; congruence. Qed.

Theorem comparison_result_zero : forall order value,
  comparison_result order value ->
  Int.eq value Int.zero = match order with Eq => true | _ => false end.
Proof.
  intros order value RESULT. destruct order; cbn in RESULT |- *.
  - subst; apply Int.eq_true.
  - apply Int.eq_false. intros EQ; subst. change (0 < 0) in RESULT; lia.
  - apply Int.eq_false. intros EQ; subst. change (0 < 0) in RESULT; lia.
Qed.

Lemma readable_bytes_unique : forall m p xs ys,
  readable_bytes m p xs -> readable_bytes m p ys -> length xs = length ys -> xs = ys.
Proof.
  intros m p xs ys [_ X] [_ Y] LEN. rewrite LEN in X.
  apply map_byte_injective; congruence.
Qed.

Lemma terminated_prefix_unique : forall xs ys rest,
  Forall (fun b => b <> Byte.zero) xs -> Forall (fun b => b <> Byte.zero) ys ->
  ys ++ [Byte.zero] = (xs ++ [Byte.zero]) ++ rest -> xs = ys.
Proof.
  induction xs as [|x xs IH]; destruct ys as [|y ys]; intros rest X Y EQ; cbn in EQ; auto.
  - inversion EQ; subst y. inversion Y; contradiction.
  - inversion EQ; subst x. inversion X; contradiction.
  - inversion EQ; subst y. inversion X; inversion Y; subst. f_equal; eapply IH; eassumption.
Qed.

Theorem c_string_unique : forall m p xs ys,
  c_string m p xs -> c_string m p ys -> xs = ys.
Proof.
  intros m p xs ys [X [_ LOADX]] [Y [_ LOADY]].
  destruct (Nat.le_ge_cases (length xs) (length ys)).
  - destruct (load_prefix _ _ _ _ _ LOADY LOADX) as [rest PREFIX].
    { rewrite !app_length; cbn; lia. }
    eapply terminated_prefix_unique; eassumption.
  - destruct (load_prefix _ _ _ _ _ LOADX LOADY) as [rest PREFIX].
    { rewrite !app_length; cbn; lia. }
    symmetry; eapply terminated_prefix_unique; eassumption.
Qed.

Definition memcmp_owned m left right count :=
  exists xs ys, readable_bytes m left xs /\ readable_bytes m right ys /\
    Z.of_nat (length xs) = count /\ length xs = length ys.
Definition strcmp_owned m left right :=
  exists xs ys, c_string m left xs /\ c_string m right ys.
Definition memcmp_result m left right count value :=
  exists xs ys, readable_bytes m left xs /\ readable_bytes m right ys /\
    Z.of_nat (length xs) = count /\ length xs = length ys /\
    comparison_result (compare_bytes xs ys) value.
Definition strcmp_result m left right value :=
  exists xs ys, c_string m left xs /\ c_string m right ys /\
    comparison_result (compare_bytes xs ys) value.

Theorem memcmp_progress : forall m left right count,
  memcmp_owned m left right count -> exists value, memcmp_result m left right count value.
Proof.
  intros m left right count [xs [ys [X [Y [SIZE LEN]]]]].
  exists (comparison_value (compare_bytes xs ys)), xs, ys.
  split; [exact X|]. split; [exact Y|]. split; [exact SIZE|].
  split; [exact LEN|apply comparison_result_exists].
Qed.

Theorem strcmp_progress : forall m left right,
  strcmp_owned m left right -> exists value, strcmp_result m left right value.
Proof.
  intros m left right [xs [ys [X Y]]].
  exists (comparison_value (compare_bytes xs ys)), xs, ys.
  split; [exact X|]. split; [exact Y|apply comparison_result_exists].
Qed.

Theorem memcmp_zero_iff : forall m left right xs ys value,
  readable_bytes m left xs -> readable_bytes m right ys -> length xs = length ys ->
  memcmp_result m left right (Z.of_nat (length xs)) value ->
  (Int.eq value Int.zero = true <-> xs = ys).
Proof.
  intros m left right xs ys value X Y LEN [a [b [A [B [SIZE [AB RESULT]]]]]].
  assert (a = xs) by (eapply readable_bytes_unique; [exact A|exact X|lia]); subst a.
  assert (b = ys) by (eapply readable_bytes_unique; [exact B|exact Y|lia]); subst b.
  rewrite (comparison_result_zero _ _ RESULT), <- compare_bytes_equal.
  destruct (compare_bytes xs ys); split; congruence.
Qed.

Theorem strcmp_zero_iff : forall m left right xs ys value,
  c_string m left xs -> c_string m right ys -> strcmp_result m left right value ->
  (Int.eq value Int.zero = true <-> xs = ys).
Proof.
  intros m left right xs ys value X Y [a [b [A [B RESULT]]]].
  assert (a = xs) by (eapply c_string_unique; eassumption); subst a.
  assert (b = ys) by (eapply c_string_unique; eassumption); subst b.
  rewrite (comparison_result_zero _ _ RESULT), <- compare_bytes_equal.
  destruct (compare_bytes xs ys); split; congruence.
Qed.

Definition copy_disjoint source destination count :=
  address_block source <> address_block destination \/
  address_offset source + count <= address_offset destination \/
  address_offset destination + count <= address_offset source.
Definition copy_owned m source destination bytes :=
  readable_bytes m source bytes /\ span_bounds destination bytes /\
  Mem.range_perm m (address_block destination) (address_offset destination)
    (address_offset destination + Z.of_nat (length bytes)) Cur Writable /\
  copy_disjoint source destination (Z.of_nat (length bytes)).
Definition copy_result m source destination bytes after :=
  copy_owned m source destination bytes /\
  Mem.storebytes m (address_block destination) (address_offset destination) (map Byte bytes) = Some after.

Theorem copy_progress : forall m source destination bytes,
  copy_owned m source destination bytes -> exists after, copy_result m source destination bytes after.
Proof.
  intros m source destination bytes OWN. pose proof OWN as [_ [_ [RANGE _]]].
  rewrite <- (map_length Byte bytes) in RANGE.
  destruct (Mem.range_perm_storebytes _ _ _ _ RANGE) as [after STORE].
  exists after; split; assumption.
Qed.

Theorem copy_exact_content : forall m source destination bytes after,
  copy_result m source destination bytes after ->
  Mem.loadbytes after (address_block destination) (address_offset destination)
    (Z.of_nat (length bytes)) = Some (map Byte bytes).
Proof.
  intros m source destination bytes after [_ STORE].
  rewrite <- (map_length Byte bytes). eapply Mem.loadbytes_storebytes_same; eassumption.
Qed.

Theorem copy_preserves_permissions : forall m source destination bytes after,
  copy_result m source destination bytes after ->
  forall b pos kind perm, Mem.perm after b pos kind perm <-> Mem.perm m b pos kind perm.
Proof.
  intros m source destination bytes after [_ STORE]; intros.
  split; eauto using Mem.perm_storebytes_1, Mem.perm_storebytes_2.
Qed.

Theorem copy_preserves_outside : forall m source destination bytes after,
  copy_result m source destination bytes after ->
  Mem.unchanged_on (outside_bytes (address_block destination) (address_offset destination) (length bytes)) m after.
Proof.
  intros m source destination bytes after [_ STORE]. eapply Mem.storebytes_unchanged_on; [exact STORE|].
  rewrite map_length. unfold outside_bytes; intros pos BOUND [NE|[LOW|HIGH]]; lia.
Qed.

Theorem copy_preserves_source : forall m source destination bytes after,
  copy_result m source destination bytes after -> readable_bytes after source bytes.
Proof.
  intros m source destination bytes after [[READ [_ [_ SEP]]] STORE].
  destruct READ as [BOUNDS LOAD]. split; [assumption|]. rewrite <- LOAD.
  eapply Mem.loadbytes_storebytes_other; [exact STORE|lia|]. rewrite map_length.
  unfold copy_disjoint in SEP; destruct SEP as [NE|[BEFORE|AFTER]]; auto.
Qed.

(* The schedule can name any in-range position in any order. It is not a prefix
   restriction and is not required to be a permutation. A lost copy never returns. *)
Inductive partial_copy destination (bytes : list Byte.int) : mem -> list nat -> mem -> Prop :=
| partial_copy_done : forall m, partial_copy destination bytes m [] m
| partial_copy_next : forall m index byte mid rest after,
    nth_error bytes index = Some byte ->
    Mem.store Mint8unsigned m (address_block destination)
      (address_offset destination + Z.of_nat index) (Vint (Int.repr (Byte.unsigned byte))) = Some mid ->
    partial_copy destination bytes mid rest after ->
    partial_copy destination bytes m (index :: rest) after.

Theorem partial_copy_permissions : forall destination bytes m schedule after,
  partial_copy destination bytes m schedule after ->
  forall b pos kind perm, Mem.perm after b pos kind perm <-> Mem.perm m b pos kind perm.
Proof.
  intros destination bytes m schedule after RUN; induction RUN; intros; [tauto|].
  rewrite IHRUN. split; eauto using Mem.perm_store_1, Mem.perm_store_2.
Qed.

Theorem partial_copy_outside : forall destination bytes m schedule after,
  partial_copy destination bytes m schedule after ->
  Mem.unchanged_on (outside_bytes (address_block destination) (address_offset destination) (length bytes)) m after.
Proof.
  intros destination bytes m schedule after RUN; induction RUN; [apply Mem.unchanged_on_refl|].
  eapply Mem.unchanged_on_trans; [|exact IHRUN]. eapply Mem.store_unchanged_on; [exact H0|].
  assert (INDEX : (index < length bytes)%nat) by (apply nth_error_Some; rewrite H; discriminate).
  unfold outside_bytes. intros pos RANGE [NE|[LOW|HIGH]]; cbn in RANGE; lia.
Qed.

Theorem partial_copy_exists : forall destination bytes schedule m,
  Forall (fun index => (index < length bytes)%nat) schedule ->
  Mem.range_perm m (address_block destination) (address_offset destination)
    (address_offset destination + Z.of_nat (length bytes)) Cur Writable ->
  exists after, partial_copy destination bytes m schedule after.
Proof.
  intros destination bytes schedule; induction schedule as [|index rest IH]; intros m INDICES RANGE.
  - exists m; constructor.
  - inversion INDICES; subst.
    destruct (nth_error bytes index) as [byte|] eqn:BYTE.
    2: { apply nth_error_None in BYTE; lia. }
    destruct (Mem.valid_access_store m Mint8unsigned (address_block destination)
      (address_offset destination + Z.of_nat index) (Vint (Int.repr (Byte.unsigned byte)))) as [mid STORE].
    { split; [|apply Z.divide_1_l]. red; intros pos BOUND. apply RANGE. cbn in BOUND; lia. }
    destruct (IH mid H2) as [after TAIL].
    { red; intros. eapply Mem.perm_store_1; [exact STORE|apply RANGE; assumption]. }
    exists after; econstructor; eassumption.
Qed.

Theorem partial_copy_source : forall m source destination bytes schedule after,
  copy_owned m source destination bytes -> partial_copy destination bytes m schedule after ->
  readable_bytes after source bytes.
Proof.
  intros m source destination bytes schedule after OWN RUN.
  destruct OWN as [[BOUNDS LOAD] [_ [_ SEP]]]. split; [exact BOUNDS|].
  revert LOAD. induction RUN; intros LOAD; [assumption|]. apply IHRUN.
  rewrite <- LOAD. eapply Mem.loadbytes_store_other; [exact H0|].
  assert (INDEX : (index < length bytes)%nat) by (apply nth_error_Some; rewrite H; discriminate).
  unfold copy_disjoint in SEP; cbn. destruct SEP as [NE|[BEFORE|AFTER]]; auto; lia.
Qed.

Require Import Readers.

Theorem allocated_comparison_spans : forall base xs ys,
  Z.of_nat (length (xs ++ ys)) <= 160 ->
  exists allocated b m,
    Mem.alloc base 0 (Z.of_nat (length (xs ++ ys))) = (allocated, b) /\
    Mem.storebytes allocated b 0 (map Byte (xs ++ ys)) = Some m /\
    readable_bytes m {|address_block := b; address_offset := 0|} xs /\
    readable_bytes m {|address_block := b; address_offset := Z.of_nat (length xs)|} ys.
Proof.
  intros base xs ys SIZE. destruct (allocated_bytes base (xs ++ ys))
    as [allocated [b [m [ALLOC [STORE LOAD]]]]].
  exists allocated, b, m. split; [exact ALLOC|]. split; [exact STORE|].
  assert (X : 0 <= Z.of_nat (length xs) <= 160) by (rewrite app_length, Nat2Z.inj_add in SIZE; lia).
  assert (Y : 0 <= Z.of_nat (length ys) <= 160) by (rewrite app_length, Nat2Z.inj_add in SIZE; lia).
  split; split.
  - unfold span_bounds; cbn [address_offset].
    change Ptrofs.modulus with 18446744073709551616.
    change Int64.max_unsigned with 18446744073709551615. lia.
  - exact (load_first _ _ _ _ _ LOAD).
  - unfold span_bounds; cbn [address_offset].
    change Ptrofs.modulus with 18446744073709551616.
    change Int64.max_unsigned with 18446744073709551615. lia.
  - exact (load_suffix _ _ _ _ _ LOAD).
Qed.

Theorem arbitrary_c_string_pair : forall (base : mem) xs ys,
  Forall (fun b => b <> Byte.zero) xs -> Forall (fun b => b <> Byte.zero) ys ->
  Z.of_nat (length xs + length ys) <= 158 ->
  exists m left right, c_string m left xs /\ c_string m right ys.
Proof.
  intros base xs ys X Y SIZE.
  destruct (allocated_comparison_spans base (xs ++ [Byte.zero]) (ys ++ [Byte.zero]))
    as [allocated [b [m [_ [_ [LEFT RIGHT]]]]]].
  { rewrite !app_length, !Nat2Z.inj_add in *; cbn; lia. }
  exists m, {|address_block := b; address_offset := 0|},
    {|address_block := b; address_offset := Z.of_nat (length (xs ++ [Byte.zero]))|}.
  split; split; assumption.
Qed.

Theorem arbitrary_copy_input : forall base (bytes : list Byte.int),
  Z.of_nat (length bytes) <= 160 ->
  exists allocated b m,
    Mem.alloc base 0 (2 * Z.of_nat (length bytes)) = (allocated, b) /\
    Mem.storebytes allocated b 0 (map Byte bytes) = Some m /\
    copy_owned m {|address_block := b; address_offset := 0|}
      {|address_block := b; address_offset := Z.of_nat (length bytes)|} bytes.
Proof.
  intros base bytes SIZE.
  destruct (Mem.alloc base 0 (2 * Z.of_nat (length bytes))) as [allocated b] eqn:ALLOC.
  assert (RANGE : Mem.range_perm allocated b 0 (0 + Z.of_nat (length (map Byte bytes))) Cur Writable).
  { rewrite map_length. red; intros pos BOUND. eapply Mem.perm_implies.
    - eapply Mem.perm_alloc_2; [exact ALLOC|lia].
    - constructor. }
  destruct (Mem.range_perm_storebytes _ _ _ _ RANGE) as [m STORE].
  exists allocated, b, m. split; [reflexivity|]. split; [exact STORE|].
  split.
  - split.
    + unfold span_bounds; cbn [address_offset].
      change Ptrofs.modulus with 18446744073709551616.
      change Int64.max_unsigned with 18446744073709551615. lia.
    + cbn [address_block address_offset]. rewrite <- (map_length Byte bytes).
      eapply Mem.loadbytes_storebytes_same; exact STORE.
  - split.
    + unfold span_bounds; cbn [address_offset].
      change Ptrofs.modulus with 18446744073709551616.
      change Int64.max_unsigned with 18446744073709551615. lia.
    + split.
      * red; intros pos BOUND. eapply Mem.perm_storebytes_1; [exact STORE|].
        eapply Mem.perm_implies.
        -- eapply Mem.perm_alloc_2; [exact ALLOC|cbn in BOUND; lia].
        -- constructor.
      * unfold copy_disjoint; cbn. right; left; lia.
Qed.

Theorem copy_nonprefix_schedule_exists : forall (base : mem) a b c,
  exists m source destination after,
    copy_owned m source destination [a;b;c] /\
    partial_copy destination [a;b;c] m [2%nat;0%nat] after /\
    readable_bytes after source [a;b;c] /\
    Mem.unchanged_on (outside_bytes (address_block destination) (address_offset destination) 3) m after.
Proof.
  intros base a b c. destruct (arbitrary_copy_input base [a;b;c] ltac:(cbn; lia))
    as [allocated [block [m [_ [_ OWN]]]]].
  pose proof OWN as [_ [_ [RANGE _]]].
  destruct (partial_copy_exists {|address_block := block; address_offset := 3|}
    [a;b;c] [2%nat;0%nat] m) as [after RUN].
  { repeat constructor; cbn; lia. }
  { exact RANGE. }
  eexists m, _, _, after. split; [exact OWN|]. split; [exact RUN|].
  split; [eapply partial_copy_source; eassumption|exact (partial_copy_outside _ _ _ _ _ RUN)].
Qed.

Lemma readable_address_identity : forall m a b xs ys,
  readable_bytes m a xs -> readable_bytes m b ys -> address_value a = address_value b -> a = b.
Proof.
  intros m [ab ao] [bb bo] xs ys [[A _] _] [[B _] _] EQ.
  unfold address_value in EQ; cbn in *.
  assert (BLOCK : ab = bb) by congruence; subst bb.
  assert (SAME : Ptrofs.unsigned (Ptrofs.repr ao) = Ptrofs.unsigned (Ptrofs.repr bo)) by congruence.
  rewrite !Ptrofs.unsigned_repr in SAME by (unfold Ptrofs.max_unsigned; lia).
  subst bo; reflexivity.
Qed.

Lemma c_string_address_identity : forall m a b xs ys,
  c_string m a xs -> c_string m b ys -> address_value a = address_value b -> a = b.
Proof.
  intros m a b xs ys [_ A] [_ B] EQ. eapply readable_address_identity; eassumption.
Qed.

Lemma readable_address_components : forall m a b xs ys,
  readable_bytes m a xs -> readable_bytes m b ys -> address_block a = address_block b ->
  Ptrofs.unsigned (Ptrofs.repr (address_offset a)) = Ptrofs.unsigned (Ptrofs.repr (address_offset b)) -> a = b.
Proof.
  intros m [ab ao] [bb bo] xs ys [[A _] _] [[B _] _] BLOCK SAME.
  cbn in *; subst bb.
  rewrite !Ptrofs.unsigned_repr in SAME by (unfold Ptrofs.max_unsigned; lia).
  subst bo; reflexivity.
Qed.
