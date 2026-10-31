(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-effects.memory: Byte-aware local contracts; no Linux or compiler claim. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata.
Import ListNotations.
Open Scope Z_scope.

Inductive direction := reading | writing.

Record request := {
  operation : direction;
  descriptor : int;
  buffer_block : block;
  buffer_offset : Z;
  requested : Z;
  errno_block : block;
  errno_offset : Z
}.

Definition separated (q : request) : Prop :=
  buffer_block q <> errno_block q \/
  buffer_offset q + requested q <= errno_offset q \/
  errno_offset q + 4 <= buffer_offset q.

Definition owned (q : request) (m : mem) : Prop :=
  0 <= requested q <= 160 /\
  0 <= buffer_offset q < Ptrofs.modulus /\
  buffer_offset q + requested q <= Ptrofs.modulus /\
  0 <= errno_offset q /\ errno_offset q + 4 <= Ptrofs.modulus /\
  Mem.valid_access m Mint32 (errno_block q) (errno_offset q) Writable /\
  separated q /\
  match operation q with
  | reading => Mem.range_perm m (buffer_block q) (buffer_offset q)
      (buffer_offset q + requested q) Cur Writable
  | writing => exists bytes : list Byte.int,
      Z.of_nat (length bytes) = requested q /\
      Mem.loadbytes m (buffer_block q) (buffer_offset q) (requested q) =
        Some (map Byte bytes)
  end.

(* Success is allowed to leave errno alone or to update it. The update belongs
   to the observation, so an equal reply cannot hide a different TLS mutation. *)
Inductive errno_change (q : request) : mem -> option int -> mem -> Prop :=
| errno_keep : forall m, errno_change q m None m
| errno_set : forall m error m',
    Mem.store Mint32 m (errno_block q) (errno_offset q) (Vint error) = Some m' ->
    errno_change q m (Some error) m'.

Inductive reply :=
| transfer (bytes : list Byte.int) (errno : option int)
| failure (errno : int)
| zero (errno : option int).

Definition returned (r : reply) : int64 :=
  match r with
  | transfer bytes _ => Int64.repr (Z.of_nat (length bytes))
  | failure _ => Int64.mone
  | zero _ => Int64.zero
  end.

Inductive io_return (q : request) (m : mem) : reply -> mem -> Prop :=
| write_returns : forall bytes error m',
    owned q m -> operation q = writing ->
    0 < Z.of_nat (length bytes) <= requested q ->
    Mem.loadbytes m (buffer_block q) (buffer_offset q)
      (Z.of_nat (length bytes)) = Some (map Byte bytes) ->
    errno_change q m error m' ->
    io_return q m (transfer bytes error) m'
| read_returns : forall bytes error copied m',
    owned q m -> operation q = reading ->
    0 < Z.of_nat (length bytes) <= requested q ->
    Mem.storebytes m (buffer_block q) (buffer_offset q) (map Byte bytes) = Some copied ->
    errno_change q copied error m' ->
    io_return q m (transfer bytes error) m'
| error_returns : forall error m',
    owned q m ->
    errno_change q m (Some error) m' ->
    io_return q m (failure error) m'
| zero_returns : forall error m',
    owned q m -> errno_change q m error m' ->
    io_return q m (zero error) m'.

Theorem errno_change_deterministic : forall q m error a b,
  errno_change q m error a -> errno_change q m error b -> a = b.
Proof. intros q m error a b A B; inversion A; inversion B; subst; congruence. Qed.

Theorem io_return_deterministic : forall q m event a b,
  io_return q m event a -> io_return q m event b -> a = b.
Proof.
  intros q m event a b A B; inversion A; inversion B; subst; try congruence.
  all: repeat match goal with
    | H : transfer _ _ = transfer _ _ |- _ => inversion H; clear H; subst
    | H : failure _ = failure _ |- _ => inversion H; clear H; subst
    | H : zero _ = zero _ |- _ => inversion H; clear H; subst
    end; try congruence; try solve [eapply errno_change_deterministic; eauto].
  match goal with
  | A : Mem.storebytes ?m ?b ?o ?bytes = Some ?x,
    B : Mem.storebytes ?m ?b ?o ?bytes = Some ?y |- _ =>
      assert (x = y) by congruence; subst
  end.
  eapply errno_change_deterministic; eauto.
Qed.

Theorem return_bounds : forall q m event m',
  io_return q m event m' ->
  Int64.signed (returned event) = -1 \/
    0 <= Int64.signed (returned event) <= requested q.
Proof.
  intros q m event m' H; inversion H; subst; simpl.
  - right. rewrite Int64.signed_repr; [lia|].
    destruct H0 as [SIZE _]. change (-9223372036854775808 <= Z.of_nat (length bytes) <= 9223372036854775807); lia.
  - right. rewrite Int64.signed_repr; [lia|].
    destruct H0 as [SIZE _]. change (-9223372036854775808 <= Z.of_nat (length bytes) <= 9223372036854775807); lia.
  - left; reflexivity.
  - right. change (0 <= 0 <= requested q). match goal with H : owned q m |- _ => destruct H as [SIZE _]; lia end.
Qed.

Theorem failure_errno : forall q m error m',
  io_return q m (failure error) m' ->
  Mem.load Mint32 m' (errno_block q) (errno_offset q) = Some (Vint error).
Proof.
  intros q m error m' H; inversion H; subst.
  match goal with H : errno_change _ _ _ _ |- _ => inversion H; subst end.
  erewrite Mem.load_store_same by eauto. reflexivity.
Qed.

Theorem errno_change_preserves_buffer : forall q m error m' count,
  separated q -> 0 <= count <= requested q ->
  errno_change q m error m' ->
  Mem.loadbytes m' (buffer_block q) (buffer_offset q) count =
    Mem.loadbytes m (buffer_block q) (buffer_offset q) count.
Proof.
  intros q m error m' count SEP BOUNDS H; inversion H; subst; auto.
  eapply Mem.loadbytes_store_other; eauto.
  unfold separated in SEP. simpl. destruct SEP as [SEP|[SEP|SEP]]; auto; lia.
Qed.

Theorem read_exact_bytes : forall q m bytes error m',
  operation q = reading -> io_return q m (transfer bytes error) m' ->
  Mem.loadbytes m' (buffer_block q) (buffer_offset q)
    (Z.of_nat (length bytes)) = Some (map Byte bytes).
Proof.
  intros q m bytes error m' READ H; inversion H; subst; try congruence.
  erewrite errno_change_preserves_buffer; eauto.
  - rewrite <- (map_length Byte bytes). eapply Mem.loadbytes_storebytes_same; eauto.
  - match goal with H : owned q m |- _ => destruct H as [_ [_ [_ [_ [_ [_ [SEP _]]]]]]]; exact SEP end.
  - lia.
Qed.

Theorem write_buffer_preserved : forall q m bytes error m',
  operation q = writing -> io_return q m (transfer bytes error) m' ->
  Mem.loadbytes m' (buffer_block q) (buffer_offset q) (requested q) =
    Mem.loadbytes m (buffer_block q) (buffer_offset q) (requested q).
Proof.
  intros q m bytes error m' WRITE H; inversion H; subst; try congruence.
  eapply errno_change_preserves_buffer; eauto.
  - match goal with H : owned q m |- _ => destruct H as [_ [_ [_ [_ [_ [_ [SEP _]]]]]]]; exact SEP end.
  - match goal with H : owned q m |- _ => destruct H as [SIZE _]; lia end.
Qed.

Theorem read_outside_preserved : forall q m bytes error m' b ofs count,
  operation q = reading -> io_return q m (transfer bytes error) m' ->
  0 <= count ->
  (b <> buffer_block q \/ ofs + count <= buffer_offset q \/
    buffer_offset q + requested q <= ofs) ->
  (b <> errno_block q \/ ofs + count <= errno_offset q \/ errno_offset q + 4 <= ofs) ->
  Mem.loadbytes m' b ofs count = Mem.loadbytes m b ofs count.
Proof.
  intros q m bytes error m' b ofs count READ H LEN BUF ERR.
  inversion H; subst; try congruence.
  match goal with H : errno_change _ _ _ _ |- _ => inversion H; subst end.
  - eapply Mem.loadbytes_storebytes_other; eauto; try lia. rewrite map_length.
    destruct BUF as [BUF|[BUF|BUF]]; auto; lia.
  - rewrite (Mem.loadbytes_store_other _ _ _ _ _ _ H0 b ofs count) by (simpl; tauto).
    eapply Mem.loadbytes_storebytes_other; eauto; try lia. rewrite map_length.
    destruct BUF as [BUF|[BUF|BUF]]; auto; lia.
Qed.

(* Nonvacuity: actual CompCert allocation/store operations, with independent
   fresh errno and buffer blocks. This is a model witness, not a host syscall. *)
Theorem owned_read_inhabited : exists q m,
  owned q m /\ operation q = reading /\ requested q = 4.
Proof.
  destruct (Mem.alloc Mem.empty 0 4) as [m0 b] eqn:BUF.
  destruct (Mem.alloc m0 0 4) as [m1 eb] eqn:ERR.
  exists {| operation := reading; descriptor := Int.zero;
    buffer_block := b; buffer_offset := 0; requested := 4;
    errno_block := eb; errno_offset := 0 |}, m1.
  assert (NE : b <> eb).
  { pose proof (Mem.alloc_result _ _ _ _ _ BUF).
    pose proof (Mem.alloc_result _ _ _ _ _ ERR).
    pose proof (Mem.nextblock_alloc _ _ _ _ _ BUF). subst; lia. }
  assert (EA : Mem.valid_access m1 Mint32 eb 0 Writable).
  { eapply Mem.valid_access_implies.
    - eapply Mem.valid_access_alloc_same; eauto; simpl; try lia. exists 0; reflexivity.
    - constructor. }
  assert (BA : Mem.range_perm m1 b 0 4 Cur Writable).
  { intros i HI. eapply Mem.perm_alloc_1; eauto.
    eapply Mem.perm_implies; [eapply Mem.perm_alloc_2; eauto; lia|constructor]. }
  split; [|auto]. unfold owned; simpl.
  split; [lia|].
  split; [change (0 <= 0 < 18446744073709551616); lia|].
  split; [change (4 <= 18446744073709551616); lia|].
  split; [lia|].
  split; [change (4 <= 18446744073709551616); lia|].
  split; [exact EA|]. split; [unfold separated; simpl; auto|exact BA].
Qed.

Theorem read_transfer_exists : forall q m bytes,
  owned q m -> operation q = reading ->
  0 < Z.of_nat (length bytes) <= requested q ->
  exists m', io_return q m (transfer bytes None) m'.
Proof.
  intros q m bytes OWN READ SIZE.
  pose proof OWN as OWN0.
  destruct OWN as [BOUNDS [OFFSET [WRAP [EO [EW [ERR [SEP BUF]]]]]]].
  rewrite READ in BUF.
  assert (WRITE : Mem.range_perm m (buffer_block q) (buffer_offset q)
    (buffer_offset q + Z.of_nat (length (map Byte bytes))) Cur Writable).
  { rewrite map_length. intros i HI. apply BUF; lia. }
  destruct (Mem.range_perm_storebytes _ _ _ _ WRITE) as [m' COPY].
  exists m'. eapply read_returns; eauto.
  constructor.
Qed.

Theorem error_return_exists : forall q m error,
  owned q m -> exists m', io_return q m (failure error) m'.
Proof.
  intros q m error OWN.
  pose proof OWN as OWN0.
  destruct OWN as [BOUNDS [OFFSET [WRAP [EO [EW [ERR REST]]]]]].
  destruct (Mem.valid_access_store _ _ _ _ (Vint error) ERR) as [m' STORE].
  exists m'. apply error_returns; [exact OWN0|]. constructor; assumption.
Qed.

Theorem zero_return_exists : forall q m,
  owned q m -> io_return q m (zero None) m.
Proof. intros; constructor; [assumption|constructor]. Qed.

Theorem arbitrary_read_and_error_witness : forall bytes error,
  Z.of_nat (length bytes) = 2 ->
  exists q m read_memory error_memory,
    owned q m /\ requested q = 4 /\
    io_return q m (transfer bytes None) read_memory /\
    io_return q m (failure error) error_memory /\
    Mem.loadbytes read_memory (buffer_block q) (buffer_offset q) 2 = Some (map Byte bytes) /\
    Mem.load Mint32 error_memory (errno_block q) (errno_offset q) = Some (Vint error).
Proof.
  intros bytes error LENGTH.
  destruct owned_read_inhabited as [q [m [OWN [READ COUNT]]]].
  destruct (read_transfer_exists q m bytes OWN READ) as [mr R]; [lia|].
  destruct (error_return_exists q m error OWN) as [me E].
  exists q, m, mr, me. split; [exact OWN|]. split; [exact COUNT|].
  split; [exact R|]. split; [exact E|]. split.
  - rewrite <- LENGTH. eapply read_exact_bytes; eauto.
  - eapply failure_errno; eauto.
Qed.

Definition for_write (q : request) : request :=
  {| operation := writing; descriptor := descriptor q;
     buffer_block := buffer_block q; buffer_offset := buffer_offset q;
     requested := requested q; errno_block := errno_block q; errno_offset := errno_offset q |}.

Theorem full_read_then_write : forall q m bytes after,
  operation q = reading -> Z.of_nat (length bytes) = requested q ->
  io_return q m (transfer bytes None) after ->
  io_return (for_write q) after (transfer bytes None) after.
Proof.
  intros q m bytes after READ LENGTH H. inversion H; subst; try congruence.
  match goal with H : errno_change _ _ None _ |- _ => inversion H; subst end.
  match goal with H : owned q m |- _ =>
    destruct H as [SIZE [OFFSET [WRAP [EO [EW [ERR [SEP BUF]]]]]]] end.
  assert (OWN : owned (for_write q) after).
  { unfold owned, for_write; simpl.
    split; [exact SIZE|]. split; [exact OFFSET|]. split; [exact WRAP|].
    split; [exact EO|]. split; [exact EW|]. split.
    - eapply Mem.storebytes_valid_access_1; eauto.
    - split; [exact SEP|]. exists bytes; split; [exact LENGTH|].
      rewrite <- LENGTH, <- (map_length Byte bytes).
      eapply Mem.loadbytes_storebytes_same; eauto. }
  apply write_returns.
  - exact OWN.
  - reflexivity.
  - simpl; lia.
  - simpl. rewrite <- (map_length Byte bytes). eapply Mem.loadbytes_storebytes_same; eauto.
  - constructor.
Qed.

Theorem arbitrary_write_witness : forall bytes,
  Z.of_nat (length bytes) = 4 ->
  exists q m, requested q = 4 /\ operation q = writing /\
    io_return q m (transfer bytes None) m.
Proof.
  intros bytes LENGTH.
  destruct owned_read_inhabited as [q [m [OWN [READ COUNT]]]].
  destruct (read_transfer_exists q m bytes OWN READ) as [after R]; [lia|].
  exists (for_write q), after. split; [exact COUNT|]. split; [reflexivity|].
  eapply full_read_then_write; eauto; lia.
Qed.
