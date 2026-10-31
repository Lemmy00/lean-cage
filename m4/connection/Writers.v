(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-effects.writers: Complete source writers from independent ownership. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events
  Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Slice Machine ClightSteps WriteAll Deterministic StoreSteps WriteBytes.
Import ListNotations.
Open Scope Z_scope.

Definition put32_byte x i := Int.zero_ext 8 (Int.shru x (Int.repr (8 * i))).
Definition put64_byte x i := Int.zero_ext 8
  (Int.repr (Int64.unsigned (Int64.shru x (Int64.repr (8 * i))))).
Definition put32_values x := map (put32_byte x) [0; 1; 2; 3].
Definition put64_values x := map (put64_byte x) [0; 1; 2; 3; 4; 5; 6; 7].
Definition writer_initial f b ofs x k m := Callstate (Internal f) [Vptr b ofs; x] k m.

Lemma writer_entry : forall ge f b ofs x k m,
  f = f_put32 \/ f = f_put64 ->
  edge ge (writer_initial f b ofs x k m)
    (State f (fn_body f) k empty_env
      (PTree.set _x x (PTree.set _p (Vptr b ofs) (create_undef_temps (fn_temps f)))) m).
Proof.
  intros ge f b ofs x k m WRITER. destruct WRITER; subst f;
    split; [exact I| |exact I|]; split.
  1,3: apply step_internal_function; constructor;
    [constructor|repeat constructor; simpl; intuition discriminate|
     unfold list_disjoint, var_names; simpl; intros a c [A|[A|A]] [C|C];
       try contradiction; subst; discriminate|constructor|reflexivity].
  all: split; [reflexivity|]; intros t other STEP; inversion STEP; subst;
    match goal with H : function_entry2 _ _ _ _ _ _ _ |- _ => inversion H; subst end;
    match goal with H : alloc_variables _ _ _ _ _ _ |- _ => inversion H; subst end;
    match goal with H : bind_parameter_temps _ _ _ = _ |- _ => cbn in H; inversion H; subst end;
    auto.
Qed.

Ltac next_store := eapply store_next; [cbn [memory_of]; eassumption| |].
Ltac store_unchanged := next_store; [apply unchanged_store_edge|].
Ltac route_store := store_unchanged; [WriteAll.structural|].
Ltac set_store := store_unchanged; [eapply edge_set; WriteAll.expression|].
Ltac branch_store choice := store_unchanged;
  [eapply edge_if with (b := choice); [WriteAll.expression|reflexivity]|].
Ltac assign_byte := next_store;
  [eapply byte_assignment;
    [WriteAll.expression|WriteAll.expression|
      cbn [typeof tuchar sem_cast classify_cast cast_int_int]; rewrite Int.zero_ext_idem by lia; reflexivity|
      match goal with |- context [Ptrofs.mul ?a ?b] =>
        let idx := eval vm_compute in (Ptrofs.unsigned (Ptrofs.mul a b)) in
        change (Ptrofs.mul a b) with (Ptrofs.repr idx);
        eapply pointer_byte_store with (index := idx); [lia|lia|] end;
      match goal with H : Mem.store Mint8unsigned ?m ?b ?pos _ = Some _ |-
          Mem.store Mint8unsigned ?m ?b ?want _ = Some _ =>
        replace want with pos by lia; exact H end]|].
Ltac writer_iteration := route_store; route_store; branch_store true;
  route_store; assign_byte; route_store; set_store; route_store.
Ltac writer_end := route_store; route_store; branch_store false;
  route_store; route_store; next_store; [apply void_return_edge; assumption|];
  apply store_done; cbn; eassumption.

Theorem put32_source_path : forall ge m b ofs x k final,
  is_call_cont k -> Ptrofs.unsigned ofs + 4 <= Ptrofs.modulus ->
  byte_writes m b (Ptrofs.unsigned ofs) (put32_values x) final ->
  store_path ge (writer_prefix m b (Ptrofs.unsigned ofs) (put32_values x))
    (writer_initial f_put32 b ofs (Vint x) k m) 42 (Returnstate Vundef k final).
Proof.
  intros ge m b ofs x k final K BOUND WRITES.
  assert (P0 : writer_prefix m b (Ptrofs.unsigned ofs) (put32_values x) m)
    by apply writer_prefix_initial.
  unfold put32_values in WRITES; simpl map in WRITES.
  inversion WRITES as [|? ? ? ? ? m1 ? S1 T1]; subst. clear WRITES.
  inversion T1 as [|? ? ? ? ? m2 ? S2 T2]; subst. clear T1.
  inversion T2 as [|? ? ? ? ? m3 ? S3 T3]; subst. clear T2.
  inversion T3 as [|? ? ? ? ? m4 ? S4 T4]; subst. clear T3.
  inversion T4; subst. clear T4.
  assert (P1 : writer_prefix m b (Ptrofs.unsigned ofs) (put32_values x) m1).
  { exists [put32_byte x 0], [put32_byte x 1; put32_byte x 2; put32_byte x 3]. split; [reflexivity|].
    econstructor; [eassumption|]. constructor. }
  assert (P2 : writer_prefix m b (Ptrofs.unsigned ofs) (put32_values x) m2).
  { exists [put32_byte x 0; put32_byte x 1], [put32_byte x 2; put32_byte x 3]. split; [reflexivity|].
    econstructor; [eassumption|]. econstructor; [eassumption|]. constructor. }
  assert (P3 : writer_prefix m b (Ptrofs.unsigned ofs) (put32_values x) m3).
  { exists [put32_byte x 0; put32_byte x 1; put32_byte x 2], [put32_byte x 3]. split; [reflexivity|].
    econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. constructor. }
  assert (P4 : writer_prefix m b (Ptrofs.unsigned ofs) (put32_values x) final).
  { exists [put32_byte x 0; put32_byte x 1; put32_byte x 2; put32_byte x 3], []. split; [reflexivity|].
    econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. constructor. }
  store_unchanged; [apply writer_entry; auto|].
  unfold f_put32; simpl fn_body. route_store; set_store; route_store.
  do 4 writer_iteration. writer_end.
Qed.

Theorem put64_source_path : forall ge m b ofs x k final,
  is_call_cont k -> Ptrofs.unsigned ofs + 8 <= Ptrofs.modulus ->
  byte_writes m b (Ptrofs.unsigned ofs) (put64_values x) final ->
  store_path ge (writer_prefix m b (Ptrofs.unsigned ofs) (put64_values x))
    (writer_initial f_put64 b ofs (Vlong x) k m) 74 (Returnstate Vundef k final).
Proof.
  intros ge m b ofs x k final K BOUND WRITES.
  assert (P0 : writer_prefix m b (Ptrofs.unsigned ofs) (put64_values x) m)
    by apply writer_prefix_initial.
  unfold put64_values in WRITES; simpl map in WRITES.
  inversion WRITES as [|? ? ? ? ? m1 ? S1 T1]; subst. clear WRITES.
  inversion T1 as [|? ? ? ? ? m2 ? S2 T2]; subst. clear T1.
  inversion T2 as [|? ? ? ? ? m3 ? S3 T3]; subst. clear T2.
  inversion T3 as [|? ? ? ? ? m4 ? S4 T4]; subst. clear T3.
  inversion T4 as [|? ? ? ? ? m5 ? S5 T5]; subst. clear T4.
  inversion T5 as [|? ? ? ? ? m6 ? S6 T6]; subst. clear T5.
  inversion T6 as [|? ? ? ? ? m7 ? S7 T7]; subst. clear T6.
  inversion T7 as [|? ? ? ? ? m8 ? S8 T8]; subst. clear T7.
  inversion T8; subst. clear T8.
  assert (P1 : writer_prefix m b (Ptrofs.unsigned ofs) (put64_values x) m1).
  { exists [put64_byte x 0], [put64_byte x 1; put64_byte x 2; put64_byte x 3; put64_byte x 4; put64_byte x 5; put64_byte x 6; put64_byte x 7]. split; [reflexivity|].
    econstructor; [eassumption|]. constructor. }
  assert (P2 : writer_prefix m b (Ptrofs.unsigned ofs) (put64_values x) m2).
  { exists [put64_byte x 0; put64_byte x 1], [put64_byte x 2; put64_byte x 3; put64_byte x 4; put64_byte x 5; put64_byte x 6; put64_byte x 7]. split; [reflexivity|].
    econstructor; [eassumption|]. econstructor; [eassumption|]. constructor. }
  assert (P3 : writer_prefix m b (Ptrofs.unsigned ofs) (put64_values x) m3).
  { exists [put64_byte x 0; put64_byte x 1; put64_byte x 2], [put64_byte x 3; put64_byte x 4; put64_byte x 5; put64_byte x 6; put64_byte x 7]. split; [reflexivity|].
    econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. constructor. }
  assert (P4 : writer_prefix m b (Ptrofs.unsigned ofs) (put64_values x) m4).
  { exists [put64_byte x 0; put64_byte x 1; put64_byte x 2; put64_byte x 3], [put64_byte x 4; put64_byte x 5; put64_byte x 6; put64_byte x 7]. split; [reflexivity|].
    econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. constructor. }
  assert (P5 : writer_prefix m b (Ptrofs.unsigned ofs) (put64_values x) m5).
  { exists [put64_byte x 0; put64_byte x 1; put64_byte x 2; put64_byte x 3; put64_byte x 4], [put64_byte x 5; put64_byte x 6; put64_byte x 7]. split; [reflexivity|].
    econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. constructor. }
  assert (P6 : writer_prefix m b (Ptrofs.unsigned ofs) (put64_values x) m6).
  { exists [put64_byte x 0; put64_byte x 1; put64_byte x 2; put64_byte x 3; put64_byte x 4; put64_byte x 5], [put64_byte x 6; put64_byte x 7]. split; [reflexivity|].
    econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. constructor. }
  assert (P7 : writer_prefix m b (Ptrofs.unsigned ofs) (put64_values x) m7).
  { exists [put64_byte x 0; put64_byte x 1; put64_byte x 2; put64_byte x 3; put64_byte x 4; put64_byte x 5; put64_byte x 6], [put64_byte x 7]. split; [reflexivity|].
    econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. constructor. }
  assert (P8 : writer_prefix m b (Ptrofs.unsigned ofs) (put64_values x) final).
  { exists [put64_byte x 0; put64_byte x 1; put64_byte x 2; put64_byte x 3; put64_byte x 4; put64_byte x 5; put64_byte x 6; put64_byte x 7], []. split; [reflexivity|].
    econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. econstructor; [eassumption|]. constructor. }
  store_unchanged; [apply writer_entry; auto|].
  unfold f_put64; simpl fn_body. route_store; set_store; route_store.
  do 8 writer_iteration. writer_end.
Qed.

(* These constructors require only permission and pointer bounds. They do not
   assume any memory initialization, output bytes, execution, or return. *)
Inductive writer_input m b ofs : function -> val -> list int -> nat -> Prop :=
| writer32_input : forall x,
    Ptrofs.unsigned ofs + 4 <= Ptrofs.modulus ->
    Mem.range_perm m b (Ptrofs.unsigned ofs) (Ptrofs.unsigned ofs + 4) Cur Writable ->
    writer_input m b ofs f_put32 (Vint x) (put32_values x) 42
| writer64_input : forall x,
    Ptrofs.unsigned ofs + 8 <= Ptrofs.modulus ->
    Mem.range_perm m b (Ptrofs.unsigned ofs) (Ptrofs.unsigned ofs + 8) Cur Writable ->
    writer_input m b ofs f_put64 (Vlong x) (put64_values x) 74.

Theorem writer_execution : forall ge m b ofs f value values count k,
  writer_input m b ofs f value values count -> is_call_cont k ->
  exists final, byte_writes m b (Ptrofs.unsigned ofs) values final /\
    store_path ge (writer_prefix m b (Ptrofs.unsigned ofs) values)
      (writer_initial f b ofs value k m) count (Returnstate Vundef k final).
Proof.
  intros ge m b ofs f value values count k INPUT K. destruct INPUT.
  - destruct (byte_writes_exists (put32_values x) _ _ _ H0) as [final WRITES].
    exists final; split; [exact WRITES|apply put32_source_path; assumption].
  - destruct (byte_writes_exists (put64_values x) _ _ _ H0) as [final WRITES].
    exists final; split; [exact WRITES|apply put64_source_path; assumption].
Qed.

Theorem writer_success_exists : forall cell m b ofs f value values count k,
  writer_input m b ofs f value values count -> is_call_cont k ->
  exists final, byte_writes m b (Ptrofs.unsigned ofs) values final /\
    steps (Clight.globalenv Slice.prog) cell (live (writer_initial f b ofs value k m))
      (repeat (source_step E0) count) (live (Returnstate Vundef k final)).
Proof.
  intros. destruct (writer_execution (Clight.globalenv Slice.prog) _ _ _ _ _ _ _ _ H H0)
    as [final [WRITES PATH]]. exists final; split; [assumption|].
  eapply store_path_actual; exact PATH.
Qed.

Theorem writer_all_prefixes : forall cell m b ofs f value values count events target,
  writer_input m b ofs f value values count ->
  steps (Clight.globalenv Slice.prog) cell (live (writer_initial f b ofs value Kstop m)) events target ->
  writer_prefix m b (Ptrofs.unsigned ofs) values (routine_memory target) /\
  (length events <= S count)%nat.
Proof.
  intros. destruct (writer_execution (Clight.globalenv Slice.prog) _ _ _ _ _ _ _ Kstop H I)
    as [final [WRITES PATH]]. eapply store_path_prefix_invariant; eassumption.
Qed.

Theorem writer_return_exact : forall cell m b ofs f value values count events actual after,
  writer_input m b ofs f value values count ->
  steps (Clight.globalenv Slice.prog) cell (live (writer_initial f b ofs value Kstop m)) events
    (live (Returnstate actual Kstop after)) ->
  actual = Vundef /\ events = repeat (source_step E0) count /\
  byte_writes m b (Ptrofs.unsigned ofs) values after /\
  Mem.loadbytes after b (Ptrofs.unsigned ofs) (Z.of_nat (length values)) =
    Some (map byte_encoding values).
Proof.
  intros. destruct (writer_execution (Clight.globalenv Slice.prog) _ _ _ _ _ _ _ Kstop H I)
    as [final [WRITES PATH]].
  destruct (store_path_return_exact _ _ _ _ _ _ _ _ _ _ PATH H0) as [ACTUAL [AFTER EVENTS]].
  subst. split; [reflexivity|]. split; [reflexivity|]. split; [exact WRITES|].
  eapply byte_writes_content; [exact WRITES|]. destruct H; discriminate.
Qed.

Theorem writer_defined_prefix : forall cell m b ofs f value values count events s,
  writer_input m b ofs f value values count ->
  steps (Clight.globalenv Slice.prog) cell (live (writer_initial f b ofs value Kstop m)) events (live s) ->
  (exists final, s = Returnstate Vundef Kstop final /\
    byte_writes m b (Ptrofs.unsigned ofs) values final) \/
  exists next, step (Clight.globalenv Slice.prog) cell (live s) (source_step E0) (live next).
Proof.
  intros. destruct (writer_execution (Clight.globalenv Slice.prog) _ _ _ _ _ _ _ Kstop H I)
    as [final [WRITES PATH]].
  destruct (store_path_defined_prefix _ _ _ _ _ _ _ _ _ PATH H0); auto.
  left; exists final; auto.
Qed.

Theorem writer_loss_every_prefix : forall cell m b ofs f value values count n,
  writer_input m b ofs f value values count -> (n <= count)%nat ->
  exists mid,
    steps (Clight.globalenv Slice.prog) cell (live (writer_initial f b ofs value Kstop m))
      (repeat (source_step E0) n) (live mid) /\
    steps (Clight.globalenv Slice.prog) cell (live (writer_initial f b ofs value Kstop m))
      (repeat (source_step E0) n ++ [loss_step]) (dead (memory_of mid)) /\
    writer_prefix m b (Ptrofs.unsigned ofs) values (memory_of mid).
Proof.
  intros. destruct (writer_execution (Clight.globalenv Slice.prog) _ _ _ _ _ _ _ Kstop H I)
    as [final [WRITES PATH]]. eapply store_path_loss_every_prefix; eassumption.
Qed.

Theorem arbitrary_put32_input : forall base x,
  exists m b, Mem.alloc base 0 4 = (m, b) /\
    writer_input m b Ptrofs.zero f_put32 (Vint x) (put32_values x) 42.
Proof.
  intros base x. destruct (allocated_writer_input base 4) as [b [m [ALLOC OWN]]].
  exists m, b. split; [exact ALLOC|]. constructor; [vm_compute; congruence|exact OWN].
Qed.

Theorem arbitrary_put64_input : forall base x,
  exists m b, Mem.alloc base 0 8 = (m, b) /\
    writer_input m b Ptrofs.zero f_put64 (Vlong x) (put64_values x) 74.
Proof.
  intros base x. destruct (allocated_writer_input base 8) as [b [m [ALLOC OWN]]].
  exists m, b. split; [exact ALLOC|]. constructor; [vm_compute; congruence|exact OWN].
Qed.

(* A concrete interruption witness exposes the first store itself. It cannot be
   mistaken for an atomic whole-word operation, including at unaligned offsets. *)
Theorem put32_first_byte_loss : forall cell m b ofs x,
  writer_input m b ofs f_put32 (Vint x) (put32_values x) 42 ->
  exists after,
    Mem.store Mint8unsigned m b (Ptrofs.unsigned ofs) (Vint (put32_byte x 0)) = Some after /\
    steps (Clight.globalenv Slice.prog) cell
      (live (writer_initial f_put32 b ofs (Vint x) Kstop m))
      (repeat (source_step E0) 9 ++ [loss_step]) (dead after) /\
    Mem.unchanged_on (outside_bytes b (Ptrofs.unsigned ofs) 1) m after /\
    Mem.loadbytes after b (Ptrofs.unsigned ofs) 1 = Some [byte_encoding (put32_byte x 0)].
Proof.
  intros cell m b ofs x INPUT. inversion INPUT; subst.
  destruct (byte_writes_exists (put32_values x) _ _ _ H1) as [final WRITES].
  inversion WRITES as [|? ? ? ? ? after ? STORE TAIL]; subst.
  assert (PATH : exists s, memory_of s = after /\
    store_path (Clight.globalenv Slice.prog) (fun _ => True)
      (writer_initial f_put32 b ofs (Vint x) Kstop m) 9 s).
  { assert (OK : True) by exact I. eexists. split; [|].
    2: { store_unchanged; [apply writer_entry; auto|].
      unfold f_put32; simpl fn_body. route_store; set_store; route_store.
      route_store; route_store; branch_store true; route_store; assign_byte.
      apply store_done; exact I. }
    reflexivity. }
  destruct PATH as [s [MEM PATH]].
  exists after. split; [exact STORE|]. split.
  - rewrite <- MEM. eapply store_path_terminal_loss; exact PATH.
  - assert (ONE : byte_writes m b (Ptrofs.unsigned ofs) [put32_byte x 0] after)
      by (econstructor; [exact STORE|constructor]).
    split; [exact (byte_writes_outside _ _ _ _ _ ONE)|].
    exact (byte_writes_content _ _ _ _ _ ONE ltac:(discriminate)).
Qed.

Theorem arbitrary_unaligned_writer_inputs : forall base x y,
  exists m b, Mem.alloc base 0 9 = (m, b) /\
    writer_input m b (Ptrofs.repr 1) f_put32 (Vint x) (put32_values x) 42 /\
    writer_input m b (Ptrofs.repr 1) f_put64 (Vlong y) (put64_values y) 74.
Proof.
  intros base x y. destruct (allocated_writer_input base 9) as [b [m [ALLOC OWN]]].
  exists m, b. split; [exact ALLOC|]. split; constructor;
    try solve [vm_compute; congruence];
    red; intros pos RANGE; apply OWN;
    change (1 <= pos < 5) in RANGE || change (1 <= pos < 9) in RANGE;
    change (0 <= pos < 9); lia.
Qed.
