(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-decoder.source: Exact reserved-byte loop statements and bounded machine arithmetic. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Slice Machine ClightSteps WriteAll StoreSteps LocalAccess CallAccess Library
  ResultLayout ResultSource FrameBytes DecoderSource DecoderControl SourceReach.
Import ListNotations.
Open Scope Z_scope.

Definition zero_scan_body index loaded high :=
  Ssequence (Sifthenelse (Ebinop Olt (Etempvar index tint)
    (Econst_int (Int.repr (Z.of_nat high)) tint) tint) Sskip Sbreak)
    (Ssequence (Sset loaded (Ederef (Ebinop Oadd (Etempvar _p (tptr tuchar))
      (Etempvar index tint) (tptr tuchar)) tuchar))
      (Sifthenelse (Etempvar loaded tuchar)
        (Sreturn (Some (Eunop Oneg (Econst_int Int.one tint) tint))) Sskip)).
Definition zero_scan_increment index :=
  Sset index (Ebinop Oadd (Etempvar index tint) (Econst_int Int.one tint) tint).
Definition zero_scan_loop index loaded high :=
  Sloop (zero_scan_body index loaded high) (zero_scan_increment index).
Definition zero_scan index loaded low high :=
  Ssequence (Sset index (Econst_int (Int.repr (Z.of_nat low)) tint))
    (zero_scan_loop index loaded high).

Theorem decoder_header_reserved_source : decoder_tail_reserved = zero_scan _i _t'95 156 160.
Proof. reflexivity. Qed.
Definition decoder_payload_reserved := match decoder_postchecks with
  Ssequence _ (Ssequence reserved _) => reserved | _ => Sskip end.
Theorem decoder_payload_reserved_source : decoder_payload_reserved = zero_scan _i__1 _t'83 96 156.
Proof. reflexivity. Qed.

Lemma small_counter_signed : forall n, (n <= 160)%nat ->
  Int.signed (Int.repr (Z.of_nat n)) = Z.of_nat n.
Proof. intros; apply Int.signed_repr; change (-2147483648 <= Z.of_nat n <= 2147483647); lia. Qed.
Lemma small_counter_lt : forall a b, (a < b <= 160)%nat ->
  Int.lt (Int.repr (Z.of_nat a)) (Int.repr (Z.of_nat b)) = true.
Proof.
  intros a b BOUND; unfold Int.lt. rewrite !small_counter_signed by lia.
  destruct (zlt (Z.of_nat a) (Z.of_nat b)); [reflexivity|lia].
Qed.
Lemma counter_at_end : forall a, Int.lt (Int.repr (Z.of_nat a)) (Int.repr (Z.of_nat a)) = false.
Proof. intros; unfold Int.lt. destruct (zlt _ _); [lia|reflexivity]. Qed.
Lemma small_counter_pointer : forall n, (n <= 160)%nat ->
  Ptrofs.mul (Ptrofs.repr 1) (ptrofs_of_int Signed (Int.repr (Z.of_nat n))) =
    Ptrofs.repr (Z.of_nat n).
Proof.
  intros n BOUND. unfold ptrofs_of_int, Ptrofs.of_ints.
  rewrite small_counter_signed by exact BOUND. rewrite Ptrofs.mul_commut. apply Ptrofs.mul_one.
Qed.
Lemma counter_increment : forall n,
  Int.add (Int.repr (Z.of_nat n)) Int.one = Int.repr (Z.of_nat (S n)).
Proof.
  intros. unfold Int.add, Int.one. apply Int.eqm_samerepr.
  replace (Z.of_nat (S n)) with (Z.of_nat n+1) by lia.
  apply Int.eqm_add; apply Int.eqm_sym; apply Int.eqm_unsigned_repr.
Qed.

Definition zero_range bytes low high := forall i,
  (low <= i < high)%nat -> byte_word_at bytes i = Int.zero.
Lemma zero_range_empty : forall bytes n, zero_range bytes n n.
Proof. intros bytes n i BOUND; lia. Qed.
Lemma zero_range_cons : forall bytes low high,
  byte_word_at bytes low = Int.zero -> zero_range bytes (S low) high -> zero_range bytes low high.
Proof. intros bytes low high FIRST TAIL i BOUND. destruct (Nat.eq_dec i low); [subst;exact FIRST|apply TAIL;lia]. Qed.

Definition zero_boundary local k p output ofs bytes low high m freed target :=
  (exists i, (low <= i < high)%nat /\ byte_word_at bytes i <> Int.zero /\
    zero_range bytes low i /\ target = Returnstate (Vint Int.mone) (call_cont k) freed) \/
  (exists le, target = State f_decode_frame Sskip k (decoder_env local) le m /\
    le ! _p = Some (address_value p) /\ le ! _r = Some (Vptr output (Ptrofs.repr ofs)) /\
    zero_range bytes low high).
Lemma zero_boundary_advance : forall local k p output ofs bytes low high m freed target,
  byte_word_at bytes low = Int.zero ->
  zero_boundary local k p output ofs bytes (S low) high m freed target ->
  zero_boundary local k p output ofs bytes low high m freed target.
Proof.
  intros local k p output ofs bytes low high m freed target FIRST [BAD|GOOD].
  - destruct BAD as [i [RANGE [NE [PREFIX TARGET]]]]. left; exists i;
      split; [lia|]. split; [exact NE|]. split;
      [eapply zero_range_cons; eassumption|exact TARGET].
  - destruct GOOD as [le [TARGET [PTR [OUT ZERO]]]]. right; exists le.
    split; [exact TARGET|]. split; [exact PTR|]. split; [exact OUT|].
    eapply zero_range_cons; eassumption.
Qed.
Lemma zero_reaches_consequence : forall ge P Q R start,
  source_reaches ge P Q start -> (forall s, Q s -> R s) -> source_reaches ge P R start.
Proof. intros ge P Q R start [n [last [PATH POST]]] IMPLIES.
  exists n,last; split; [exact PATH|apply IMPLIES;exact POST]. Qed.

Lemma zero_loop_source_reaches : forall m freed local p bytes output ofs k index loaded high,
  readable_bytes m p bytes -> length bytes = 160%nat -> (high <= 160)%nat ->
  index <> _p -> index <> _r -> loaded <> _p -> loaded <> _r -> loaded <> index ->
  Mem.free m local 0 144 = Some freed ->
  forall remaining current le,
  (current+remaining=high)%nat ->
  le ! index = Some (Vint (Int.repr (Z.of_nat current))) ->
  le ! _p = Some (address_value p) -> le ! _r = Some (Vptr output (Ptrofs.repr ofs)) ->
  source_reaches result_ge (fun after => after = m \/ after = freed)
    (zero_boundary local k p output ofs bytes current high m freed)
    (State f_decode_frame (zero_scan_loop index loaded high) k (decoder_env local) le m).
Proof.
  intros m freed local p bytes output ofs k index loaded high READ LEN HIGH IP IR LP LR LI FREE remaining.
  induction remaining as [|remaining IH]; intros current le COUNT INDEX PTR OUT.
  - assert (current=high) by lia; subst current.
    unfold zero_scan_loop, zero_scan_body, zero_scan_increment.
    decoder_reach_route. decoder_reach_route.
    eapply source_reaches_prepend; [left;reflexivity|apply unchanged_store_edge|].
    + eapply edge_if with (b:=false).
      * decoder_control_expression.
      * change (bool_val (Val.of_bool (Int.lt (Int.repr (Z.of_nat high))
          (Int.repr (Z.of_nat high)))) tint m = Some false).
        rewrite (counter_at_end high). reflexivity.
    + repeat decoder_reach_route.
      apply source_reaches_done; [left;reflexivity|].
      right; exists le. split; [reflexivity|]. split; [exact PTR|].
      split; [exact OUT|apply zero_range_empty].
  - unfold zero_scan_loop, zero_scan_body, zero_scan_increment.
    decoder_reach_route. decoder_reach_route.
    eapply source_reaches_prepend; [left;reflexivity|apply unchanged_store_edge|].
    + eapply edge_if with (b:=true).
      * decoder_control_expression.
      * change (bool_val (Val.of_bool (Int.lt (Int.repr (Z.of_nat current))
          (Int.repr (Z.of_nat high)))) tint m = Some true).
        rewrite (small_counter_lt current high ltac:(lia)). reflexivity.
    + repeat decoder_reach_route.
      Ltac zero_lookup := cbn [set_opttemp];
        repeat first [rewrite PTree.gss | rewrite PTree.gso by congruence];
        first [reflexivity|eassumption].
      Ltac zero_expression := first
        [apply value_int | eapply value_temp; zero_lookup
        |eapply value_binary; [zero_expression|zero_expression|reflexivity]
        |eapply value_unary; [zero_expression|reflexivity]].
      eapply source_reaches_prepend; [left;reflexivity|apply unchanged_store_edge|].
      * eapply edge_set with (v:=Vint (byte_word_at bytes current)).
        eapply value_load; [zero_expression|reflexivity|].
        change (Mem.loadv Mint8unsigned m (Vptr (address_block p)
          (Ptrofs.add (Ptrofs.repr (address_offset p))
            (Ptrofs.mul (Ptrofs.repr 1) (ptrofs_of_int Signed (Int.repr (Z.of_nat current)))))) =
            Some (Vint (byte_word_at bytes current))).
        rewrite small_counter_pointer by lia. rewrite pointer_add_representations.
        exact (readable_byte_load m p bytes current READ ltac:(rewrite LEN;lia)).
      * decoder_reach_route.
        eapply source_reaches_prepend; [left;reflexivity|apply unchanged_store_edge|].
        -- eapply edge_if with (b:=negb (Int.eq (byte_word_at bytes current) Int.zero));
             [zero_expression|reflexivity].
        -- destruct (Int.eq (byte_word_at bytes current) Int.zero) eqn:BYTE; cbn [negb].
           ++ repeat decoder_reach_route.
              eapply source_reaches_prepend; [left;reflexivity|apply unchanged_store_edge|].
              ** eapply edge_set; zero_expression.
              ** decoder_reach_route.
                 cbn [cast_int_int]. rewrite counter_increment.
                 eapply zero_reaches_consequence.
                 --- eapply (IH (S current)); [lia|zero_lookup|zero_lookup|zero_lookup].
                 --- intros target BOUNDARY. eapply zero_boundary_advance.
                     +++ apply Int.same_if_eq; exact BYTE.
                     +++ exact BOUNDARY.
           ++ eapply source_reaches_prepend; [left;reflexivity| |].
              ** eapply decoder_local_return;
                   [apply old_expression_value; zero_expression|reflexivity|exact FREE].
              ** apply source_reaches_done; [right;reflexivity|].
                 left; exists current. split; [lia|]. split.
                 --- intro EQ; rewrite EQ, Int.eq_true in BYTE; discriminate.
                 --- split; [apply zero_range_empty|reflexivity].
Qed.

Theorem zero_scan_source_reaches : forall m freed local p bytes output ofs k index loaded low high le,
  readable_bytes m p bytes -> length bytes = 160%nat -> (low <= high <= 160)%nat ->
  index <> _p -> index <> _r -> loaded <> _p -> loaded <> _r -> loaded <> index ->
  Mem.free m local 0 144 = Some freed ->
  le ! _p = Some (address_value p) -> le ! _r = Some (Vptr output (Ptrofs.repr ofs)) ->
  source_reaches result_ge (fun after => after = m \/ after = freed)
    (zero_boundary local k p output ofs bytes low high m freed)
    (State f_decode_frame (zero_scan index loaded low high) k (decoder_env local) le m).
Proof.
  intros m freed local p bytes output ofs k index loaded low high le READ LEN BOUNDS IP IR LP LR LI FREE PTR OUT.
  unfold zero_scan. decoder_reach_route. decoder_reach_set. decoder_reach_route.
  eapply (zero_loop_source_reaches m freed local p bytes output ofs k index loaded high
    READ LEN ltac:(lia) IP IR LP LR LI FREE (high-low)%nat low).
  - lia.
  - apply PTree.gss.
  - rewrite PTree.gso by congruence; exact PTR.
  - rewrite PTree.gso by congruence; exact OUT.
Qed.
