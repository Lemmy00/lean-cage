(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual fraction syntax selects a nonempty bounded digit scan or fails closed. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayJsonNumberSource GatewayJsonNumberSourceBytes
  GatewayJsonNumberSourceTests GatewayJsonNumberSourceScans GatewayJsonNumberSourceFold GatewayJsonNumberLexical
  GatewayIntegerPrefix GatewaySourceSegments GatewaySourceSegmentAutomation GatewayFramedRuntime GatewayFailurePaths GatewaySourceCuts.
Import ListNotations.
Open Scope Z_scope.

Definition json_fraction_select := json_number_rest json_number_fraction.
Definition json_fraction_test_cont continuation := Kseq json_fraction_select continuation.
Definition json_fraction_loop_cont continuation := Kseq json_number_fraction_guard continuation.
Definition json_fraction_written := [_t'8; _t'32; _t'5; _index; _fraction; _t'6; _t'7; _t'31; _t'30].

Lemma json_number_segment_denial {World Event} (backend : gateway_backend World Event) ge
    property source target :
  gateway_source_segment backend ge property source target property ->
  gateway_failure_result backend ge target -> gateway_failure_when backend ge property source.
Proof.
  intros SEGMENT FAILURE before world events value after next GOOD RUN.
  destruct (gateway_source_segment_cut backend ge _ _ _ _ SEGMENT before world events value after next GOOD RUN)
    as (prefix & suffix & middle & current & EVENTS & QUIET & PREFIX & READY & SUFFIX).
  exact (FAILURE middle current suffix value after next SUFFIX).
Qed.

Theorem gateway_json_fraction_to_test {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) parameters continuation memory :
  gateway_ambient_closed backend property ->
  gateway_source_segment backend ge property
    (State f_host_json_number json_number_fraction continuation empty_env parameters memory)
    (State f_host_json_number (json_marker_source json_fraction_marker)
      (json_fraction_test_cont continuation) empty_env parameters memory) property.
Proof.
  intro CLOSED; unfold json_fraction_test_cont, json_fraction_select, json_marker_source.
  eapply gateway_segment_same with (next := State f_host_json_number (json_number_first json_number_fraction)
    (Kseq (json_number_rest json_number_fraction) continuation) empty_env parameters memory);
    [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_seq |apply gateway_segment_here].
Qed.

Theorem gateway_json_fraction_skipped {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) parameters continuation memory :
  gateway_ambient_closed backend property -> parameters ! _t'8 = Some (Vint Int.zero) ->
  gateway_source_segment backend ge property
    (State f_host_json_number Sskip (json_fraction_test_cont continuation) empty_env parameters memory)
    (State f_host_json_number Sskip continuation empty_env parameters memory) property.
Proof.
  intros CLOSED FLAG; unfold json_fraction_test_cont.
  gateway_segment_dynamic CLOSED ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
Qed.

Lemma json_number_word_increment index : Int64.add (Int64.repr index) (Int64.repr 1) = Int64.repr (index + 1).
Proof.
  unfold Int64.add; apply Int64.eqm_samerepr.
  apply Int64.eqm_add; apply Int64.eqm_unsigned_repr_l; apply Int64.eqm_refl.
Qed.

Theorem gateway_json_fraction_entered {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) parameters continuation index memory :
  gateway_ambient_closed backend property -> parameters ! _t'8 = Some (Vint Int.one) ->
  parameters ! _index = Some (Vlong (Int64.repr index)) ->
  exists changed,
    gateway_source_segment backend ge property
      (State f_host_json_number Sskip (json_fraction_test_cont continuation) empty_env parameters memory)
      (State f_host_json_number json_number_fraction_loop (json_fraction_loop_cont continuation) empty_env changed memory) property /\
    changed ! _index = Some (Vlong (Int64.repr (index + 1))) /\
    changed ! _fraction = Some (Vlong (Int64.repr (index + 1))) /\
    (forall identifier, ~ In identifier [_t'5; _index; _fraction] -> changed ! identifier = parameters ! identifier).
Proof.
  intros CLOSED FLAG POSITION; unfold json_fraction_test_cont, json_fraction_loop_cont; eexists; split.
  - gateway_segment_dynamic CLOSED ltac:(fun _ => fail)
      ltac:(fun _ => cbn -[Int64.add Int64.repr]; rewrite ?json_number_word_increment; reflexivity).
  - split; [repeat rewrite PTree.gso by discriminate; apply PTree.gss |].
    split; [apply PTree.gss |]. intros identifier OUTSIDE; repeat rewrite PTree.gso by
      (intro SAME; apply OUTSIDE; subst identifier; cbn; auto); reflexivity.
Qed.

Theorem gateway_json_fraction_guard {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) parameters continuation start finish memory :
  gateway_ambient_closed backend property -> 0 <= start <= 65536 -> 0 <= finish <= 65536 ->
  parameters ! _index = Some (Vlong (Int64.repr finish)) ->
  parameters ! _fraction = Some (Vlong (Int64.repr start)) ->
  gateway_source_segment backend ge property
    (State f_host_json_number Sskip (json_fraction_loop_cont continuation) empty_env parameters memory)
    (State f_host_json_number (if Z.eqb finish start then Sgoto _invalid else Sskip)
      continuation empty_env parameters memory) property.
Proof.
  intros CLOSED START FINISH POSITION FRACTION; unfold json_fraction_loop_cont.
  eapply gateway_segment_same with (next := State f_host_json_number json_number_fraction_guard continuation empty_env parameters memory);
    [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_skip_seq |].
  eapply gateway_segment_same with (next := State f_host_json_number (if Z.eqb finish start then Sgoto _invalid else Sskip)
    continuation empty_env parameters memory).
  - exact CLOSED.
  - cbn; tauto.
  - intros; eapply certified_if_edge with (v := Val.of_bool (Z.eqb finish start)) (b := Z.eqb finish start).
    + eapply binary_expression_value with (v := Vlong (Int64.repr finish)) (w := Vlong (Int64.repr start));
        [apply old_expression_value, value_temp; exact POSITION |apply old_expression_value, value_temp; exact FRACTION |].
      change (Some (Val.of_bool (Int64.eq (Int64.repr finish) (Int64.repr start))) = Some (Val.of_bool (Z.eqb finish start))).
      rewrite json_number_word_equal by lia; reflexivity.
    + destruct (Z.eqb finish start); reflexivity.
  - apply gateway_segment_here.
Qed.

Theorem gateway_json_number_fraction_source {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) parameters continuation object index count remaining memory :
  gateway_ambient_closed backend property -> call_cont continuation = Kstop ->
  0 <= index -> index + Z.of_nat (length remaining) = count -> count <= 65536 ->
  parameters ! _bytes = Some (Vptr object Ptrofs.zero) -> parameters ! _index = Some (Vlong (Int64.repr index)) ->
  parameters ! _size = Some (Vlong (Int64.repr count)) ->
  (forall offset byte, nth_error remaining offset = Some byte -> forall memory world, property memory world ->
    Mem.loadv Mint8signed memory (Vptr object (Ptrofs.repr (index + Z.of_nat offset))) = Some (Vint (Int.repr (Byte.signed byte)))) ->
  match json_number_take_fraction remaining with
  | None => gateway_failure_when backend ge property
      (State f_host_json_number json_number_fraction continuation empty_env parameters memory)
  | Some (fragment, tail) => exists changed,
      gateway_source_segment backend ge property
        (State f_host_json_number json_number_fraction continuation empty_env parameters memory)
        (State f_host_json_number Sskip continuation empty_env changed memory) property /\
      changed ! _bytes = Some (Vptr object Ptrofs.zero) /\
      changed ! _size = Some (Vlong (Int64.repr count)) /\
      changed ! _index = Some (Vlong (Int64.repr (index + Z.of_nat (length fragment)))) /\
      (forall identifier, ~ In identifier json_fraction_written -> changed ! identifier = parameters ! identifier)
  end.
Proof.
  intros CLOSED STOP INDEX LENGTH BOUND BYTES POSITION SIZE LOADS.
  pose proof (gateway_json_fraction_to_test backend ge property parameters continuation memory CLOSED) as PREFIX.
  destruct remaining as [|byte rest].
  - cbn in LENGTH; rewrite Z.add_0_r in LENGTH; subst index; cbn [json_number_take_fraction].
    destruct (gateway_json_number_marker_end backend ge property json_fraction_marker parameters
      (json_fraction_test_cont continuation) count memory CLOSED ltac:(lia) POSITION SIZE)
      as (tested & TEST & FLAG & FRAME).
    exists tested; split.
    + eapply json_number_segment_compose; [exact PREFIX |]. eapply json_number_segment_compose; [exact TEST |].
      apply gateway_json_fraction_skipped; assumption.
    + split; [rewrite FRAME; [exact BYTES |discriminate] |].
      split; [rewrite FRAME; [exact SIZE |discriminate] |]. split.
      * cbn; rewrite Z.add_0_r; rewrite FRAME; [exact POSITION |discriminate].
      * intros identifier OUTSIDE; apply FRAME; intro SAME; apply OUTSIDE; subst identifier; cbn; auto.
  - assert (RANGE : 0 <= index /\ index < count /\ count <= 65536).
    { change (index + Z.of_nat (S (length rest)) = count) in LENGTH; rewrite Nat2Z.inj_succ in LENGTH; lia. }
    assert (TAIL_LENGTH : index + 1 + Z.of_nat (length rest) = count).
    { change (index + Z.of_nat (S (length rest)) = count) in LENGTH; rewrite Nat2Z.inj_succ in LENGTH; lia. }
    destruct (gateway_json_number_marker_test backend ge property json_fraction_marker parameters
      (json_fraction_test_cont continuation) object index count byte memory CLOSED RANGE BYTES POSITION SIZE
      ltac:(intros changed owner GOOD; specialize (LOADS 0%nat byte eq_refl changed owner GOOD); cbn in LOADS;
        rewrite Z.add_0_r in LOADS; exact LOADS)) as (tested & TEST & FLAG & TEST_FRAME).
    assert (TEST_BYTES : tested ! _bytes = Some (Vptr object Ptrofs.zero)) by
      (rewrite TEST_FRAME; [exact BYTES |cbn; intuition discriminate]).
    assert (TEST_SIZE : tested ! _size = Some (Vlong (Int64.repr count))) by
      (rewrite TEST_FRAME; [exact SIZE |cbn; intuition discriminate]).
    assert (TEST_INDEX : tested ! _index = Some (Vlong (Int64.repr index))) by
      (rewrite TEST_FRAME; [exact POSITION |cbn; intuition discriminate]).
    cbn [json_number_take_fraction]; destruct (Byte.eq byte (Byte.repr 46)) eqn:MARKER.
    + cbn [json_marker_flag json_marker_matches] in FLAG; rewrite MARKER in FLAG.
      destruct (gateway_json_fraction_entered backend ge property tested continuation index memory CLOSED FLAG TEST_INDEX)
        as (entered & ENTER & ENTER_INDEX & ENTER_FRACTION & ENTER_FRAME).
      pose proof (gateway_json_number_scan_digits backend ge property json_fraction_scan (json_fraction_loop_cont continuation)
        object count memory CLOSED ltac:(lia) rest entered (index + 1) ltac:(lia)
        ltac:(change (index + Z.of_nat (S (length rest)) = count) in LENGTH; rewrite Nat2Z.inj_succ in LENGTH; lia)
        ltac:(rewrite ENTER_FRAME; [exact TEST_BYTES |cbn; intuition discriminate]) ENTER_INDEX
        ltac:(rewrite ENTER_FRAME; [exact TEST_SIZE |cbn; intuition discriminate])
        ltac:(intros offset selected SELECTED changed owner GOOD; specialize (LOADS (S offset) selected SELECTED changed owner GOOD);
          rewrite Nat2Z.inj_succ in LOADS; replace (index + Z.succ (Z.of_nat offset)) with (index + 1 + Z.of_nat offset) in LOADS by lia;
          exact LOADS)) as SCAN.
      pose proof (json_number_take_digits_sound rest) as LEXICAL.
      destruct (json_number_take_digits rest) as [digits tail] eqn:TAKE; cbn in SCAN, LEXICAL |- *.
      destruct SCAN as (scanned & SCAN & SCAN_BYTES & SCAN_SIZE & SCAN_INDEX & SCAN_FRAME).
      destruct LEXICAL as [REST [DIGITS TAIL]].
      assert (DIGIT_LENGTH : Z.of_nat (length digits) <= Z.of_nat (length rest)).
      { rewrite REST, length_app, Nat2Z.inj_add; lia. }
      assert (FRACTION : scanned ! _fraction = Some (Vlong (Int64.repr (index + 1)))) by
        (rewrite SCAN_FRAME; [exact ENTER_FRACTION |cbn; intuition discriminate]).
      pose proof (gateway_json_fraction_guard backend ge property scanned continuation (index + 1)
        (index + 1 + Z.of_nat (length digits)) memory CLOSED ltac:(lia) ltac:(lia) SCAN_INDEX FRACTION) as GUARD.
      assert (TO_GUARD : gateway_source_segment backend ge property
        (State f_host_json_number json_number_fraction continuation empty_env parameters memory)
        (State f_host_json_number
          (if Z.eqb (index + 1 + Z.of_nat (length digits)) (index + 1) then Sgoto _invalid else Sskip)
          continuation empty_env scanned memory) property).
      { eapply json_number_segment_compose; [exact PREFIX |]. eapply json_number_segment_compose; [exact TEST |].
        eapply json_number_segment_compose; [exact ENTER |]. eapply json_number_segment_compose; [exact SCAN |exact GUARD]. }
      destruct digits as [|first digits].
      * cbn in TO_GUARD; rewrite Z.add_0_r, Z.eqb_refl in TO_GUARD.
        eapply json_number_segment_denial; [exact TO_GUARD |apply gateway_json_number_invalid_denied; exact STOP].
      * assert (NONEMPTY : (index + 1 + Z.of_nat (length (first :: digits)) =? index + 1) = false).
        { apply Z.eqb_neq; change (index + 1 + Z.of_nat (S (length digits)) <> index + 1); rewrite Nat2Z.inj_succ; lia. }
        rewrite NONEMPTY in TO_GUARD; exists scanned; split; [exact TO_GUARD |].
        split; [exact SCAN_BYTES |]. split; [exact SCAN_SIZE |]. split.
        -- change (scanned ! _index = Some (Vlong (Int64.repr (index + Z.of_nat (S (length (first :: digits)))))));
             rewrite Nat2Z.inj_succ; replace (index + Z.succ (Z.of_nat (length (first :: digits)))) with
               (index + 1 + Z.of_nat (length (first :: digits))) by lia; exact SCAN_INDEX.
        -- intros identifier OUTSIDE; rewrite SCAN_FRAME; [rewrite ENTER_FRAME; [apply TEST_FRAME |] |];
             intro MEMBER; apply OUTSIDE; cbn in MEMBER |- *; intuition.
    + cbn [json_marker_flag json_marker_matches] in FLAG; rewrite MARKER in FLAG.
      exists tested; split.
      * eapply json_number_segment_compose; [exact PREFIX |]. eapply json_number_segment_compose; [exact TEST |].
        apply gateway_json_fraction_skipped; assumption.
      * split; [exact TEST_BYTES |]. split; [exact TEST_SIZE |]. split; [cbn; rewrite Z.add_0_r; exact TEST_INDEX |].
        intros identifier OUTSIDE; apply TEST_FRAME; intro MEMBER; apply OUTSIDE; cbn in MEMBER |- *; intuition.
Qed.
