(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual exponent and sign branches retain the exact input cursor. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayJsonNumberSource GatewayJsonNumberSourceBytes
  GatewayJsonNumberSourceTests GatewayJsonNumberSourceScans GatewayJsonNumberSourceFold GatewayJsonNumberLexical
  GatewayJsonNumberSourceFraction GatewayIntegerPrefix GatewaySourceSegments GatewaySourceSegmentAutomation GatewayFramedRuntime
  GatewayFailurePaths GatewaySourceCuts.
Import ListNotations.
Open Scope Z_scope.

Definition json_exponent_select := json_number_rest json_number_exponent.
Definition json_exponent_test_cont continuation := Kseq json_exponent_select continuation.
Definition json_exponent_sign_source := json_number_first json_number_exponent_after_marker.
Definition json_exponent_sign_select := json_number_rest json_exponent_sign_source.
Definition json_exponent_sign_test_cont continuation := Kseq json_exponent_sign_select continuation.
Definition json_exponent_sign_cont continuation := Kseq json_number_exponent_after_sign continuation.
Definition json_exponent_loop_cont continuation := Kseq json_number_exponent_guard continuation.
Definition json_exponent_sign_written := [_t'9; _t'26; _t'27; _index].
Definition json_exponent_written := [_t'12; _t'28; _t'29; _index; _t'9; _t'26; _t'27; _exponent;
  _t'10; _t'11; _t'25; _t'24].

Theorem gateway_json_exponent_to_test {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) parameters continuation memory :
  gateway_ambient_closed backend property ->
  gateway_source_segment backend ge property
    (State f_host_json_number json_number_exponent continuation empty_env parameters memory)
    (State f_host_json_number (json_marker_source json_exponent_marker)
      (json_exponent_test_cont continuation) empty_env parameters memory) property.
Proof.
  intro CLOSED; unfold json_exponent_test_cont, json_exponent_select, json_marker_source.
  eapply gateway_segment_same with (next := State f_host_json_number (json_number_first json_number_exponent)
    (Kseq (json_number_rest json_number_exponent) continuation) empty_env parameters memory);
    [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_seq |apply gateway_segment_here].
Qed.

Theorem gateway_json_exponent_skipped {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) parameters continuation memory :
  gateway_ambient_closed backend property -> parameters ! _t'12 = Some (Vint Int.zero) ->
  gateway_source_segment backend ge property
    (State f_host_json_number Sskip (json_exponent_test_cont continuation) empty_env parameters memory)
    (State f_host_json_number Sskip continuation empty_env parameters memory) property.
Proof.
  intros CLOSED FLAG; unfold json_exponent_test_cont.
  gateway_segment_dynamic CLOSED ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
Qed.

Theorem gateway_json_exponent_entered {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) parameters continuation index memory :
  gateway_ambient_closed backend property -> parameters ! _t'12 = Some (Vint Int.one) ->
  parameters ! _index = Some (Vlong (Int64.repr index)) ->
  gateway_source_segment backend ge property
    (State f_host_json_number Sskip (json_exponent_test_cont continuation) empty_env parameters memory)
    (State f_host_json_number json_exponent_sign_source (json_exponent_sign_cont continuation) empty_env
      (PTree.set _index (Vlong (Int64.repr (index + 1))) parameters) memory) property.
Proof.
  intros CLOSED FLAG POSITION; unfold json_exponent_test_cont, json_exponent_sign_cont.
  eapply gateway_segment_same with (next := State f_host_json_number json_exponent_select continuation empty_env parameters memory);
    [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_skip_seq |].
  eapply gateway_segment_same with (next := State f_host_json_number json_number_exponent_branch continuation empty_env parameters memory).
  - exact CLOSED.
  - cbn; tauto.
  - intros; eapply certified_if_edge with (v := Vint Int.one) (b := true);
      [apply old_expression_value, value_temp; exact FLAG |reflexivity].
  - eapply gateway_segment_same with (next := State f_host_json_number json_scan_increment
      (Kseq json_number_exponent_after_marker continuation) empty_env parameters memory);
      [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_seq |].
    eapply gateway_segment_same with (next := State f_host_json_number Sskip
      (Kseq json_number_exponent_after_marker continuation) empty_env
      (PTree.set _index (Vlong (Int64.repr (index + 1))) parameters) memory).
    + exact CLOSED.
    + cbn; tauto.
    + intros; apply certified_set_edge; eapply binary_expression_value with (v := Vlong (Int64.repr index)) (w := Vint Int.one).
      * apply old_expression_value, value_temp; exact POSITION.
      * apply old_expression_value, value_int.
      * change (Some (Vlong (Int64.add (Int64.repr index) (Int64.repr 1))) = Some (Vlong (Int64.repr (index + 1)))).
        rewrite json_number_word_increment; reflexivity.
    + eapply gateway_segment_same with (next := State f_host_json_number json_number_exponent_after_marker continuation empty_env
        (PTree.set _index (Vlong (Int64.repr (index + 1))) parameters) memory);
        [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_skip_seq |].
      eapply gateway_segment_same with (next := State f_host_json_number json_exponent_sign_source
        (Kseq json_number_exponent_after_sign continuation) empty_env
        (PTree.set _index (Vlong (Int64.repr (index + 1))) parameters) memory);
        [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_seq |apply gateway_segment_here].
Qed.

Theorem gateway_json_exponent_sign_to_test {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) parameters continuation memory :
  gateway_ambient_closed backend property ->
  gateway_source_segment backend ge property
    (State f_host_json_number json_exponent_sign_source continuation empty_env parameters memory)
    (State f_host_json_number (json_marker_source json_exponent_sign)
      (json_exponent_sign_test_cont continuation) empty_env parameters memory) property.
Proof.
  intro CLOSED; unfold json_exponent_sign_test_cont, json_exponent_sign_select, json_marker_source.
  eapply gateway_segment_same with (next := State f_host_json_number
    (json_number_first json_exponent_sign_source) (Kseq (json_number_rest json_exponent_sign_source) continuation)
    empty_env parameters memory);
    [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_seq |apply gateway_segment_here].
Qed.

Theorem gateway_json_exponent_sign_advance {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) parameters continuation index (sign : bool) memory :
  gateway_ambient_closed backend property -> parameters ! _t'9 = Some (Vint (if sign then Int.one else Int.zero)) ->
  parameters ! _index = Some (Vlong (Int64.repr index)) ->
  gateway_source_segment backend ge property
    (State f_host_json_number Sskip (json_exponent_sign_test_cont continuation) empty_env parameters memory)
    (State f_host_json_number Sskip continuation empty_env
      (if sign then PTree.set _index (Vlong (Int64.repr (index + 1))) parameters else parameters) memory) property.
Proof.
  intros CLOSED FLAG POSITION; unfold json_exponent_sign_test_cont.
  eapply gateway_segment_same with (next := State f_host_json_number json_exponent_sign_select continuation empty_env parameters memory);
    [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_skip_seq |].
  destruct sign.
  - eapply gateway_segment_same with (next := State f_host_json_number json_scan_increment continuation empty_env parameters memory).
    + exact CLOSED.
    + cbn; tauto.
    + intros; eapply certified_if_edge with (v := Vint Int.one) (b := true);
        [apply old_expression_value, value_temp; exact FLAG |reflexivity].
    + eapply gateway_segment_same with (next := State f_host_json_number Sskip continuation empty_env
        (PTree.set _index (Vlong (Int64.repr (index + 1))) parameters) memory).
      * exact CLOSED.
      * cbn; tauto.
      * intros; apply certified_set_edge; eapply binary_expression_value with (v := Vlong (Int64.repr index)) (w := Vint Int.one).
        -- apply old_expression_value, value_temp; exact POSITION.
        -- apply old_expression_value, value_int.
        -- change (Some (Vlong (Int64.add (Int64.repr index) (Int64.repr 1))) = Some (Vlong (Int64.repr (index + 1)))).
           rewrite json_number_word_increment; reflexivity.
      * apply gateway_segment_here.
  - eapply gateway_segment_same with (next := State f_host_json_number Sskip continuation empty_env parameters memory).
    + exact CLOSED.
    + cbn; tauto.
    + intros; eapply certified_if_edge with (v := Vint Int.zero) (b := false);
        [apply old_expression_value, value_temp; exact FLAG |reflexivity].
    + apply gateway_segment_here.
Qed.

Theorem gateway_json_exponent_loop_entry {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) parameters continuation index memory :
  gateway_ambient_closed backend property -> parameters ! _index = Some (Vlong (Int64.repr index)) ->
  gateway_source_segment backend ge property
    (State f_host_json_number Sskip (json_exponent_sign_cont continuation) empty_env parameters memory)
    (State f_host_json_number json_number_exponent_loop (json_exponent_loop_cont continuation) empty_env
      (PTree.set _exponent (Vlong (Int64.repr index)) parameters) memory) property.
Proof.
  intros CLOSED POSITION; unfold json_exponent_sign_cont, json_exponent_loop_cont.
  gateway_segment_dynamic CLOSED ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
Qed.

Theorem gateway_json_number_exponent_sign_source {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) parameters continuation object index count remaining memory :
  gateway_ambient_closed backend property -> 0 <= index ->
  index + Z.of_nat (length remaining) = count -> count <= 65536 ->
  parameters ! _bytes = Some (Vptr object Ptrofs.zero) -> parameters ! _index = Some (Vlong (Int64.repr index)) ->
  parameters ! _size = Some (Vlong (Int64.repr count)) ->
  (forall offset byte, nth_error remaining offset = Some byte -> forall memory world, property memory world ->
    Mem.loadv Mint8signed memory (Vptr object (Ptrofs.repr (index + Z.of_nat offset))) = Some (Vint (Int.repr (Byte.signed byte)))) ->
  let (sign, tail) := json_number_take_exponent_sign remaining in
  exists changed,
    gateway_source_segment backend ge property
      (State f_host_json_number json_exponent_sign_source continuation empty_env parameters memory)
      (State f_host_json_number Sskip continuation empty_env changed memory) property /\
    changed ! _bytes = Some (Vptr object Ptrofs.zero) /\
    changed ! _size = Some (Vlong (Int64.repr count)) /\
    changed ! _index = Some (Vlong (Int64.repr (index + Z.of_nat (length sign)))) /\
    (forall identifier, ~ In identifier json_exponent_sign_written -> changed ! identifier = parameters ! identifier).
Proof.
  intros CLOSED INDEX LENGTH BOUND BYTES POSITION SIZE LOADS.
  pose proof (gateway_json_exponent_sign_to_test backend ge property parameters continuation memory CLOSED) as PREFIX.
  destruct remaining as [|byte rest].
  - cbn in LENGTH; rewrite Z.add_0_r in LENGTH; subst index; cbn [json_number_take_exponent_sign].
    destruct (gateway_json_number_marker_end backend ge property json_exponent_sign parameters
      (json_exponent_sign_test_cont continuation) count memory CLOSED ltac:(lia) POSITION SIZE)
      as (tested & TEST & FLAG & FRAME).
    assert (TEST_INDEX : tested ! _index = Some (Vlong (Int64.repr count))) by
      (rewrite FRAME; [exact POSITION |discriminate]).
    exists tested; split.
    + eapply json_number_segment_compose; [exact PREFIX |]. eapply json_number_segment_compose; [exact TEST |].
      apply (gateway_json_exponent_sign_advance backend ge property tested continuation count false memory); assumption.
    + split; [rewrite FRAME; [exact BYTES |discriminate] |].
      split; [rewrite FRAME; [exact SIZE |discriminate] |]. split.
      * cbn; rewrite Z.add_0_r; exact TEST_INDEX.
      * intros identifier OUTSIDE; apply FRAME; intro SAME; apply OUTSIDE; subst identifier; cbn; auto.
  - assert (RANGE : 0 <= index /\ index < count /\ count <= 65536).
    { change (index + Z.of_nat (S (length rest)) = count) in LENGTH; rewrite Nat2Z.inj_succ in LENGTH; lia. }
    destruct (gateway_json_number_marker_test backend ge property json_exponent_sign parameters
      (json_exponent_sign_test_cont continuation) object index count byte memory CLOSED RANGE BYTES POSITION SIZE
      ltac:(intros changed owner GOOD; specialize (LOADS 0%nat byte eq_refl changed owner GOOD); cbn in LOADS;
        rewrite Z.add_0_r in LOADS; exact LOADS)) as (tested & TEST & FLAG & FRAME).
    assert (TEST_BYTES : tested ! _bytes = Some (Vptr object Ptrofs.zero)) by
      (rewrite FRAME; [exact BYTES |cbn; intuition discriminate]).
    assert (TEST_SIZE : tested ! _size = Some (Vlong (Int64.repr count))) by
      (rewrite FRAME; [exact SIZE |cbn; intuition discriminate]).
    assert (TEST_INDEX : tested ! _index = Some (Vlong (Int64.repr index))) by
      (rewrite FRAME; [exact POSITION |cbn; intuition discriminate]).
    cbn [json_marker_flag json_marker_matches] in FLAG.
    cbn [json_number_take_exponent_sign]; destruct (Byte.eq byte (Byte.repr 43) || Byte.eq byte (Byte.repr 45)) eqn:SIGN.
    + rewrite ?SIGN in FLAG; exists (PTree.set _index (Vlong (Int64.repr (index + 1))) tested); split.
      * eapply json_number_segment_compose; [exact PREFIX |]. eapply json_number_segment_compose; [exact TEST |].
        apply (gateway_json_exponent_sign_advance backend ge property tested continuation index true memory); assumption.
      * split; [rewrite PTree.gso by discriminate; exact TEST_BYTES |].
        split; [rewrite PTree.gso by discriminate; exact TEST_SIZE |]. split; [apply PTree.gss |].
        intros identifier OUTSIDE; rewrite PTree.gso by (intro SAME; apply OUTSIDE; subst identifier; cbn; auto).
        apply FRAME; intro MEMBER; apply OUTSIDE; cbn in MEMBER |- *; intuition.
    + rewrite ?SIGN in FLAG; exists tested; split.
      * eapply json_number_segment_compose; [exact PREFIX |]. eapply json_number_segment_compose; [exact TEST |].
        apply (gateway_json_exponent_sign_advance backend ge property tested continuation index false memory); assumption.
      * split; [exact TEST_BYTES |]. split; [exact TEST_SIZE |]. split; [cbn; rewrite Z.add_0_r; exact TEST_INDEX |].
        intros identifier OUTSIDE; apply FRAME; intro MEMBER; apply OUTSIDE; cbn in MEMBER |- *; intuition.
Qed.

Theorem gateway_json_exponent_guard {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) parameters continuation start finish memory :
  gateway_ambient_closed backend property -> 0 <= start <= 65536 -> 0 <= finish <= 65536 ->
  parameters ! _index = Some (Vlong (Int64.repr finish)) ->
  parameters ! _exponent = Some (Vlong (Int64.repr start)) ->
  gateway_source_segment backend ge property
    (State f_host_json_number Sskip (json_exponent_loop_cont continuation) empty_env parameters memory)
    (State f_host_json_number (if Z.eqb finish start then Sgoto _invalid else Sskip)
      continuation empty_env parameters memory) property.
Proof.
  intros CLOSED START FINISH POSITION FRACTION; unfold json_exponent_loop_cont.
  eapply gateway_segment_same with (next := State f_host_json_number json_number_exponent_guard continuation empty_env parameters memory);
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


Theorem gateway_json_number_exponent_source {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) parameters continuation object index count remaining memory :
  gateway_ambient_closed backend property -> call_cont continuation = Kstop ->
  0 <= index -> index + Z.of_nat (length remaining) = count -> count <= 65536 ->
  parameters ! _bytes = Some (Vptr object Ptrofs.zero) -> parameters ! _index = Some (Vlong (Int64.repr index)) ->
  parameters ! _size = Some (Vlong (Int64.repr count)) ->
  (forall offset byte, nth_error remaining offset = Some byte -> forall memory world, property memory world ->
    Mem.loadv Mint8signed memory (Vptr object (Ptrofs.repr (index + Z.of_nat offset))) = Some (Vint (Int.repr (Byte.signed byte)))) ->
  match json_number_take_exponent remaining with
  | None => gateway_failure_when backend ge property
      (State f_host_json_number json_number_exponent continuation empty_env parameters memory)
  | Some (fragment, tail) => exists changed,
      gateway_source_segment backend ge property
        (State f_host_json_number json_number_exponent continuation empty_env parameters memory)
        (State f_host_json_number Sskip continuation empty_env changed memory) property /\
      changed ! _bytes = Some (Vptr object Ptrofs.zero) /\
      changed ! _size = Some (Vlong (Int64.repr count)) /\
      changed ! _index = Some (Vlong (Int64.repr (index + Z.of_nat (length fragment)))) /\
      (forall identifier, ~ In identifier json_exponent_written -> changed ! identifier = parameters ! identifier)
  end.
Proof.
  intros CLOSED STOP INDEX LENGTH BOUND BYTES POSITION SIZE LOADS.
  pose proof (gateway_json_exponent_to_test backend ge property parameters continuation memory CLOSED) as PREFIX.
  destruct remaining as [|byte rest].
  - cbn in LENGTH; rewrite Z.add_0_r in LENGTH; subst index; cbn [json_number_take_exponent].
    destruct (gateway_json_number_marker_end backend ge property json_exponent_marker parameters
      (json_exponent_test_cont continuation) count memory CLOSED ltac:(lia) POSITION SIZE)
      as (tested & TEST & FLAG & FRAME).
    exists tested; split.
    + eapply json_number_segment_compose; [exact PREFIX |]. eapply json_number_segment_compose; [exact TEST |].
      apply gateway_json_exponent_skipped; assumption.
    + split; [rewrite FRAME; [exact BYTES |discriminate] |].
      split; [rewrite FRAME; [exact SIZE |discriminate] |]. split.
      * cbn; rewrite Z.add_0_r; rewrite FRAME; [exact POSITION |discriminate].
      * intros identifier OUTSIDE; apply FRAME; intro SAME; apply OUTSIDE; subst identifier; cbn; auto.
  - assert (RANGE : 0 <= index /\ index < count /\ count <= 65536).
    { change (index + Z.of_nat (S (length rest)) = count) in LENGTH; rewrite Nat2Z.inj_succ in LENGTH; lia. }
    assert (TAIL_LENGTH : index + 1 + Z.of_nat (length rest) = count).
    { change (index + Z.of_nat (S (length rest)) = count) in LENGTH; rewrite Nat2Z.inj_succ in LENGTH; lia. }
    destruct (gateway_json_number_marker_test backend ge property json_exponent_marker parameters
      (json_exponent_test_cont continuation) object index count byte memory CLOSED RANGE BYTES POSITION SIZE
      ltac:(intros changed owner GOOD; specialize (LOADS 0%nat byte eq_refl changed owner GOOD); cbn in LOADS;
        rewrite Z.add_0_r in LOADS; exact LOADS)) as (tested & TEST & FLAG & TEST_FRAME).
    assert (TEST_BYTES : tested ! _bytes = Some (Vptr object Ptrofs.zero)) by
      (rewrite TEST_FRAME; [exact BYTES |cbn; intuition discriminate]).
    assert (TEST_SIZE : tested ! _size = Some (Vlong (Int64.repr count))) by
      (rewrite TEST_FRAME; [exact SIZE |cbn; intuition discriminate]).
    assert (TEST_INDEX : tested ! _index = Some (Vlong (Int64.repr index))) by
      (rewrite TEST_FRAME; [exact POSITION |cbn; intuition discriminate]).
    cbn [json_number_take_exponent]; destruct (Byte.eq byte (Byte.repr 101) || Byte.eq byte (Byte.repr 69)) eqn:MARKER.
    + cbn [json_marker_flag json_marker_matches] in FLAG; rewrite MARKER in FLAG.
      pose proof (gateway_json_exponent_entered backend ge property tested continuation index memory CLOSED FLAG TEST_INDEX) as ENTER.
      set (entered := PTree.set _index (Vlong (Int64.repr (index + 1))) tested).
      pose proof (gateway_json_number_exponent_sign_source backend ge property entered (json_exponent_sign_cont continuation)
        object (index + 1) count rest memory CLOSED ltac:(lia) TAIL_LENGTH BOUND
        ltac:(unfold entered; rewrite PTree.gso by discriminate; exact TEST_BYTES) ltac:(unfold entered; apply PTree.gss)
        ltac:(unfold entered; rewrite PTree.gso by discriminate; exact TEST_SIZE)
        ltac:(intros offset selected SELECTED changed owner GOOD; specialize (LOADS (S offset) selected SELECTED changed owner GOOD);
          rewrite Nat2Z.inj_succ in LOADS; replace (index + Z.succ (Z.of_nat offset)) with (index + 1 + Z.of_nat offset) in LOADS by lia;
          exact LOADS)) as SIGNED.
      pose proof (json_number_exponent_sign_sound rest) as SIGN_LEXICAL.
      destruct (json_number_take_exponent_sign rest) as [sign unsigned] eqn:SIGN; cbn in SIGNED, SIGN_LEXICAL |- *.
      destruct SIGNED as (signed & SIGNED & SIGN_BYTES & SIGN_SIZE & SIGN_INDEX & SIGN_FRAME).
      destruct SIGN_LEXICAL as [SIGN_REST SIGN_KIND].
      assert (UNSIGNED_LENGTH : index + 1 + Z.of_nat (length sign) + Z.of_nat (length unsigned) = count).
      { rewrite SIGN_REST, length_app, Nat2Z.inj_add in TAIL_LENGTH; lia. }
      pose proof (gateway_json_exponent_loop_entry backend ge property signed continuation
        (index + 1 + Z.of_nat (length sign)) memory CLOSED SIGN_INDEX) as ENTRY.
      set (positioned := PTree.set _exponent (Vlong (Int64.repr (index + 1 + Z.of_nat (length sign)))) signed).
      pose proof (gateway_json_number_scan_digits backend ge property json_exponent_scan (json_exponent_loop_cont continuation)
        object count memory CLOSED ltac:(lia) unsigned positioned (index + 1 + Z.of_nat (length sign)) ltac:(lia)
        UNSIGNED_LENGTH
        ltac:(unfold positioned; rewrite PTree.gso by discriminate; exact SIGN_BYTES)
        ltac:(unfold positioned; rewrite PTree.gso by discriminate; exact SIGN_INDEX)
        ltac:(unfold positioned; rewrite PTree.gso by discriminate; exact SIGN_SIZE)
        ltac:(intros offset selected SELECTED changed owner GOOD;
          specialize (LOADS (S (length sign + offset)) selected
            ltac:(cbn; rewrite SIGN_REST, nth_error_app2 by lia; replace (length sign + offset - length sign)%nat with offset by lia; exact SELECTED)
            changed owner GOOD);
          rewrite Nat2Z.inj_succ, Nat2Z.inj_add in LOADS;
          replace (index + Z.succ (Z.of_nat (length sign) + Z.of_nat offset)) with
            (index + 1 + Z.of_nat (length sign) + Z.of_nat offset) in LOADS by lia; exact LOADS)) as SCAN.
      pose proof (json_number_take_digits_sound unsigned) as LEXICAL.
      destruct (json_number_take_digits unsigned) as [digits tail] eqn:TAKE; cbn in SCAN, LEXICAL |- *.
      destruct SCAN as (scanned & SCAN & SCAN_BYTES & SCAN_SIZE & SCAN_INDEX & SCAN_FRAME).
      destruct LEXICAL as [REST [DIGITS TAIL]].
      assert (DIGIT_LENGTH : Z.of_nat (length digits) <= Z.of_nat (length unsigned)).
      { rewrite REST, length_app, Nat2Z.inj_add; lia. }
      assert (EXPONENT : scanned ! _exponent = Some (Vlong (Int64.repr (index + 1 + Z.of_nat (length sign))))) by
        (rewrite SCAN_FRAME; [unfold positioned; apply PTree.gss |cbn; intuition discriminate]).
      pose proof (gateway_json_exponent_guard backend ge property scanned continuation (index + 1 + Z.of_nat (length sign))
        (index + 1 + Z.of_nat (length sign) + Z.of_nat (length digits)) memory CLOSED ltac:(lia) ltac:(lia) SCAN_INDEX EXPONENT) as GUARD.
      assert (TO_GUARD : gateway_source_segment backend ge property
        (State f_host_json_number json_number_exponent continuation empty_env parameters memory)
        (State f_host_json_number
          (if Z.eqb (index + 1 + Z.of_nat (length sign) + Z.of_nat (length digits)) (index + 1 + Z.of_nat (length sign)) then Sgoto _invalid else Sskip)
          continuation empty_env scanned memory) property).
      { eapply json_number_segment_compose; [exact PREFIX |]. eapply json_number_segment_compose; [exact TEST |].
        eapply json_number_segment_compose; [exact ENTER |]. eapply json_number_segment_compose; [exact SIGNED |].
        eapply json_number_segment_compose; [exact ENTRY |]. eapply json_number_segment_compose; [exact SCAN |exact GUARD]. }
      destruct digits as [|first digits].
      * cbn in TO_GUARD; rewrite Z.add_0_r, Z.eqb_refl in TO_GUARD.
        eapply json_number_segment_denial; [exact TO_GUARD |apply gateway_json_number_invalid_denied; exact STOP].
      * assert (NONEMPTY : (index + 1 + Z.of_nat (length sign) + Z.of_nat (length (first :: digits)) =? index + 1 + Z.of_nat (length sign)) = false).
        { apply Z.eqb_neq; change (index + 1 + Z.of_nat (length sign) + Z.of_nat (S (length digits)) <> index + 1 + Z.of_nat (length sign));
            rewrite Nat2Z.inj_succ; lia. }
        rewrite NONEMPTY in TO_GUARD; exists scanned; split; [exact TO_GUARD |].
        split; [exact SCAN_BYTES |]. split; [exact SCAN_SIZE |]. split.
        -- change (scanned ! _index = Some (Vlong (Int64.repr (index + Z.of_nat (S (length (sign ++ first :: digits)))))));
             rewrite Nat2Z.inj_succ, length_app, Nat2Z.inj_add;
             replace (index + Z.succ (Z.of_nat (length sign) + Z.of_nat (length (first :: digits)))) with
               (index + 1 + Z.of_nat (length sign) + Z.of_nat (length (first :: digits))) by lia; exact SCAN_INDEX.
        -- intros identifier OUTSIDE; rewrite SCAN_FRAME; [unfold positioned; rewrite PTree.gso; [rewrite SIGN_FRAME;
             [unfold entered; rewrite PTree.gso; [apply TEST_FRAME |] |] |] |];
             intro MEMBER; apply OUTSIDE; cbn in MEMBER |- *; intuition.
    + cbn [json_marker_flag json_marker_matches] in FLAG; rewrite MARKER in FLAG.
      exists tested; split.
      * eapply json_number_segment_compose; [exact PREFIX |]. eapply json_number_segment_compose; [exact TEST |].
        apply gateway_json_exponent_skipped; assumption.
      * split; [exact TEST_BYTES |]. split; [exact TEST_SIZE |]. split; [cbn; rewrite Z.add_0_r; exact TEST_INDEX |].
        intros identifier OUTSIDE; apply TEST_FRAME; intro MEMBER; apply OUTSIDE; cbn in MEMBER |- *; intuition.
Qed.
