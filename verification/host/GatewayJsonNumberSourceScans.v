(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual fractional/exponent loops test signed bytes before incrementing the bounded index. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayJsonNumberSource GatewayJsonNumberSourceBytes
  GatewayIntegerCanonical GatewayIntegerLoop GatewaySourceSegments GatewaySourceSegmentAutomation GatewayFramedRuntime.
Import ListNotations.
Open Scope Z_scope.

Inductive json_number_scan := json_fraction_scan | json_exponent_scan.
Definition json_scan_lower scan := match scan with json_fraction_scan => _t'6 | json_exponent_scan => _t'10 end.
Definition json_scan_upper scan := match scan with json_fraction_scan => _t'7 | json_exponent_scan => _t'11 end.
Definition json_scan_lower_character scan := match scan with json_fraction_scan => _t'31 | json_exponent_scan => _t'25 end.
Definition json_scan_upper_character scan := match scan with json_fraction_scan => _t'30 | json_exponent_scan => _t'24 end.
Definition json_scan_character := Ederef (Ebinop Oadd (Etempvar _bytes (tptr tschar)) (Etempvar _index tulong) (tptr tschar)) tschar.
Definition json_scan_increment := Sset _index (Ebinop Oadd (Etempvar _index tulong) (Econst_int Int.one tint) tulong).
Definition json_scan_test scan := Ssequence
  (Sifthenelse (Ebinop Olt (Etempvar _index tulong) (Etempvar _size tulong) tint)
    (Ssequence (Sset (json_scan_lower_character scan) json_scan_character)
      (Sset (json_scan_lower scan) (Ecast
        (Ebinop Oge (Etempvar (json_scan_lower_character scan) tschar) (Econst_int (Int.repr 48) tint) tint) tbool)))
    (Sset (json_scan_lower scan) (Econst_int Int.zero tint)))
  (Sifthenelse (Etempvar (json_scan_lower scan) tint)
    (Ssequence (Sset (json_scan_upper_character scan) json_scan_character)
      (Sset (json_scan_upper scan) (Ecast
        (Ebinop Ole (Etempvar (json_scan_upper_character scan) tschar) (Econst_int (Int.repr 57) tint) tint) tbool)))
    (Sset (json_scan_upper scan) (Econst_int Int.zero tint))).
Definition json_scan_body scan := Ssequence
  (Ssequence (json_scan_test scan) (Sifthenelse (Etempvar (json_scan_upper scan) tint) Sskip Sbreak))
  json_scan_increment.
Definition json_scan_source scan := match scan with json_fraction_scan => json_number_fraction_loop | json_exponent_scan => json_number_exponent_loop end.

Theorem json_scan_source_shape scan : json_scan_source scan = Sloop (json_scan_body scan) Sskip.
Proof. destruct scan; reflexivity. Qed.

Theorem gateway_json_number_scan_test {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) scan parameters continuation object index count byte memory :
  gateway_ambient_closed backend property -> 0 <= index /\ index < count /\ count <= 65536 ->
  parameters ! _bytes = Some (Vptr object Ptrofs.zero) -> parameters ! _index = Some (Vlong (Int64.repr index)) ->
  parameters ! _size = Some (Vlong (Int64.repr count)) ->
  (forall memory world, property memory world -> Mem.loadv Mint8signed memory (Vptr object (Ptrofs.repr index)) =
    Some (Vint (Int.repr (Byte.signed byte)))) ->
  exists next_parameters,
    gateway_source_segment backend ge property
      (State f_host_json_number (json_scan_test scan) continuation empty_env parameters memory)
      (State f_host_json_number Sskip continuation empty_env next_parameters memory) property /\
    (forall identifier, ~ In identifier [json_scan_lower scan; json_scan_upper scan;
      json_scan_lower_character scan; json_scan_upper_character scan] -> next_parameters ! identifier = parameters ! identifier) /\
    next_parameters ! _bytes = parameters ! _bytes /\ next_parameters ! _index = parameters ! _index /\
    next_parameters ! _size = parameters ! _size /\
    next_parameters ! (json_scan_upper scan) = Some (Vint (if gateway_integer_digit byte then Int.one else Int.zero)).
Proof.
  intros CLOSED INDEX BYTES POSITION SIZE CHARACTER.
  assert (LESS : Int64.ltu (Int64.repr index) (Int64.repr count) = true).
  { rewrite json_number_word_less by lia; apply Z.ltb_lt; lia. }
  destruct (zlt (Byte.signed byte) 48) as [LOW |NOT_LOW];
    [|destruct (zlt 57 (Byte.signed byte)) as [HIGH |NOT_HIGH]]; destruct scan; eexists; split.
  all: try (unfold json_scan_test, json_scan_lower, json_scan_upper, json_scan_lower_character, json_scan_upper_character, json_scan_character;
    gateway_segment_dynamic CLOSED
      ltac:(fun _ => eapply gateway_json_number_character with (index := index) (byte := byte) (object := object);
        [lia |repeat rewrite PTree.gso by discriminate; exact BYTES |repeat rewrite PTree.gso by discriminate; exact POSITION |
         eapply CHARACTER; eassumption])
      ltac:(fun _ => cbn -[Int64.ltu Int64.unsigned Int64.repr Int64.add Int.signed Int.repr Int.lt]; unfold Int.lt;
        repeat rewrite Int.signed_repr by (pose proof (gateway_integer_signed_range byte);
          change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia);
        try rewrite LESS;
        repeat first [rewrite zlt_true by lia |rewrite zlt_false by lia]; reflexivity)).
  all: repeat split; try solve [repeat rewrite PTree.gso by discriminate; reflexivity].
  all: try solve [intros identifier OUTSIDE; repeat rewrite PTree.gso by
    (intro SAME; apply OUTSIDE; subst identifier; cbn; auto 8); reflexivity].
  all: unfold json_scan_upper; repeat rewrite PTree.gso by discriminate; try rewrite PTree.gss.
  all: rewrite gateway_integer_digit_signed.
  all: destruct (48 <=? Byte.signed byte) eqn:FROM; destruct (Byte.signed byte <=? 57) eqn:TO;
    first [apply Z.leb_le in FROM |apply Z.leb_gt in FROM];
    first [apply Z.leb_le in TO |apply Z.leb_gt in TO]; try lia; reflexivity.
Qed.

Theorem gateway_json_number_scan_test_end {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) scan parameters continuation count memory :
  gateway_ambient_closed backend property -> 0 <= count <= 65536 ->
  parameters ! _index = Some (Vlong (Int64.repr count)) -> parameters ! _size = Some (Vlong (Int64.repr count)) ->
  exists next_parameters,
    gateway_source_segment backend ge property
      (State f_host_json_number (json_scan_test scan) continuation empty_env parameters memory)
      (State f_host_json_number Sskip continuation empty_env next_parameters memory) property /\
    (forall identifier, ~ In identifier [json_scan_lower scan; json_scan_upper scan] ->
      next_parameters ! identifier = parameters ! identifier) /\
    next_parameters ! (json_scan_upper scan) = Some (Vint Int.zero).
Proof.
  intros CLOSED COUNT POSITION SIZE.
  assert (LESS : Int64.ltu (Int64.repr count) (Int64.repr count) = false).
  { unfold Int64.ltu; rewrite zlt_false by lia; reflexivity. }
  destruct scan; eexists; split.
  all: try (unfold json_scan_test, json_scan_lower, json_scan_upper;
    gateway_segment_dynamic CLOSED ltac:(fun _ => fail)
      ltac:(fun _ => cbn -[Int64.ltu]; rewrite ?LESS; reflexivity)).
  all: split; [intros identifier OUTSIDE; repeat rewrite PTree.gso by
    (intro SAME; apply OUTSIDE; subst identifier; cbn; auto); reflexivity |unfold json_scan_upper; apply PTree.gss].
Qed.

Lemma json_number_segment_compose {World Event} (backend : gateway_backend World Event) ge
    property source middle boundary target result :
  gateway_source_segment backend ge property source middle boundary ->
  gateway_source_segment backend ge boundary middle target result ->
  gateway_source_segment backend ge property source target result.
Proof.
  intro FIRST; induction FIRST; intro SECOND; [exact SECOND |].
  eapply gateway_segment_next; [exact H |exact H0 |exact H1 |apply IHFIRST; exact SECOND].
Qed.

Theorem gateway_json_number_scan_to_test {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) scan parameters continuation memory :
  gateway_ambient_closed backend property ->
  gateway_source_segment backend ge property
    (State f_host_json_number (json_scan_source scan) continuation empty_env parameters memory)
    (State f_host_json_number (json_scan_test scan)
      (Kseq (Sifthenelse (Etempvar (json_scan_upper scan) tint) Sskip Sbreak)
        (Kseq json_scan_increment (Kloop1 (json_scan_body scan) Sskip continuation))) empty_env parameters memory) property.
Proof.
  intro CLOSED; rewrite json_scan_source_shape.
  eapply gateway_segment_same with (next := State f_host_json_number (json_scan_body scan)
    (Kloop1 (json_scan_body scan) Sskip continuation) empty_env parameters memory);
    [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_loop |].
  unfold json_scan_body at 1.
  gateway_segment_dynamic CLOSED ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
Qed.

Definition json_scan_after_test scan continuation :=
  Kseq (Sifthenelse (Etempvar (json_scan_upper scan) tint) Sskip Sbreak)
    (Kseq json_scan_increment (Kloop1 (json_scan_body scan) Sskip continuation)).

Theorem gateway_json_number_scan_break {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) scan parameters continuation memory :
  gateway_ambient_closed backend property -> parameters ! (json_scan_upper scan) = Some (Vint Int.zero) ->
  gateway_source_segment backend ge property
    (State f_host_json_number Sskip (json_scan_after_test scan continuation) empty_env parameters memory)
    (State f_host_json_number Sskip continuation empty_env parameters memory) property.
Proof.
  intros CLOSED STOP; unfold json_scan_after_test.
  eapply gateway_segment_same with (next := State f_host_json_number
    (Sifthenelse (Etempvar (json_scan_upper scan) tint) Sskip Sbreak)
    (Kseq json_scan_increment (Kloop1 (json_scan_body scan) Sskip continuation)) empty_env parameters memory);
    [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_skip_seq |].
  eapply gateway_segment_same with (next := State f_host_json_number Sbreak
    (Kseq json_scan_increment (Kloop1 (json_scan_body scan) Sskip continuation)) empty_env parameters memory).
  - exact CLOSED.
  - cbn; tauto.
  - intros; eapply certified_if_edge with (v := Vint Int.zero) (b := false);
      [apply old_expression_value, value_temp; exact STOP |reflexivity].
  - eapply gateway_segment_same with (next := State f_host_json_number Sbreak
      (Kloop1 (json_scan_body scan) Sskip continuation) empty_env parameters memory);
      [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_break_seq |].
    eapply gateway_segment_same with (next := State f_host_json_number Sskip continuation empty_env parameters memory);
      [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_break_loop1 |apply gateway_segment_here].
Qed.

Theorem gateway_json_number_scan_advance {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) scan parameters continuation index memory :
  gateway_ambient_closed backend property -> parameters ! (json_scan_upper scan) = Some (Vint Int.one) ->
  parameters ! _index = Some (Vlong (Int64.repr index)) ->
  gateway_source_segment backend ge property
    (State f_host_json_number Sskip (json_scan_after_test scan continuation) empty_env parameters memory)
    (State f_host_json_number (json_scan_source scan) continuation empty_env
      (PTree.set _index (Vlong (Int64.repr (index + 1))) parameters) memory) property.
Proof.
  intros CLOSED MORE POSITION; rewrite json_scan_source_shape; unfold json_scan_after_test.
  eapply gateway_segment_same with (next := State f_host_json_number
    (Sifthenelse (Etempvar (json_scan_upper scan) tint) Sskip Sbreak)
    (Kseq json_scan_increment (Kloop1 (json_scan_body scan) Sskip continuation)) empty_env parameters memory);
    [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_skip_seq |].
  eapply gateway_segment_same with (next := State f_host_json_number Sskip
    (Kseq json_scan_increment (Kloop1 (json_scan_body scan) Sskip continuation)) empty_env parameters memory).
  - exact CLOSED.
  - cbn; tauto.
  - intros; eapply certified_if_edge with (v := Vint Int.one) (b := true);
      [apply old_expression_value, value_temp; exact MORE |reflexivity].
  - eapply gateway_segment_same with (next := State f_host_json_number json_scan_increment
      (Kloop1 (json_scan_body scan) Sskip continuation) empty_env parameters memory);
      [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_skip_seq |].
    eapply gateway_segment_same with (next := State f_host_json_number Sskip (Kloop1 (json_scan_body scan) Sskip continuation)
      empty_env (PTree.set _index (Vlong (Int64.repr (index + 1))) parameters) memory).
    + exact CLOSED.
    + cbn; tauto.
    + intros; apply certified_set_edge; eapply binary_expression_value with (v := Vlong (Int64.repr index)) (w := Vint Int.one).
      * apply old_expression_value, value_temp; exact POSITION.
      * apply old_expression_value, value_int.
      * change (Some (Vlong (Int64.add (Int64.repr index) (Int64.repr 1))) = Some (Vlong (Int64.repr (index + 1)))).
        unfold Int64.add; f_equal; f_equal; apply Int64.eqm_samerepr.
        apply Int64.eqm_add; apply Int64.eqm_unsigned_repr_l; apply Int64.eqm_refl.
    + eapply gateway_segment_same with (next := State f_host_json_number Sskip (Kloop2 (json_scan_body scan) Sskip continuation)
        empty_env (PTree.set _index (Vlong (Int64.repr (index + 1))) parameters) memory);
        [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_skip_loop1 |].
      eapply gateway_segment_same with (next := State f_host_json_number (Sloop (json_scan_body scan) Sskip) continuation
        empty_env (PTree.set _index (Vlong (Int64.repr (index + 1))) parameters) memory);
        [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_skip_loop2 |apply gateway_segment_here].
Qed.

Theorem gateway_json_number_scan_one {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) scan parameters continuation object index count byte memory :
  gateway_ambient_closed backend property -> 0 <= index /\ index < count /\ count <= 65536 ->
  parameters ! _bytes = Some (Vptr object Ptrofs.zero) -> parameters ! _index = Some (Vlong (Int64.repr index)) ->
  parameters ! _size = Some (Vlong (Int64.repr count)) ->
  (forall memory world, property memory world -> Mem.loadv Mint8signed memory (Vptr object (Ptrofs.repr index)) =
    Some (Vint (Int.repr (Byte.signed byte)))) ->
  exists next_parameters,
    gateway_source_segment backend ge property
      (State f_host_json_number (json_scan_source scan) continuation empty_env parameters memory)
      (if gateway_integer_digit byte then State f_host_json_number (json_scan_source scan) continuation empty_env next_parameters memory
       else State f_host_json_number Sskip continuation empty_env next_parameters memory) property /\
    next_parameters ! _bytes = Some (Vptr object Ptrofs.zero) /\
    next_parameters ! _size = Some (Vlong (Int64.repr count)) /\
    next_parameters ! _index = Some (Vlong (Int64.repr (if gateway_integer_digit byte then index + 1 else index))) /\
    (forall identifier, ~ In identifier [_index; json_scan_lower scan; json_scan_upper scan;
      json_scan_lower_character scan; json_scan_upper_character scan] -> next_parameters ! identifier = parameters ! identifier).
Proof.
  intros CLOSED INDEX BYTES POSITION SIZE CHARACTER.
  pose proof (gateway_json_number_scan_to_test backend ge property scan parameters continuation memory CLOSED) as TO_TEST.
  destruct (gateway_json_number_scan_test backend ge property scan parameters (json_scan_after_test scan continuation) object index count byte memory
    CLOSED INDEX BYTES POSITION SIZE CHARACTER) as (tested & TEST & FRAME & NEXT_BYTES & NEXT_INDEX & NEXT_SIZE & DIGIT).
  destruct (gateway_integer_digit byte) eqn:DECISION.
  - exists (PTree.set _index (Vlong (Int64.repr (index + 1))) tested); split.
    + eapply json_number_segment_compose; [exact TO_TEST |]. eapply json_number_segment_compose; [exact TEST |].
      apply gateway_json_number_scan_advance; [exact CLOSED |exact DIGIT |rewrite NEXT_INDEX; exact POSITION].
    + split; [rewrite PTree.gso by discriminate; rewrite NEXT_BYTES; exact BYTES |].
      split; [rewrite PTree.gso by discriminate; rewrite NEXT_SIZE; exact SIZE |]. split; [apply PTree.gss |].
      intros identifier OUTSIDE; rewrite PTree.gso by (intro SAME; apply OUTSIDE; cbn; left; congruence).
      apply FRAME; intro MEMBER; apply OUTSIDE; right; exact MEMBER.
  - exists tested; split.
    + eapply json_number_segment_compose; [exact TO_TEST |]. eapply json_number_segment_compose; [exact TEST |].
      apply gateway_json_number_scan_break; assumption.
    + split; [rewrite NEXT_BYTES; exact BYTES |]. split; [rewrite NEXT_SIZE; exact SIZE |].
      split; [rewrite NEXT_INDEX; exact POSITION |]. intros identifier OUTSIDE.
      apply FRAME; intro MEMBER; apply OUTSIDE; right; exact MEMBER.
Qed.

Theorem gateway_json_number_scan_end {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) scan parameters continuation count memory :
  gateway_ambient_closed backend property -> 0 <= count <= 65536 ->
  parameters ! _index = Some (Vlong (Int64.repr count)) -> parameters ! _size = Some (Vlong (Int64.repr count)) ->
  exists next_parameters,
    gateway_source_segment backend ge property
      (State f_host_json_number (json_scan_source scan) continuation empty_env parameters memory)
      (State f_host_json_number Sskip continuation empty_env next_parameters memory) property /\
    (forall identifier, ~ In identifier [json_scan_lower scan; json_scan_upper scan] ->
      next_parameters ! identifier = parameters ! identifier).
Proof.
  intros CLOSED COUNT POSITION SIZE.
  pose proof (gateway_json_number_scan_to_test backend ge property scan parameters continuation memory CLOSED) as TO_TEST.
  destruct (gateway_json_number_scan_test_end backend ge property scan parameters (json_scan_after_test scan continuation) count memory
    CLOSED COUNT POSITION SIZE) as (tested & TEST & FRAME & DIGIT).
  exists tested; split; [|exact FRAME].
  eapply json_number_segment_compose; [exact TO_TEST |]. eapply json_number_segment_compose; [exact TEST |].
  apply gateway_json_number_scan_break; assumption.
Qed.
