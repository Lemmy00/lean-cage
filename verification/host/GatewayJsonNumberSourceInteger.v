(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual integer digit loop increments before its checked bounded byte test. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayJsonNumberSource GatewayJsonNumberSourceBytes
  GatewayIntegerCanonical GatewayIntegerLoop GatewaySourceSegments GatewaySourceSegmentAutomation GatewayFramedRuntime GatewayJsonNumberSourceScans GatewayJsonNumberSourceFold.
Import ListNotations.
Open Scope Z_scope.

Definition json_integer_test := Ssequence
  (Sifthenelse (Ebinop Olt (Etempvar _index tulong) (Etempvar _size tulong) tint)
    (Ssequence (Sset (_t'35) json_scan_character)
      (Sset (_t'3) (Ecast
        (Ebinop Oge (Etempvar (_t'35) tschar) (Econst_int (Int.repr 48) tint) tint) tbool)))
    (Sset (_t'3) (Econst_int Int.zero tint)))
  (Sifthenelse (Etempvar (_t'3) tint)
    (Ssequence (Sset (_t'34) json_scan_character)
      (Sset (_t'4) (Ecast
        (Ebinop Ole (Etempvar (_t'34) tschar) (Econst_int (Int.repr 57) tint) tint) tbool)))
    (Sset (_t'4) (Econst_int Int.zero tint))).
Theorem gateway_json_integer_test {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) parameters continuation object index count byte memory :
  gateway_ambient_closed backend property -> 0 <= index /\ index < count /\ count <= 65536 ->
  parameters ! _bytes = Some (Vptr object Ptrofs.zero) -> parameters ! _index = Some (Vlong (Int64.repr index)) ->
  parameters ! _size = Some (Vlong (Int64.repr count)) ->
  (forall memory world, property memory world -> Mem.loadv Mint8signed memory (Vptr object (Ptrofs.repr index)) =
    Some (Vint (Int.repr (Byte.signed byte)))) ->
  exists next_parameters,
    gateway_source_segment backend ge property
      (State f_host_json_number (json_integer_test) continuation empty_env parameters memory)
      (State f_host_json_number Sskip continuation empty_env next_parameters memory) property /\
    (forall identifier, ~ In identifier [_t'3; _t'4;
      _t'35; _t'34] -> next_parameters ! identifier = parameters ! identifier) /\
    next_parameters ! _bytes = parameters ! _bytes /\ next_parameters ! _index = parameters ! _index /\
    next_parameters ! _size = parameters ! _size /\
    next_parameters ! (_t'4) = Some (Vint (if gateway_integer_digit byte then Int.one else Int.zero)).
Proof.
  intros CLOSED INDEX BYTES POSITION SIZE CHARACTER.
  assert (LESS : Int64.ltu (Int64.repr index) (Int64.repr count) = true).
  { rewrite json_number_word_less by lia; apply Z.ltb_lt; lia. }
  destruct (zlt (Byte.signed byte) 48) as [LOW |NOT_LOW];
    [|destruct (zlt 57 (Byte.signed byte)) as [HIGH |NOT_HIGH]]; eexists; split.
  all: try (unfold json_integer_test, json_scan_character;
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
  all: repeat rewrite PTree.gso by discriminate; try rewrite PTree.gss.
  all: rewrite gateway_integer_digit_signed.
  all: destruct (48 <=? Byte.signed byte) eqn:FROM; destruct (Byte.signed byte <=? 57) eqn:TO;
    first [apply Z.leb_le in FROM |apply Z.leb_gt in FROM];
    first [apply Z.leb_le in TO |apply Z.leb_gt in TO]; try lia; reflexivity.
Qed.

Theorem gateway_json_integer_test_end {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) parameters continuation count memory :
  gateway_ambient_closed backend property -> 0 <= count <= 65536 ->
  parameters ! _index = Some (Vlong (Int64.repr count)) -> parameters ! _size = Some (Vlong (Int64.repr count)) ->
  exists next_parameters,
    gateway_source_segment backend ge property
      (State f_host_json_number (json_integer_test) continuation empty_env parameters memory)
      (State f_host_json_number Sskip continuation empty_env next_parameters memory) property /\
    (forall identifier, ~ In identifier [_t'3; _t'4] ->
      next_parameters ! identifier = parameters ! identifier) /\
    next_parameters ! (_t'4) = Some (Vint Int.zero).
Proof.
  intros CLOSED COUNT POSITION SIZE.
  assert (LESS : Int64.ltu (Int64.repr count) (Int64.repr count) = false).
  { unfold Int64.ltu; rewrite zlt_false by lia; reflexivity. }
  eexists; split.
  all: try (unfold json_integer_test;
    gateway_segment_dynamic CLOSED ltac:(fun _ => fail)
      ltac:(fun _ => cbn -[Int64.ltu]; rewrite ?LESS; reflexivity)).
  all: split; [intros identifier OUTSIDE; repeat rewrite PTree.gso by
    (intro SAME; apply OUTSIDE; subst identifier; cbn; auto); reflexivity |apply PTree.gss].
Qed.


Definition json_integer_guard := Sifthenelse (Etempvar _t'4 tint) Sskip Sbreak.
Definition json_integer_second := Ssequence json_integer_test json_integer_guard.
Definition json_integer_cont continuation := Kseq json_integer_guard (Kloop2 json_scan_increment json_integer_second continuation).
Definition json_integer_written := [_index; _t'3; _t'4; _t'35; _t'34].

Theorem json_integer_loop_shape : json_number_integer_loop = Sloop json_scan_increment json_integer_second.
Proof. reflexivity. Qed.

Theorem gateway_json_integer_increment {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) parameters continuation index memory :
  gateway_ambient_closed backend property -> parameters ! _index = Some (Vlong (Int64.repr index)) ->
  gateway_source_segment backend ge property
    (State f_host_json_number json_number_integer_loop continuation empty_env parameters memory)
    (State f_host_json_number json_integer_test (json_integer_cont continuation) empty_env
      (PTree.set _index (Vlong (Int64.repr (index + 1))) parameters) memory) property.
Proof.
  intros CLOSED POSITION; rewrite json_integer_loop_shape.
  eapply gateway_segment_same with (next := State f_host_json_number json_scan_increment
    (Kloop1 json_scan_increment json_integer_second continuation) empty_env parameters memory);
    [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_loop |].
  eapply gateway_segment_same with (next := State f_host_json_number Sskip
    (Kloop1 json_scan_increment json_integer_second continuation) empty_env
      (PTree.set _index (Vlong (Int64.repr (index + 1))) parameters) memory).
  - exact CLOSED.
  - cbn; tauto.
  - intros; apply certified_set_edge; eapply binary_expression_value with (v := Vlong (Int64.repr index)) (w := Vint Int.one).
    + apply old_expression_value, value_temp; exact POSITION.
    + apply old_expression_value, value_int.
    + change (Some (Vlong (Int64.add (Int64.repr index) (Int64.repr 1))) = Some (Vlong (Int64.repr (index + 1)))).
      unfold Int64.add; f_equal; f_equal; apply Int64.eqm_samerepr.
      apply Int64.eqm_add; apply Int64.eqm_unsigned_repr_l; apply Int64.eqm_refl.
  - eapply gateway_segment_same with (next := State f_host_json_number json_integer_second
      (Kloop2 json_scan_increment json_integer_second continuation) empty_env
      (PTree.set _index (Vlong (Int64.repr (index + 1))) parameters) memory);
      [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_skip_loop1 |].
    unfold json_integer_second at 1; unfold json_integer_cont.
    eapply gateway_segment_same with (next := State f_host_json_number json_integer_test
      (Kseq json_integer_guard (Kloop2 json_scan_increment json_integer_second continuation)) empty_env
      (PTree.set _index (Vlong (Int64.repr (index + 1))) parameters) memory);
      [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_seq |apply gateway_segment_here].
Qed.

Lemma json_integer_break_loop2 ge fn first second continuation environment parameters memory :
  edge ge (State fn Sbreak (Kloop2 first second continuation) environment parameters memory)
    (State fn Sskip continuation environment parameters memory).
Proof. intros; structural_edge. Qed.

Theorem gateway_json_integer_after_test {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) parameters continuation index (more : bool) memory :
  gateway_ambient_closed backend property -> parameters ! _t'4 = Some (Vint (if more then Int.one else Int.zero)) ->
  parameters ! _index = Some (Vlong (Int64.repr index)) ->
  gateway_source_segment backend ge property
    (State f_host_json_number Sskip (json_integer_cont continuation) empty_env parameters memory)
    (if more then State f_host_json_number json_integer_test (json_integer_cont continuation) empty_env
       (PTree.set _index (Vlong (Int64.repr (index + 1))) parameters) memory
     else State f_host_json_number Sskip continuation empty_env parameters memory) property.
Proof.
  intros CLOSED MORE POSITION; unfold json_integer_cont at 1.
  eapply gateway_segment_same with (next := State f_host_json_number json_integer_guard
    (Kloop2 json_scan_increment json_integer_second continuation) empty_env parameters memory);
    [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_skip_seq |].
  destruct more.
  - eapply gateway_segment_same with (next := State f_host_json_number Sskip
      (Kloop2 json_scan_increment json_integer_second continuation) empty_env parameters memory).
    + exact CLOSED.
    + cbn; tauto.
    + intros; eapply certified_if_edge with (v := Vint Int.one) (b := true);
        [apply old_expression_value, value_temp; exact MORE |reflexivity].
    + eapply gateway_segment_same with (next := State f_host_json_number json_number_integer_loop
        continuation empty_env parameters memory).
      * exact CLOSED.
      * cbn; tauto.
      * intros; rewrite json_integer_loop_shape; apply unchanged_store_edge, edge_skip_loop2.
      * apply gateway_json_integer_increment; assumption.
  - eapply gateway_segment_same with (next := State f_host_json_number Sbreak
      (Kloop2 json_scan_increment json_integer_second continuation) empty_env parameters memory).
    + exact CLOSED.
    + cbn; tauto.
    + intros; eapply certified_if_edge with (v := Vint Int.zero) (b := false);
        [apply old_expression_value, value_temp; exact MORE |reflexivity].
    + eapply gateway_segment_same with (next := State f_host_json_number Sskip continuation empty_env parameters memory);
        [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, json_integer_break_loop2 |apply gateway_segment_here].
Qed.

Theorem gateway_json_integer_one {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) parameters continuation object index count byte memory :
  gateway_ambient_closed backend property -> 0 <= index /\ index < count /\ count <= 65536 ->
  parameters ! _bytes = Some (Vptr object Ptrofs.zero) -> parameters ! _index = Some (Vlong (Int64.repr index)) ->
  parameters ! _size = Some (Vlong (Int64.repr count)) ->
  (forall memory world, property memory world -> Mem.loadv Mint8signed memory (Vptr object (Ptrofs.repr index)) =
    Some (Vint (Int.repr (Byte.signed byte)))) ->
  exists next_parameters,
    gateway_source_segment backend ge property
      (State f_host_json_number json_integer_test (json_integer_cont continuation) empty_env parameters memory)
      (if gateway_integer_digit byte then State f_host_json_number json_integer_test (json_integer_cont continuation) empty_env next_parameters memory
       else State f_host_json_number Sskip continuation empty_env next_parameters memory) property /\
    next_parameters ! _bytes = Some (Vptr object Ptrofs.zero) /\
    next_parameters ! _size = Some (Vlong (Int64.repr count)) /\
    next_parameters ! _index = Some (Vlong (Int64.repr (if gateway_integer_digit byte then index + 1 else index))) /\
    (forall identifier, ~ In identifier json_integer_written -> next_parameters ! identifier = parameters ! identifier).
Proof.
  intros CLOSED INDEX BYTES POSITION SIZE CHARACTER.
  destruct (gateway_json_integer_test backend ge property parameters (json_integer_cont continuation) object index count byte memory
    CLOSED INDEX BYTES POSITION SIZE CHARACTER) as (tested & TEST & FRAME & NEXT_BYTES & NEXT_INDEX & NEXT_SIZE & DIGIT).
  destruct (gateway_integer_digit byte) eqn:DECISION.
  - exists (PTree.set _index (Vlong (Int64.repr (index + 1))) tested); split.
    + eapply json_number_segment_compose; [exact TEST |]. apply (gateway_json_integer_after_test backend ge property tested continuation index true memory);
        [exact CLOSED |exact DIGIT |rewrite NEXT_INDEX; exact POSITION].
    + split; [rewrite PTree.gso by discriminate; rewrite NEXT_BYTES; exact BYTES |].
      split; [rewrite PTree.gso by discriminate; rewrite NEXT_SIZE; exact SIZE |]. split; [apply PTree.gss |].
      intros identifier OUTSIDE; rewrite PTree.gso by (intro SAME; apply OUTSIDE; cbn; left; congruence).
      apply FRAME; intro MEMBER; apply OUTSIDE; right; exact MEMBER.
  - exists tested; split.
    + eapply json_number_segment_compose; [exact TEST |]. apply (gateway_json_integer_after_test backend ge property tested continuation index false memory);
        [exact CLOSED |exact DIGIT |rewrite NEXT_INDEX; exact POSITION].
    + split; [rewrite NEXT_BYTES; exact BYTES |]. split; [rewrite NEXT_SIZE; exact SIZE |].
      split; [rewrite NEXT_INDEX; exact POSITION |]. intros identifier OUTSIDE.
      apply FRAME; intro MEMBER; apply OUTSIDE; right; exact MEMBER.
Qed.

Theorem gateway_json_integer_end {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) parameters continuation count memory :
  gateway_ambient_closed backend property -> 0 <= count <= 65536 ->
  parameters ! _index = Some (Vlong (Int64.repr count)) -> parameters ! _size = Some (Vlong (Int64.repr count)) ->
  exists next_parameters,
    gateway_source_segment backend ge property
      (State f_host_json_number json_integer_test (json_integer_cont continuation) empty_env parameters memory)
      (State f_host_json_number Sskip continuation empty_env next_parameters memory) property /\
    (forall identifier, ~ In identifier [_t'3; _t'4] -> next_parameters ! identifier = parameters ! identifier).
Proof.
  intros CLOSED COUNT POSITION SIZE.
  destruct (gateway_json_integer_test_end backend ge property parameters (json_integer_cont continuation) count memory
    CLOSED COUNT POSITION SIZE) as (tested & TEST & FRAME & DIGIT).
  exists tested; split; [|exact FRAME]. eapply json_number_segment_compose; [exact TEST |].
  apply (gateway_json_integer_after_test backend ge property tested continuation count false memory); [exact CLOSED |exact DIGIT |].
  rewrite FRAME; [exact POSITION |cbn; intuition discriminate].
Qed.
