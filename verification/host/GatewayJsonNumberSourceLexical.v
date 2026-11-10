(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The entire actual numeric lexer reaches a constructor only for the same valid complete wire number. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayValue GatewayJsonNumberSource GatewayJsonNumberSourceBytes
  GatewayJsonNumberSourceEntry GatewayJsonNumberSourceScans GatewayJsonNumberSourceIntegerPrefix
  GatewayJsonNumberSourceFraction GatewayJsonNumberSourceExponent GatewayJsonNumberSourcePhases
  GatewayJsonNumberLexical GatewayJsonNumberLexicalSlices GatewayIntegerPrefix
  GatewaySourceSegments GatewayFramedRuntime GatewayFailurePaths GatewaySourceCuts.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_actual_json_number_lexical_source {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) parameters object bytes memory :
  gateway_ambient_closed backend property -> Z.of_nat (length bytes) <= 65536 ->
  parameters ! _bytes = Some (Vptr object Ptrofs.zero) ->
  parameters ! _size = Some (Vlong (Int64.repr (Z.of_nat (length bytes)))) ->
  (forall offset byte, nth_error bytes offset = Some byte -> forall memory world, property memory world ->
    Mem.loadv Mint8signed memory (Vptr object (Ptrofs.repr (Z.of_nat offset))) = Some (Vint (Int.repr (Byte.signed byte)))) ->
  gateway_failure_when backend ge property
    (State f_host_json_number (fn_body f_host_json_number) Kstop empty_env parameters memory) \/
  exists parts changed,
    json_number_lexical bytes = Some parts /\
    let integer_end := gateway_integer_start bytes + Z.of_nat (length (json_parts_integer parts)) in
    0 <= integer_end <= Z.of_nat (length bytes) /\
    gateway_source_segment backend ge property
      (State f_host_json_number (fn_body f_host_json_number) Kstop empty_env parameters memory)
      (json_lexical_constructor integer_end (Z.of_nat (length bytes)) changed memory) property /\
    changed ! _bytes = Some (Vptr object Ptrofs.zero) /\
    changed ! _size = Some (Vlong (Int64.repr (Z.of_nat (length bytes)))) /\
    changed ! _index = Some (Vlong (Int64.repr (Z.of_nat (length bytes)))) /\
    changed ! _integer_end = Some (Vlong (Int64.repr integer_end)) /\
    changed ! _digits = Some (Vlong (Int64.repr (gateway_integer_start bytes))) /\
    changed ! _negative = Some (Vint (if gateway_integer_negative bytes then Int.one else Int.zero)) /\
    json_parts_sign parts = json_number_sign bytes.
Proof.
  intros CLOSED BOUND BYTES SIZE LOADS.
  pose proof (gateway_json_number_entry_source backend ge property parameters object bytes memory CLOSED BOUND BYTES SIZE LOADS) as ENTRY.
  destruct (json_number_unsigned_source bytes) as [UNSIGNED_SOURCE START_LENGTH].
  destruct (gateway_integer_digits bytes) as [|first rest] eqn:UNSIGNED; [left; exact ENTRY |].
  destruct ENTRY as (entered & ENTRY & ENTER_BYTES & ENTER_SIZE & ENTER_INDEX & ENTER_DIGITS & ENTER_NEGATIVE & ENTER_FRAME).
  set (start := gateway_integer_start bytes) in *.
  set (count := Z.of_nat (length bytes)) in *.
  assert (INITIAL_LENGTH : start + Z.of_nat (length (first :: rest)) = count).
  { rewrite START_LENGTH; exact (json_number_slice_length _ _ _ UNSIGNED_SOURCE). }
  pose proof (json_number_slice_loads property object bytes (json_number_sign_prefix bytes) (first :: rest) UNSIGNED_SOURCE LOADS) as INITIAL_LOADS.
  rewrite <- START_LENGTH in INITIAL_LOADS.
  pose proof (gateway_json_number_integer_source backend ge property entered json_number_integer_cont object start count first rest memory
    CLOSED eq_refl ltac:(rewrite START_LENGTH; lia) INITIAL_LENGTH BOUND ENTER_BYTES ENTER_INDEX ENTER_SIZE INITIAL_LOADS) as INTEGER.
  destruct (json_number_take_integer (first :: rest)) as [[integer tail_integer] |] eqn:TAKE_INTEGER.
  2: { left; eapply json_number_segment_failure_when; [exact ENTRY |exact INTEGER]. }
  destruct INTEGER as (integral & INTEGER & INTEGER_BYTES & INTEGER_SIZE & INTEGER_INDEX & INTEGER_FRAME).
  pose proof (json_number_integer_slice _ _ _ TAKE_INTEGER) as INTEGER_SLICE.
  set (integer_prefix := json_number_sign_prefix bytes ++ integer).
  set (integer_end := start + Z.of_nat (length integer)).
  assert (INTEGER_SOURCE : bytes = integer_prefix ++ tail_integer).
  { unfold integer_prefix; etransitivity; [exact UNSIGNED_SOURCE |]; rewrite INTEGER_SLICE; apply app_assoc. }
  assert (INTEGER_LENGTH : integer_end = Z.of_nat (length integer_prefix)).
  { unfold integer_end, integer_prefix; rewrite length_app, Nat2Z.inj_add, START_LENGTH; reflexivity. }
  assert (INTEGER_REST : integer_end + Z.of_nat (length tail_integer) = count).
  { rewrite INTEGER_LENGTH; exact (json_number_slice_length _ _ _ INTEGER_SOURCE). }
  assert (INTEGER_RANGE : 0 <= integer_end <= count) by (rewrite INTEGER_LENGTH in *; lia).
  assert (THROUGH_INTEGER : gateway_source_segment backend ge property
    (State f_host_json_number (fn_body f_host_json_number) Kstop empty_env parameters memory)
    (State f_host_json_number Sskip json_number_integer_cont empty_env integral memory) property).
  { eapply json_number_segment_compose; [exact ENTRY |exact INTEGER]. }
  pose proof (gateway_json_number_to_fraction backend ge property integral integer_end memory CLOSED INTEGER_INDEX) as TO_FRACTION.
  set (fraction_parameters := PTree.set _integer_end (Vlong (Int64.repr integer_end)) integral).
  pose proof (json_number_slice_loads property object bytes integer_prefix tail_integer INTEGER_SOURCE LOADS) as FRACTION_LOADS.
  rewrite <- INTEGER_LENGTH in FRACTION_LOADS.
  pose proof (gateway_json_number_fraction_source backend ge property fraction_parameters json_lexical_fraction_cont object integer_end count tail_integer memory
    CLOSED eq_refl ltac:(lia) INTEGER_REST BOUND
    ltac:(unfold fraction_parameters; rewrite PTree.gso by discriminate; exact INTEGER_BYTES)
    ltac:(unfold fraction_parameters; rewrite PTree.gso by discriminate; exact INTEGER_INDEX)
    ltac:(unfold fraction_parameters; rewrite PTree.gso by discriminate; exact INTEGER_SIZE) FRACTION_LOADS) as FRACTION.
  destruct (json_number_take_fraction tail_integer) as [[fraction tail_fraction] |] eqn:TAKE_FRACTION.
  2: { left; eapply json_number_segment_failure_when; [exact THROUGH_INTEGER |].
    eapply json_number_segment_failure_when; [exact TO_FRACTION |exact FRACTION]. }
  destruct FRACTION as (fractional & FRACTION & FRACTION_BYTES & FRACTION_SIZE & FRACTION_INDEX & FRACTION_FRAME).
  destruct (json_number_take_fraction_sound _ _ _ TAKE_FRACTION) as [FRACTION_SLICE FRACTION_VALID].
  set (fraction_prefix := integer_prefix ++ fraction).
  set (fraction_end := integer_end + Z.of_nat (length fraction)).
  assert (FRACTION_SOURCE : bytes = fraction_prefix ++ tail_fraction).
  { unfold fraction_prefix; etransitivity; [exact INTEGER_SOURCE |]; rewrite FRACTION_SLICE; apply app_assoc. }
  assert (FRACTION_LENGTH : fraction_end = Z.of_nat (length fraction_prefix)).
  { unfold fraction_end, fraction_prefix; rewrite length_app, Nat2Z.inj_add, INTEGER_LENGTH; reflexivity. }
  assert (FRACTION_REST : fraction_end + Z.of_nat (length tail_fraction) = count).
  { rewrite FRACTION_LENGTH; exact (json_number_slice_length _ _ _ FRACTION_SOURCE). }
  assert (FRACTION_RANGE : 0 <= fraction_end <= count) by (rewrite FRACTION_LENGTH in *; lia).
  assert (THROUGH_FRACTION : gateway_source_segment backend ge property
    (State f_host_json_number (fn_body f_host_json_number) Kstop empty_env parameters memory)
    (State f_host_json_number Sskip json_lexical_fraction_cont empty_env fractional memory) property).
  { eapply json_number_segment_compose; [exact THROUGH_INTEGER |]. eapply json_number_segment_compose; [exact TO_FRACTION |exact FRACTION]. }
  pose proof (gateway_json_number_to_exponent backend ge property fractional memory CLOSED) as TO_EXPONENT.
  pose proof (json_number_slice_loads property object bytes fraction_prefix tail_fraction FRACTION_SOURCE LOADS) as EXPONENT_LOADS.
  rewrite <- FRACTION_LENGTH in EXPONENT_LOADS.
  pose proof (gateway_json_number_exponent_source backend ge property fractional json_lexical_exponent_cont object fraction_end count tail_fraction memory
    CLOSED eq_refl ltac:(lia) FRACTION_REST BOUND FRACTION_BYTES FRACTION_INDEX FRACTION_SIZE EXPONENT_LOADS) as EXPONENT.
  destruct (json_number_take_exponent tail_fraction) as [[exponent tail_exponent] |] eqn:TAKE_EXPONENT.
  2: { left; eapply json_number_segment_failure_when; [exact THROUGH_FRACTION |].
    eapply json_number_segment_failure_when; [exact TO_EXPONENT |exact EXPONENT]. }
  destruct EXPONENT as (final & EXPONENT & FINAL_BYTES & FINAL_SIZE & FINAL_INDEX & EXPONENT_FRAME).
  destruct (json_number_take_exponent_sound _ _ _ TAKE_EXPONENT) as [EXPONENT_SLICE EXPONENT_VALID].
  set (final_prefix := fraction_prefix ++ exponent).
  set (finish := fraction_end + Z.of_nat (length exponent)).
  assert (FINAL_SOURCE : bytes = final_prefix ++ tail_exponent).
  { unfold final_prefix; etransitivity; [exact FRACTION_SOURCE |]; rewrite EXPONENT_SLICE; apply app_assoc. }
  assert (FINAL_LENGTH : finish = Z.of_nat (length final_prefix)).
  { unfold finish, final_prefix; rewrite length_app, Nat2Z.inj_add, FRACTION_LENGTH; reflexivity. }
  assert (FINAL_REST : finish + Z.of_nat (length tail_exponent) = count).
  { rewrite FINAL_LENGTH; exact (json_number_slice_length _ _ _ FINAL_SOURCE). }
  assert (FINAL_RANGE : 0 <= finish <= count) by (rewrite FINAL_LENGTH in *; lia).
  assert (FINAL_END : final ! _integer_end = Some (Vlong (Int64.repr integer_end))).
  { rewrite EXPONENT_FRAME, FRACTION_FRAME; [unfold fraction_parameters; apply PTree.gss | |]; cbn; intuition discriminate. }
  assert (FINAL_DIGITS : final ! _digits = Some (Vlong (Int64.repr start))).
  { rewrite EXPONENT_FRAME, FRACTION_FRAME; [unfold fraction_parameters; rewrite PTree.gso by discriminate; rewrite INTEGER_FRAME;
      [exact ENTER_DIGITS |] | |]; cbn; intuition discriminate. }
  assert (FINAL_NEGATIVE : final ! _negative = Some (Vint (if gateway_integer_negative bytes then Int.one else Int.zero))).
  { rewrite EXPONENT_FRAME, FRACTION_FRAME; [unfold fraction_parameters; rewrite PTree.gso by discriminate; rewrite INTEGER_FRAME;
      [exact ENTER_NEGATIVE |] | |]; cbn; intuition discriminate. }
  assert (THROUGH_EXPONENT : gateway_source_segment backend ge property
    (State f_host_json_number (fn_body f_host_json_number) Kstop empty_env parameters memory)
    (State f_host_json_number Sskip json_lexical_exponent_cont empty_env final memory) property).
  { eapply json_number_segment_compose; [exact THROUGH_FRACTION |]. eapply json_number_segment_compose; [exact TO_EXPONENT |exact EXPONENT]. }
  pose proof (gateway_json_number_constructor_select backend ge property final finish integer_end count memory CLOSED
    ltac:(lia) ltac:(lia) ltac:(lia) FINAL_INDEX FINAL_END FINAL_SIZE) as CONSTRUCTOR.
  fold fraction_end in FINAL_INDEX; fold finish in FINAL_INDEX.
  destruct tail_exponent as [|leftover tail_exponent].
  - cbn in FINAL_REST; rewrite Z.add_0_r in FINAL_REST; rewrite FINAL_REST in CONSTRUCTOR, FINAL_INDEX.
    rewrite Z.eqb_refl in CONSTRUCTOR.
    right; exists {| json_parts_sign := json_number_sign bytes; json_parts_integer := integer;
      json_parts_fraction := fraction; json_parts_exponent := exponent |}, final; split.
    + rewrite json_number_lexical_split, UNSIGNED, TAKE_INTEGER; unfold json_number_finish;
        rewrite TAKE_FRACTION, TAKE_EXPONENT; reflexivity.
    + cbn [json_parts_integer json_parts_sign]. fold start; fold integer_end; fold count.
      split; [exact INTEGER_RANGE |]. split.
      * eapply json_number_segment_compose; [exact THROUGH_EXPONENT |exact CONSTRUCTOR].
      * split; [exact FINAL_BYTES |]. split; [exact FINAL_SIZE |]. split; [exact FINAL_INDEX |].
        split; [exact FINAL_END |]. split; [exact FINAL_DIGITS |]. split; [exact FINAL_NEGATIVE |reflexivity].
  - assert (INCOMPLETE : (finish =? count) = false).
    { apply Z.eqb_neq; change (finish + Z.of_nat (S (length tail_exponent)) = count) in FINAL_REST;
        rewrite Nat2Z.inj_succ in FINAL_REST; lia. }
    rewrite INCOMPLETE in CONSTRUCTOR; left.
    eapply json_number_segment_denial; [eapply json_number_segment_compose; [exact THROUGH_EXPONENT |exact CONSTRUCTOR] |].
    apply gateway_json_number_invalid_denied; reflexivity.
Qed.
