(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual numeric marker tests inspect the same bounded input byte. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayJsonNumberSource GatewayJsonNumberSourceBytes
  GatewayIntegerCanonical GatewayIntegerLoop GatewayIntegerPrefix GatewaySourceSegments GatewaySourceSegmentAutomation GatewayFramedRuntime.
Import ListNotations.
Open Scope Z_scope.

Ltac json_number_source_reduce :=
  cbn -[Int64.eq Int64.ltu Int64.unsigned Int64.repr Int64.add Int.eq Int.signed Int.repr Int.lt
    Byte.eq Byte.signed Z.of_nat];
  repeat rewrite Nat2Z.inj_succ;
  repeat rewrite Int.signed_repr by (change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia);
  change Int64.zero with (Int64.repr 0);
  change Int64.one with (Int64.repr 1);
  try change (Int64.add (Int64.repr 0) (Int64.repr 1)) with (Int64.repr 1);
  repeat first [rewrite gateway_integer_small_equal by
      lia
    |rewrite json_number_word_equal by lia |rewrite json_number_word_less by lia];
  repeat match goal with |- context[Z.eqb (Byte.signed ?character) ?constant] =>
    rewrite <- (gateway_integer_signed_equal character constant) by lia end;
  repeat match goal with H : Byte.eq _ _ = _ |- _ => progress (rewrite H) end;
  repeat match goal with H : Z.eqb _ _ = _ |- _ => progress (rewrite H) end;
  repeat match goal with
  | |- context[Z.eqb ?first ?second] => first [rewrite (proj2 (Z.eqb_eq first second) ltac:(lia)) |
      rewrite (proj2 (Z.eqb_neq first second) ltac:(lia))]
  | |- context[Z.ltb ?first ?second] => first [rewrite (proj2 (Z.ltb_lt first second) ltac:(lia)) |
      rewrite (proj2 (Z.ltb_ge first second) ltac:(lia))]
  end;
  repeat rewrite Int.eq_true;
  try rewrite (Int.eq_false Int.one Int.zero Int.one_not_zero);
  reflexivity.

Inductive json_marker_test := json_fraction_marker | json_exponent_marker | json_exponent_sign.
Definition json_marker_source kind := match kind with
  | json_fraction_marker => json_number_first json_number_fraction
  | json_exponent_marker => json_number_first json_number_exponent
  | json_exponent_sign => json_number_first (json_number_first json_number_exponent_after_marker)
  end.
Definition json_marker_flag kind := match kind with
  | json_fraction_marker => _t'8 | json_exponent_marker => _t'12 | json_exponent_sign => _t'9 end.
Definition json_marker_written kind := match kind with
  | json_fraction_marker => [_t'8; _t'32]
  | json_exponent_marker => [_t'12; _t'28; _t'29]
  | json_exponent_sign => [_t'9; _t'26; _t'27] end.
Definition json_marker_matches kind byte := match kind with
  | json_fraction_marker => Byte.eq byte (Byte.repr 46)
  | json_exponent_marker => Byte.eq byte (Byte.repr 101) || Byte.eq byte (Byte.repr 69)
  | json_exponent_sign => Byte.eq byte (Byte.repr 43) || Byte.eq byte (Byte.repr 45) end.

Theorem gateway_json_number_marker_test {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) kind parameters continuation object index count byte memory :
  gateway_ambient_closed backend property -> 0 <= index /\ index < count /\ count <= 65536 ->
  parameters ! _bytes = Some (Vptr object Ptrofs.zero) -> parameters ! _index = Some (Vlong (Int64.repr index)) ->
  parameters ! _size = Some (Vlong (Int64.repr count)) ->
  (forall memory world, property memory world -> Mem.loadv Mint8signed memory (Vptr object (Ptrofs.repr index)) =
    Some (Vint (Int.repr (Byte.signed byte)))) ->
  exists changed,
    gateway_source_segment backend ge property
      (State f_host_json_number (json_marker_source kind) continuation empty_env parameters memory)
      (State f_host_json_number Sskip continuation empty_env changed memory) property /\
    changed ! (json_marker_flag kind) = Some (Vint (if json_marker_matches kind byte then Int.one else Int.zero)) /\
    (forall identifier, ~ In identifier (json_marker_written kind) -> changed ! identifier = parameters ! identifier).
Proof.
  intros CLOSED INDEX BYTES POSITION SIZE LOAD.
  pose proof (gateway_integer_signed_range byte) as BYTE_RANGE.
  destruct kind.
  - destruct (Byte.eq byte (Byte.repr 46)) eqn:FRACTION.
    all: eexists; split.
    all: try (unfold json_marker_source;
      gateway_segment_dynamic CLOSED
        ltac:(fun _ => eapply gateway_json_number_character with (index := index) (byte := byte) (object := object);
          [lia |repeat rewrite PTree.gso by discriminate; exact BYTES |repeat rewrite PTree.gso by discriminate; exact POSITION |
            eapply LOAD; eassumption]) ltac:(fun _ => json_number_source_reduce)).
    all: split; [cbn [json_marker_flag json_marker_matches]; rewrite FRACTION; apply PTree.gss |
      intros identifier OUTSIDE; repeat rewrite PTree.gso by
        (intro SAME; apply OUTSIDE; subst identifier; cbn; auto); reflexivity].
  - destruct (Byte.eq byte (Byte.repr 101)) eqn:LOWER; destruct (Byte.eq byte (Byte.repr 69)) eqn:UPPER.
    all: eexists; split.
    all: try (unfold json_marker_source;
      gateway_segment_dynamic CLOSED
        ltac:(fun _ => eapply gateway_json_number_character with (index := index) (byte := byte) (object := object);
          [lia |repeat rewrite PTree.gso by discriminate; exact BYTES |repeat rewrite PTree.gso by discriminate; exact POSITION |
            eapply LOAD; eassumption]) ltac:(fun _ => json_number_source_reduce)).
    all: split; [cbn [json_marker_flag json_marker_matches]; rewrite LOWER, UPPER; cbn; apply PTree.gss |
      intros identifier OUTSIDE; repeat rewrite PTree.gso by
        (intro SAME; apply OUTSIDE; subst identifier; cbn; auto); reflexivity].
  - destruct (Byte.eq byte (Byte.repr 43)) eqn:PLUS; destruct (Byte.eq byte (Byte.repr 45)) eqn:MINUS.
    all: eexists; split.
    all: try (unfold json_marker_source;
      gateway_segment_dynamic CLOSED
        ltac:(fun _ => eapply gateway_json_number_character with (index := index) (byte := byte) (object := object);
          [lia |repeat rewrite PTree.gso by discriminate; exact BYTES |repeat rewrite PTree.gso by discriminate; exact POSITION |
            eapply LOAD; eassumption]) ltac:(fun _ => json_number_source_reduce)).
    all: split; [cbn [json_marker_flag json_marker_matches]; rewrite PLUS, MINUS; cbn; apply PTree.gss |
      intros identifier OUTSIDE; repeat rewrite PTree.gso by
        (intro SAME; apply OUTSIDE; subst identifier; cbn; auto); reflexivity].
Qed.

Theorem gateway_json_number_marker_end {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) kind parameters continuation count memory :
  gateway_ambient_closed backend property -> 0 <= count <= 65536 ->
  parameters ! _index = Some (Vlong (Int64.repr count)) -> parameters ! _size = Some (Vlong (Int64.repr count)) ->
  exists changed,
    gateway_source_segment backend ge property
      (State f_host_json_number (json_marker_source kind) continuation empty_env parameters memory)
      (State f_host_json_number Sskip continuation empty_env changed memory) property /\
    changed ! (json_marker_flag kind) = Some (Vint Int.zero) /\
    (forall identifier, identifier <> json_marker_flag kind -> changed ! identifier = parameters ! identifier).
Proof.
  intros CLOSED COUNT POSITION SIZE; destruct kind; eexists; split.
  all: try (unfold json_marker_source; gateway_segment_dynamic CLOSED ltac:(fun _ => fail) ltac:(fun _ => json_number_source_reduce)).
  all: split; [apply PTree.gss |intros identifier OUTSIDE; apply PTree.gso; cbn [json_marker_flag] in OUTSIDE; congruence].
Qed.
