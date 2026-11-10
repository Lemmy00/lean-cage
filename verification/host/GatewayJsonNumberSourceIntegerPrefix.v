(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual zero/nonzero integer guard selects the exact decimal prefix. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayJsonNumberSource GatewayJsonNumberSourceBytes
  GatewayJsonNumberSourceTests GatewayJsonNumberSourceScans GatewayJsonNumberSourceInteger GatewayJsonNumberSourceIntegerFold
  GatewayJsonNumberSourceFraction GatewayJsonNumberLexical GatewayIntegerCanonical GatewayIntegerLoop GatewayIntegerPrefix
  GatewaySourceSegments GatewaySourceSegmentAutomation GatewayFramedRuntime GatewayFailurePaths GatewaySourceCuts.
Import ListNotations.
Open Scope Z_scope.

Definition json_number_take_integer bytes : option (list Byte.int * list Byte.int) :=
  match bytes with
  | [] => None
  | first :: rest => if Byte.eq first (Byte.repr 48) then Some ([first], rest)
    else if (49 <=? Byte.unsigned first) && (Byte.unsigned first <=? 57) then
      let (digits, tail) := json_number_take_digits rest in Some (first :: digits, tail)
    else None end.
Definition json_integer_prefix_written := [_t'33; _t'36; _t'37; _t'2].
Definition json_integer_all_written := json_integer_prefix_written ++ json_integer_written.

Lemma json_number_integer_after_split sign bytes : json_number_integer_after sign bytes =
  match json_number_take_integer bytes with Some (integer, tail) => json_number_finish sign integer tail | None => None end.
Proof.
  destruct bytes as [|first rest]; [reflexivity |]. cbn [json_number_integer_after json_number_take_integer].
  destruct (Byte.eq first (Byte.repr 48)); [reflexivity |].
  destruct ((49 <=? Byte.unsigned first) && (Byte.unsigned first <=? 57)); [|reflexivity].
  destruct (json_number_take_digits rest); reflexivity.
Qed.

Theorem gateway_json_number_integer_zero {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) parameters continuation object index byte memory :
  gateway_ambient_closed backend property -> 0 <= index < 65536 -> Byte.eq byte (Byte.repr 48) = true ->
  parameters ! _bytes = Some (Vptr object Ptrofs.zero) -> parameters ! _index = Some (Vlong (Int64.repr index)) ->
  (forall memory world, property memory world -> Mem.loadv Mint8signed memory (Vptr object (Ptrofs.repr index)) =
    Some (Vint (Int.repr (Byte.signed byte)))) ->
  exists changed,
    gateway_source_segment backend ge property
      (State f_host_json_number json_number_integer continuation empty_env parameters memory)
      (State f_host_json_number Sskip continuation empty_env changed memory) property /\
    changed ! _index = Some (Vlong (Int64.repr (index + 1))) /\
    (forall identifier, ~ In identifier [_t'33; _index] -> changed ! identifier = parameters ! identifier).
Proof.
  intros CLOSED INDEX ZERO BYTES POSITION LOAD; pose proof (gateway_integer_signed_range byte) as BYTE_RANGE.
  eexists; split.
  - gateway_segment_dynamic CLOSED
      ltac:(fun _ => eapply gateway_json_number_character with (index := index) (byte := byte) (object := object);
        [lia |repeat rewrite PTree.gso by discriminate; exact BYTES |repeat rewrite PTree.gso by discriminate; exact POSITION |
          eapply LOAD; eassumption]) ltac:(fun _ => json_number_source_reduce).
  - split.
    + repeat rewrite PTree.gso by discriminate; rewrite PTree.gss.
      change (Some (Vlong (Int64.add (Int64.repr index) (Int64.repr 1))) = Some (Vlong (Int64.repr (index + 1)))).
      rewrite json_number_word_increment; reflexivity.
    + intros identifier OUTSIDE; repeat rewrite PTree.gso by
        (intro SAME; apply OUTSIDE; subst identifier; cbn; auto); reflexivity.
Qed.

Theorem gateway_json_number_integer_nonzero {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) parameters continuation object index byte memory :
  gateway_ambient_closed backend property -> 0 <= index < 65536 -> Byte.eq byte (Byte.repr 48) = false ->
  49 <= Byte.signed byte <= 57 ->
  parameters ! _bytes = Some (Vptr object Ptrofs.zero) -> parameters ! _index = Some (Vlong (Int64.repr index)) ->
  (forall memory world, property memory world -> Mem.loadv Mint8signed memory (Vptr object (Ptrofs.repr index)) =
    Some (Vint (Int.repr (Byte.signed byte)))) ->
  exists changed,
    gateway_source_segment backend ge property
      (State f_host_json_number json_number_integer continuation empty_env parameters memory)
      (State f_host_json_number json_number_integer_loop continuation empty_env changed memory) property /\
    (forall identifier, ~ In identifier json_integer_prefix_written -> changed ! identifier = parameters ! identifier).
Proof.
  intros CLOSED INDEX ZERO DIGIT BYTES POSITION LOAD; pose proof (gateway_integer_signed_range byte) as BYTE_RANGE.
  eexists; split.
  - gateway_segment_dynamic CLOSED
      ltac:(fun _ => eapply gateway_json_number_character with (index := index) (byte := byte) (object := object);
        [lia |repeat rewrite PTree.gso by discriminate; exact BYTES |repeat rewrite PTree.gso by discriminate; exact POSITION |
          eapply LOAD; eassumption])
      ltac:(fun _ => cbn -[Int64.eq Int64.repr Int64.add Int.eq Int.signed Int.repr Int.lt Byte.eq Byte.signed];
        try unfold Int.lt;
        repeat rewrite Int.signed_repr by (change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia);
        repeat first [rewrite zlt_true by lia |rewrite zlt_false by lia]; json_number_source_reduce).
  - intros identifier OUTSIDE; repeat rewrite PTree.gso by
      (intro SAME; apply OUTSIDE; subst identifier; cbn; auto 8); reflexivity.
Qed.

Theorem gateway_json_number_integer_invalid {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) parameters continuation object index byte memory :
  gateway_ambient_closed backend property -> call_cont continuation = Kstop ->
  0 <= index < 65536 -> Byte.eq byte (Byte.repr 48) = false ->
  (Byte.signed byte < 49 \/ 57 < Byte.signed byte) ->
  parameters ! _bytes = Some (Vptr object Ptrofs.zero) -> parameters ! _index = Some (Vlong (Int64.repr index)) ->
  (forall memory world, property memory world -> Mem.loadv Mint8signed memory (Vptr object (Ptrofs.repr index)) =
    Some (Vint (Int.repr (Byte.signed byte)))) ->
  gateway_failure_when backend ge property
    (State f_host_json_number json_number_integer continuation empty_env parameters memory).
Proof.
  intros CLOSED STOP INDEX ZERO INVALID BYTES POSITION LOAD; pose proof (gateway_integer_signed_range byte) as BYTE_RANGE.
  destruct INVALID as [LOW |HIGH]; assert (SEGMENT : exists changed, gateway_source_segment backend ge property
    (State f_host_json_number json_number_integer continuation empty_env parameters memory)
    (State f_host_json_number (Sgoto _invalid) (Kseq json_number_integer_loop continuation) empty_env changed memory) property).
  all: try (eexists; gateway_segment_dynamic CLOSED
    ltac:(fun _ => eapply gateway_json_number_character with (index := index) (byte := byte) (object := object);
      [lia |repeat rewrite PTree.gso by discriminate; exact BYTES |repeat rewrite PTree.gso by discriminate; exact POSITION |
        eapply LOAD; eassumption])
    ltac:(fun _ => cbn -[Int64.eq Int64.repr Int64.add Int.eq Int.signed Int.repr Int.lt Byte.eq Byte.signed];
      try unfold Int.lt;
      repeat rewrite Int.signed_repr by (change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia);
      repeat first [rewrite zlt_true by lia |rewrite zlt_false by lia]; json_number_source_reduce)).
  all: destruct SEGMENT as [changed SEGMENT]; eapply json_number_segment_denial;
    [exact SEGMENT |apply gateway_json_number_invalid_denied; exact STOP].
Qed.

Lemma json_number_nonzero_signed byte :
  (49 <= Byte.signed byte <= 57) <-> (49 <= Byte.unsigned byte <= 57).
Proof.
  unfold Byte.signed; pose proof (Byte.unsigned_range byte) as RANGE.
  change Byte.half_modulus with 128; change Byte.modulus with 256 in *.
  destruct (zlt (Byte.unsigned byte) 128); split; lia.
Qed.

Theorem gateway_json_number_integer_source {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) parameters continuation object index count first rest memory :
  gateway_ambient_closed backend property -> call_cont continuation = Kstop ->
  0 <= index -> index + Z.of_nat (length (first :: rest)) = count -> count <= 65536 ->
  parameters ! _bytes = Some (Vptr object Ptrofs.zero) -> parameters ! _index = Some (Vlong (Int64.repr index)) ->
  parameters ! _size = Some (Vlong (Int64.repr count)) ->
  (forall offset byte, nth_error (first :: rest) offset = Some byte -> forall memory world, property memory world ->
    Mem.loadv Mint8signed memory (Vptr object (Ptrofs.repr (index + Z.of_nat offset))) = Some (Vint (Int.repr (Byte.signed byte)))) ->
  match json_number_take_integer (first :: rest) with
  | None => gateway_failure_when backend ge property
      (State f_host_json_number json_number_integer continuation empty_env parameters memory)
  | Some (fragment, tail) => exists changed,
      gateway_source_segment backend ge property
        (State f_host_json_number json_number_integer continuation empty_env parameters memory)
        (State f_host_json_number Sskip continuation empty_env changed memory) property /\
      changed ! _bytes = Some (Vptr object Ptrofs.zero) /\
      changed ! _size = Some (Vlong (Int64.repr count)) /\
      changed ! _index = Some (Vlong (Int64.repr (index + Z.of_nat (length fragment)))) /\
      (forall identifier, ~ In identifier json_integer_all_written -> changed ! identifier = parameters ! identifier)
  end.
Proof.
  intros CLOSED STOP INDEX LENGTH BOUND BYTES POSITION SIZE LOADS.
  assert (RANGE : 0 <= index < count /\ index < 65536).
  { change (index + Z.of_nat (S (length rest)) = count) in LENGTH; rewrite Nat2Z.inj_succ in LENGTH; lia. }
  assert (TAIL_LENGTH : index + 1 + Z.of_nat (length rest) = count).
  { change (index + Z.of_nat (S (length rest)) = count) in LENGTH; rewrite Nat2Z.inj_succ in LENGTH; lia. }
  assert (FIRST : forall memory world, property memory world ->
    Mem.loadv Mint8signed memory (Vptr object (Ptrofs.repr index)) = Some (Vint (Int.repr (Byte.signed first)))).
  { intros changed owner GOOD; specialize (LOADS 0%nat first eq_refl changed owner GOOD); cbn in LOADS;
      rewrite Z.add_0_r in LOADS; exact LOADS. }
  cbn [json_number_take_integer]; destruct (Byte.eq first (Byte.repr 48)) eqn:ZERO.
  - destruct (gateway_json_number_integer_zero backend ge property parameters continuation object index first memory
      CLOSED ltac:(lia) ZERO BYTES POSITION FIRST) as (changed & SEGMENT & NEXT_INDEX & FRAME).
    exists changed; split; [exact SEGMENT |]. split.
    + rewrite FRAME; [exact BYTES |cbn; intuition discriminate].
    + split; [rewrite FRAME; [exact SIZE |cbn; intuition discriminate] |]. split; [exact NEXT_INDEX |].
      intros identifier OUTSIDE; apply FRAME; intro MEMBER; apply OUTSIDE; unfold json_integer_all_written;
        apply in_or_app; cbn in MEMBER; destruct MEMBER as [SAME |[SAME |EMPTY]];
        [left; subst identifier; cbn; auto |right; subst identifier; cbn; auto |contradiction].
  - destruct ((49 <=? Byte.unsigned first) && (Byte.unsigned first <=? 57)) eqn:LEADING.
    + assert (SIGNED : 49 <= Byte.signed first <= 57).
      { apply json_number_nonzero_signed; apply andb_true_iff in LEADING; destruct LEADING;
          apply Z.leb_le in H; apply Z.leb_le in H0; lia. }
      destruct (gateway_json_number_integer_nonzero backend ge property parameters continuation object index first memory
        CLOSED ltac:(lia) ZERO SIGNED BYTES POSITION FIRST) as (entered & PREFIX & FRAME).
      pose proof (gateway_json_number_integer_digits backend ge property continuation object count memory rest entered index
        CLOSED ltac:(lia) TAIL_LENGTH
        ltac:(rewrite FRAME; [exact BYTES |cbn; intuition discriminate])
        ltac:(rewrite FRAME; [exact POSITION |cbn; intuition discriminate])
        ltac:(rewrite FRAME; [exact SIZE |cbn; intuition discriminate])
        ltac:(intros offset selected SELECTED changed owner GOOD; specialize (LOADS (S offset) selected SELECTED changed owner GOOD);
          rewrite Nat2Z.inj_succ in LOADS; replace (index + Z.succ (Z.of_nat offset)) with (index + 1 + Z.of_nat offset) in LOADS by lia;
          exact LOADS)) as SCAN.
      destruct (json_number_take_digits rest) as [digits tail] eqn:TAKE; cbn in SCAN |- *.
      destruct SCAN as (changed & SUFFIX & NEXT_BYTES & NEXT_SIZE & NEXT_INDEX & SCAN_FRAME).
      exists changed; split; [eapply json_number_segment_compose; [exact PREFIX |exact SUFFIX] |].
      split; [exact NEXT_BYTES |]. split; [exact NEXT_SIZE |]. split.
      * change (changed ! _index = Some (Vlong (Int64.repr (index + Z.of_nat (S (length digits)))))); rewrite Nat2Z.inj_succ;
          replace (index + Z.succ (Z.of_nat (length digits))) with (index + 1 + Z.of_nat (length digits)) by lia; exact NEXT_INDEX.
      * intros identifier OUTSIDE; rewrite SCAN_FRAME.
        -- apply FRAME; intro MEMBER; apply OUTSIDE; cbn in MEMBER |- *; intuition.
        -- intro MEMBER; apply OUTSIDE; cbn in MEMBER |- *; intuition.
    + assert (INVALID : Byte.signed first < 49 \/ 57 < Byte.signed first).
      { destruct (Z_le_dec 49 (Byte.signed first)); [|left; lia].
        destruct (Z_le_dec (Byte.signed first) 57); [|right; lia].
        assert (UNSIGNED : 49 <= Byte.unsigned first <= 57) by (apply json_number_nonzero_signed; lia).
        assert (TRUE : ((49 <=? Byte.unsigned first) && (Byte.unsigned first <=? 57)) = true) by
          (apply andb_true_iff; split; apply Z.leb_le; lia); congruence. }
      exact (gateway_json_number_integer_invalid backend ge property parameters continuation object index first memory
        CLOSED STOP ltac:(lia) ZERO INVALID BYTES POSITION FIRST).
Qed.
