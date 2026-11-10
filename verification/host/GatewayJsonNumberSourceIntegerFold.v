(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual numeric loops stop at the exact first nondigit or bounded end. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayJsonNumberSource GatewayMachine GatewayJsonNumberSourceInteger GatewayJsonNumberLexical
  GatewayJsonNumberSourceScans GatewayIntegerCanonical GatewaySourceSegments GatewayFramedRuntime.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_json_integer_test_digits {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) continuation object count memory :
  gateway_ambient_closed backend property -> 0 <= count <= 65536 ->
  forall remaining parameters index, 0 <= index -> index + Z.of_nat (length remaining) = count ->
  parameters ! _bytes = Some (Vptr object Ptrofs.zero) -> parameters ! _index = Some (Vlong (Int64.repr index)) ->
  parameters ! _size = Some (Vlong (Int64.repr count)) ->
  (forall offset byte, nth_error remaining offset = Some byte -> forall memory world, property memory world ->
    Mem.loadv Mint8signed memory (Vptr object (Ptrofs.repr (index + Z.of_nat offset))) = Some (Vint (Int.repr (Byte.signed byte)))) ->
  let (digits, tail) := json_number_take_digits remaining in
  exists final_parameters,
    gateway_source_segment backend ge property
      (State f_host_json_number json_integer_test (json_integer_cont continuation) empty_env parameters memory)
      (State f_host_json_number Sskip continuation empty_env final_parameters memory) property /\
    final_parameters ! _bytes = Some (Vptr object Ptrofs.zero) /\
    final_parameters ! _size = Some (Vlong (Int64.repr count)) /\
    final_parameters ! _index = Some (Vlong (Int64.repr (index + Z.of_nat (length digits)))) /\
    (forall identifier, ~ In identifier json_integer_written -> final_parameters ! identifier = parameters ! identifier).
Proof.
  intros CLOSED COUNT remaining; induction remaining as [|byte rest IH];
    intros parameters index INDEX LENGTH BYTES POSITION SIZE LOADS.
  - cbn in LENGTH; rewrite Z.add_0_r in LENGTH; subst index; cbn [json_number_take_digits].
    destruct (gateway_json_integer_end backend ge property parameters continuation count memory CLOSED COUNT POSITION SIZE)
      as (final & SEGMENT & FRAME).
    exists final; split; [exact SEGMENT |]. split.
    + rewrite FRAME; [exact BYTES |cbn; intuition discriminate].
    + split; [rewrite FRAME; [exact SIZE |cbn; intuition discriminate] |]. split.
      * cbn; rewrite Z.add_0_r; rewrite FRAME; [exact POSITION |cbn; intuition discriminate].
      * intros identifier OUTSIDE; apply FRAME; intro MEMBER; apply OUTSIDE; unfold json_integer_written.
        destruct MEMBER as [SAME |[SAME |EMPTY]]; [right; left; exact SAME |right; right; left; exact SAME |contradiction].
  - assert (BOUNDS : 0 <= index /\ index < count /\ count <= 65536).
    { change (index + Z.of_nat (S (length rest)) = count) in LENGTH; rewrite Nat2Z.inj_succ in LENGTH; lia. }
    destruct (gateway_json_integer_one backend ge property parameters continuation object index count byte memory CLOSED BOUNDS
      BYTES POSITION SIZE ltac:(intros changed owner GOOD; specialize (LOADS 0%nat byte eq_refl changed owner GOOD);
        cbn in LOADS; rewrite Z.add_0_r in LOADS; exact LOADS))
      as (next_parameters & STEP & NEXT_BYTES & NEXT_SIZE & NEXT_INDEX & FRAME).
    cbn [json_number_take_digits]; destruct (gateway_integer_digit byte) eqn:DIGIT.
    + rewrite ?DIGIT in STEP, NEXT_INDEX.
      pose proof (IH next_parameters (index + 1) ltac:(lia) ltac:(change (index + Z.of_nat (S (length rest)) = count) in LENGTH; rewrite Nat2Z.inj_succ in LENGTH; lia)
        NEXT_BYTES NEXT_INDEX NEXT_SIZE
        ltac:(intros offset selected SELECTED changed owner GOOD; specialize (LOADS (S offset) selected SELECTED changed owner GOOD);
          rewrite Nat2Z.inj_succ in LOADS; replace (index + Z.succ (Z.of_nat offset)) with (index + 1 + Z.of_nat offset) in LOADS by lia;
          exact LOADS)) as NEXT.
      destruct (json_number_take_digits rest) as [digits tail] eqn:TAKE; cbn in NEXT |- *.
      destruct NEXT as (final & SUFFIX & FINAL_BYTES & FINAL_SIZE & FINAL_INDEX & FINAL_FRAME).
      exists final; split; [eapply json_number_segment_compose; [exact STEP |exact SUFFIX] |].
      split; [exact FINAL_BYTES |]. split; [exact FINAL_SIZE |]. split.
      * change (final ! _index = Some (Vlong (Int64.repr (index + Z.of_nat (S (length digits)))))); rewrite Nat2Z.inj_succ; replace (index + Z.succ (Z.of_nat (length digits))) with (index + 1 + Z.of_nat (length digits)) by lia.
        exact FINAL_INDEX.
      * intros identifier OUTSIDE; rewrite FINAL_FRAME by exact OUTSIDE; apply FRAME; exact OUTSIDE.
    + rewrite ?DIGIT in STEP, NEXT_INDEX; cbn.
      exists next_parameters; split; [exact STEP |]. split; [exact NEXT_BYTES |]. split; [exact NEXT_SIZE |].
      split; [rewrite Z.add_0_r; exact NEXT_INDEX |exact FRAME].
Qed.

Theorem gateway_json_number_integer_digits {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) continuation object count memory remaining parameters index :
  gateway_ambient_closed backend property -> 0 <= index /\ index < count /\ count <= 65536 ->
  index + 1 + Z.of_nat (length remaining) = count ->
  parameters ! _bytes = Some (Vptr object Ptrofs.zero) -> parameters ! _index = Some (Vlong (Int64.repr index)) ->
  parameters ! _size = Some (Vlong (Int64.repr count)) ->
  (forall offset byte, nth_error remaining offset = Some byte -> forall memory world, property memory world ->
    Mem.loadv Mint8signed memory (Vptr object (Ptrofs.repr (index + 1 + Z.of_nat offset))) = Some (Vint (Int.repr (Byte.signed byte)))) ->
  let (digits, tail) := json_number_take_digits remaining in
  exists final_parameters,
    gateway_source_segment backend ge property
      (State f_host_json_number json_number_integer_loop continuation empty_env parameters memory)
      (State f_host_json_number Sskip continuation empty_env final_parameters memory) property /\
    final_parameters ! _bytes = Some (Vptr object Ptrofs.zero) /\
    final_parameters ! _size = Some (Vlong (Int64.repr count)) /\
    final_parameters ! _index = Some (Vlong (Int64.repr (index + 1 + Z.of_nat (length digits)))) /\
    (forall identifier, ~ In identifier json_integer_written -> final_parameters ! identifier = parameters ! identifier).
Proof.
  intros CLOSED INDEX LENGTH BYTES POSITION SIZE LOADS.
  pose proof (gateway_json_integer_increment backend ge property parameters continuation index memory CLOSED POSITION) as PREFIX.
  pose proof (gateway_json_integer_test_digits backend ge property continuation object count memory CLOSED ltac:(lia)
    remaining (PTree.set _index (Vlong (Int64.repr (index + 1))) parameters) (index + 1) ltac:(lia) LENGTH
    ltac:(rewrite PTree.gso by discriminate; exact BYTES) ltac:(apply PTree.gss)
    ltac:(rewrite PTree.gso by discriminate; exact SIZE) LOADS) as FOLD.
  destruct (json_number_take_digits remaining) as [digits tail]; cbn in FOLD |- *.
  destruct FOLD as (final & SUFFIX & FINAL_BYTES & FINAL_SIZE & FINAL_INDEX & FRAME).
  exists final; split; [eapply json_number_segment_compose; [exact PREFIX |exact SUFFIX] |].
  split; [exact FINAL_BYTES |]. split; [exact FINAL_SIZE |]. split; [exact FINAL_INDEX |].
  intros identifier OUTSIDE; rewrite FRAME by exact OUTSIDE; rewrite PTree.gso; [reflexivity |].
  intro SAME; apply OUTSIDE; cbn; left; congruence.
Qed.
