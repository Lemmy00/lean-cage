(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual sign/empty checks bind the first integer byte or reject. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayJsonNumberSource GatewayJsonNumberSourceBytes
  GatewayJsonNumberSourceTests GatewayJsonNumberSourceFraction GatewayIntegerCanonical GatewayIntegerLoop GatewayIntegerPrefix
  GatewaySourceSegments GatewaySourceSegmentAutomation GatewayFramedRuntime GatewayFailurePaths GatewaySourceCuts.
Import ListNotations.
Open Scope Z_scope.

Definition json_number_entry_written := [_index; _negative; _digits; _t'1; _t'38].
Definition json_number_integer_cont := Kseq json_number_after_integer Kstop.

Theorem gateway_json_number_entry_source {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) parameters object bytes memory :
  gateway_ambient_closed backend property -> Z.of_nat (length bytes) <= 65536 ->
  parameters ! _bytes = Some (Vptr object Ptrofs.zero) ->
  parameters ! _size = Some (Vlong (Int64.repr (Z.of_nat (length bytes)))) ->
  (forall offset byte, nth_error bytes offset = Some byte -> forall memory world, property memory world ->
    Mem.loadv Mint8signed memory (Vptr object (Ptrofs.repr (Z.of_nat offset))) = Some (Vint (Int.repr (Byte.signed byte)))) ->
  match gateway_integer_digits bytes with
  | [] => gateway_failure_when backend ge property
      (State f_host_json_number (fn_body f_host_json_number) Kstop empty_env parameters memory)
  | _ :: _ => exists changed,
      gateway_source_segment backend ge property
        (State f_host_json_number (fn_body f_host_json_number) Kstop empty_env parameters memory)
        (State f_host_json_number json_number_integer json_number_integer_cont empty_env changed memory) property /\
      changed ! _bytes = Some (Vptr object Ptrofs.zero) /\
      changed ! _size = Some (Vlong (Int64.repr (Z.of_nat (length bytes)))) /\
      changed ! _index = Some (Vlong (Int64.repr (gateway_integer_start bytes))) /\
      changed ! _digits = Some (Vlong (Int64.repr (gateway_integer_start bytes))) /\
      changed ! _negative = Some (Vint (if gateway_integer_negative bytes then Int.one else Int.zero)) /\
      (forall identifier, ~ In identifier json_number_entry_written -> changed ! identifier = parameters ! identifier)
  end.
Proof.
  intros CLOSED BOUND BYTES SIZE LOADS.
  destruct bytes as [|first rest].
  - cbn [gateway_integer_digits gateway_integer_negative].
    assert (SEGMENT : exists changed, gateway_source_segment backend ge property
      (State f_host_json_number (fn_body f_host_json_number) Kstop empty_env parameters memory)
      (State f_host_json_number (Sgoto _invalid) (Kseq json_number_after_empty Kstop) empty_env changed memory) property).
    { eexists; gateway_segment_dynamic CLOSED ltac:(fun _ => fail) ltac:(fun _ => json_number_source_reduce). }
    destruct SEGMENT as [changed SEGMENT]; eapply json_number_segment_denial; [exact SEGMENT |].
    apply gateway_json_number_invalid_denied; reflexivity.
  - pose proof (gateway_integer_signed_range first) as BYTE_RANGE.
    cbn [gateway_integer_digits gateway_integer_negative]; destruct (Byte.eq first (Byte.repr 45)) eqn:SIGN.
    + unfold gateway_integer_digits; cbn [gateway_integer_negative]; rewrite SIGN; cbn [tl]; destruct rest as [|second tail].
      * cbn [tl].
        assert (SEGMENT : exists changed, gateway_source_segment backend ge property
          (State f_host_json_number (fn_body f_host_json_number) Kstop empty_env parameters memory)
          (State f_host_json_number (Sgoto _invalid) (Kseq json_number_after_empty Kstop) empty_env changed memory) property).
        { eexists; gateway_segment_dynamic CLOSED
            ltac:(fun _ => eapply gateway_json_number_fixed_character with (index := 0) (byte := first) (object := object);
              [lia |repeat rewrite PTree.gso by discriminate; exact BYTES |
                eapply (LOADS 0%nat first); [reflexivity |eassumption]])
            ltac:(fun _ => json_number_source_reduce). }
        destruct SEGMENT as [changed SEGMENT]; eapply json_number_segment_denial; [exact SEGMENT |].
        apply gateway_json_number_invalid_denied; reflexivity.
      * assert (LENGTH_BOUND : 2 + Z.of_nat (length tail) <= 65536).
        { change (Z.of_nat (S (S (length tail))) <= 65536) in BOUND; rewrite !Nat2Z.inj_succ in BOUND; lia. }
        cbn [tl]; eexists; split.
        -- unfold json_number_integer_cont; gateway_segment_dynamic CLOSED
            ltac:(fun _ => eapply gateway_json_number_fixed_character with (index := 0) (byte := first) (object := object);
              [lia |repeat rewrite PTree.gso by discriminate; exact BYTES |
                eapply (LOADS 0%nat first); [reflexivity |eassumption]])
            ltac:(fun _ => json_number_source_reduce).
        -- unfold gateway_integer_start, gateway_integer_negative; rewrite SIGN; repeat split;
             try solve [repeat rewrite PTree.gso by discriminate; try rewrite PTree.gss; assumption || reflexivity].
           intros identifier OUTSIDE; repeat rewrite PTree.gso by
             (intro SAME; apply OUTSIDE; subst identifier; cbn; auto 8); reflexivity.
    + assert (LENGTH_BOUND : 1 + Z.of_nat (length rest) <= 65536).
      { change (Z.of_nat (S (length rest)) <= 65536) in BOUND; rewrite Nat2Z.inj_succ in BOUND; lia. }
      unfold gateway_integer_digits; cbn [gateway_integer_negative]; rewrite SIGN; cbn [tl]; eexists; split.
      * unfold json_number_integer_cont; gateway_segment_dynamic CLOSED
          ltac:(fun _ => eapply gateway_json_number_fixed_character with (index := 0) (byte := first) (object := object);
            [lia |repeat rewrite PTree.gso by discriminate; exact BYTES |
              eapply (LOADS 0%nat first); [reflexivity |eassumption]]) ltac:(fun _ => json_number_source_reduce).
      * unfold gateway_integer_start, gateway_integer_negative; rewrite SIGN; repeat split;
           try solve [repeat rewrite PTree.gso by discriminate; try rewrite PTree.gss; assumption || reflexivity].
        intros identifier OUTSIDE; repeat rewrite PTree.gso by
          (intro SAME; apply OUTSIDE; subst identifier; cbn; auto 8); reflexivity.
Qed.
