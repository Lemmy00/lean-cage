(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: JSON number lexical data preserves sign, integer, fraction and exponent bytes. *)
From Stdlib Require Import ZArith List Bool Lia.
From compcert Require Import Integers.
From HostGateway Require Import GatewayValue GatewayIntegerCanonical.
Import ListNotations.
Open Scope Z_scope.

Fixpoint json_number_take_digits bytes : list Byte.int * list Byte.int :=
  match bytes with
  | [] => ([], [])
  | byte :: rest => if gateway_integer_digit byte then
      let (digits, remaining) := json_number_take_digits rest in (byte :: digits, remaining)
    else ([], bytes)
  end.

Definition json_number_take_fraction bytes : option (list Byte.int * list Byte.int) :=
  match bytes with
  | marker :: rest => if Byte.eq marker (Byte.repr 46) then
      let (digits, remaining) := json_number_take_digits rest in
      match digits with [] => None | _ => Some (marker :: digits, remaining) end
    else Some ([], bytes)
  | [] => Some ([], [])
  end.

Definition json_number_take_exponent_sign bytes : list Byte.int * list Byte.int :=
  match bytes with
  | head :: tail => if Byte.eq head (Byte.repr 43) || Byte.eq head (Byte.repr 45) then ([head], tail) else ([], bytes)
  | [] => ([], []) end.

Definition json_number_take_exponent bytes : option (list Byte.int * list Byte.int) :=
  match bytes with
  | marker :: rest => if Byte.eq marker (Byte.repr 101) || Byte.eq marker (Byte.repr 69) then
      let (sign, unsigned) := json_number_take_exponent_sign rest in
      let (digits, remaining) := json_number_take_digits unsigned in
      match digits with [] => None | _ => Some (marker :: sign ++ digits, remaining) end
    else Some ([], bytes)
  | [] => Some ([], [])
  end.

Record json_number_parts := {
  json_parts_sign : gateway_json_sign;
  json_parts_integer : list Byte.int;
  json_parts_fraction : list Byte.int;
  json_parts_exponent : list Byte.int
}.

Definition json_number_finish sign integer bytes : option json_number_parts :=
  match json_number_take_fraction bytes with
  | None => None
  | Some (fraction, tail) => match json_number_take_exponent tail with
    | Some (exponent, []) => Some {| json_parts_sign := sign; json_parts_integer := integer;
        json_parts_fraction := fraction; json_parts_exponent := exponent |}
    | _ => None end
  end.

Definition json_number_integer_after sign bytes : option json_number_parts :=
  match bytes with
  | [] => None
  | first :: rest => if Byte.eq first (Byte.repr 48) then json_number_finish sign [first] rest
    else if (49 <=? Byte.unsigned first) && (Byte.unsigned first <=? 57) then
      let (digits, tail) := json_number_take_digits rest in json_number_finish sign (first :: digits) tail
    else None
  end.

Definition json_number_lexical bytes : option json_number_parts :=
  match bytes with
  | first :: rest => if Byte.eq first (Byte.repr 45) then json_number_integer_after gateway_json_negative rest
    else json_number_integer_after gateway_json_positive bytes
  | [] => None
  end.

Definition json_number_parts_wire parts := gateway_json_sign_bytes (json_parts_sign parts) ++
  json_parts_integer parts ++ json_parts_fraction parts ++ json_parts_exponent parts.

Theorem json_number_take_digits_sound bytes :
  let (digits, remaining) := json_number_take_digits bytes in
  bytes = digits ++ remaining /\ Forall (fun byte => 48 <= Byte.unsigned byte <= 57) digits /\
    (remaining = [] \/ exists byte rest, remaining = byte :: rest /\ gateway_integer_digit byte = false).
Proof.
  induction bytes as [|byte rest IH]; [cbn; auto |].
  cbn [json_number_take_digits]; destruct (gateway_integer_digit byte) eqn:DIGIT.
  - destruct (json_number_take_digits rest) as [digits remaining] eqn:TAKE; cbn in IH |- *.
    destruct IH as [BYTES [DIGITS STOP]]; split; [cbn; f_equal; exact BYTES |].
    split; [constructor; [apply gateway_integer_digit_sound; exact DIGIT |exact DIGITS] |exact STOP].
  - cbn; split; [reflexivity |]. split; [constructor |right; do 2 eexists; split; [reflexivity |exact DIGIT]].
Qed.

Lemma json_number_byte_equal first second : Byte.eq first second = true -> first = second.
Proof. apply Byte.same_if_eq. Qed.

Theorem json_number_take_fraction_sound bytes fraction remaining :
  json_number_take_fraction bytes = Some (fraction, remaining) ->
  bytes = fraction ++ remaining /\ gateway_json_fraction fraction.
Proof.
  destruct bytes as [|marker rest]; cbn [json_number_take_fraction].
  - intro SAME; inversion SAME; subst; split; [reflexivity |constructor].
  - destruct (Byte.eq marker (Byte.repr 46)) eqn:MARKER.
    + apply json_number_byte_equal in MARKER; subst marker.
      pose proof (json_number_take_digits_sound rest) as SCANNED.
      destruct (json_number_take_digits rest) as [digits tail] eqn:TAKE; destruct digits as [|first digits]; [discriminate |].
      cbn in SCANNED; destruct SCANNED as [BYTES [DIGITS STOP]]; intro SAME; inversion SAME; subst fraction remaining.
      split; [cbn; f_equal; exact BYTES |constructor; split; [discriminate |exact DIGITS]].
    + intro SAME; inversion SAME; subst; split; [reflexivity |constructor].
Qed.

Theorem json_number_exponent_sign_sound bytes :
  let (sign, remaining) := json_number_take_exponent_sign bytes in
  bytes = sign ++ remaining /\ (sign = [] \/ sign = [Byte.repr 43] \/ sign = [Byte.repr 45]).
Proof.
  destruct bytes as [|head tail]; [cbn; auto |].
  cbn [json_number_take_exponent_sign].
  destruct (Byte.eq head (Byte.repr 43) || Byte.eq head (Byte.repr 45)) eqn:SIGN.
  - split; [reflexivity |]. apply orb_true_iff in SIGN; destruct SIGN as [PLUS |MINUS];
      apply json_number_byte_equal in PLUS || apply json_number_byte_equal in MINUS;
      [right; left |right; right]; congruence.
  - split; [reflexivity |left; reflexivity].
Qed.

Theorem json_number_take_exponent_sound bytes exponent remaining :
  json_number_take_exponent bytes = Some (exponent, remaining) ->
  bytes = exponent ++ remaining /\ gateway_json_exponent exponent.
Proof.
  destruct bytes as [|marker rest]; cbn [json_number_take_exponent].
  - intro SAME; inversion SAME; subst; split; [reflexivity |constructor].
  - destruct (Byte.eq marker (Byte.repr 101) || Byte.eq marker (Byte.repr 69)) eqn:MARKER.
    + assert (KIND : marker = Byte.repr 101 \/ marker = Byte.repr 69).
      { apply orb_true_iff in MARKER; destruct MARKER; [left |right]; apply json_number_byte_equal; assumption. }
      pose proof (json_number_exponent_sign_sound rest) as SIGN.
      destruct (json_number_take_exponent_sign rest) as [sign unsigned] eqn:SPLIT; destruct SIGN as [REST SIGN].
      pose proof (json_number_take_digits_sound unsigned) as SCANNED.
      destruct (json_number_take_digits unsigned) as [digits tail] eqn:TAKE; destruct digits as [|first digits]; [discriminate |].
      cbn in SCANNED; destruct SCANNED as [BYTES [DIGITS STOP]]; intro SAME; inversion SAME; subst exponent remaining.
      split.
      * cbn; f_equal; rewrite REST, BYTES.
        change (sign ++ ((first :: digits) ++ tail) = (sign ++ first :: digits) ++ tail); apply app_assoc.
      * constructor; [exact KIND |exact SIGN |split; [discriminate |exact DIGITS]].
    + intro SAME; inversion SAME; subst; split; [reflexivity |constructor].
Qed.

Theorem json_number_finish_sound sign integer bytes parts :
  json_number_finish sign integer bytes = Some parts ->
  json_parts_sign parts = sign /\ json_parts_integer parts = integer /\
  bytes = json_parts_fraction parts ++ json_parts_exponent parts /\
  gateway_json_fraction (json_parts_fraction parts) /\ gateway_json_exponent (json_parts_exponent parts).
Proof.
  unfold json_number_finish; destruct (json_number_take_fraction bytes) as [[fraction tail] |] eqn:FRACTION; [|discriminate].
  destruct (json_number_take_exponent tail) as [[exponent remaining] |] eqn:EXPONENT; [|discriminate].
  destruct remaining; [|discriminate]; intro SAME; inversion SAME; subst parts; cbn.
  destruct (json_number_take_fraction_sound _ _ _ FRACTION) as [BYTES FRACTION_VALID].
  destruct (json_number_take_exponent_sound _ _ _ EXPONENT) as [TAIL EXPONENT_VALID].
  repeat split; try assumption; rewrite TAIL, app_nil_r in BYTES; exact BYTES.
Qed.

Theorem json_number_integer_after_sound sign bytes parts :
  json_number_integer_after sign bytes = Some parts ->
  json_parts_sign parts = sign /\ bytes = json_parts_integer parts ++ json_parts_fraction parts ++ json_parts_exponent parts /\
  gateway_json_integer_part (json_parts_integer parts) /\ gateway_json_fraction (json_parts_fraction parts) /\
  gateway_json_exponent (json_parts_exponent parts).
Proof.
  destruct bytes as [|first rest]; [discriminate |]. unfold json_number_integer_after.
  destruct (Byte.eq first (Byte.repr 48)) eqn:ZERO.
  - apply json_number_byte_equal in ZERO; subst first; intro FINISH.
    destruct (json_number_finish_sound _ _ _ _ FINISH) as [SIGN [INTEGER [BYTES [FRACTION EXPONENT]]]].
    split; [exact SIGN |]. split; [rewrite INTEGER; cbn; f_equal; exact BYTES |].
    split; [left; exact INTEGER |]. split; assumption.
  - destruct ((49 <=? Byte.unsigned first) && (Byte.unsigned first <=? 57)) eqn:LEADING; [|discriminate].
    pose proof (json_number_take_digits_sound rest) as SCANNED.
    destruct (json_number_take_digits rest) as [digits tail] eqn:TAKE.
    destruct SCANNED as [BYTES [DIGITS STOP]]; intro FINISH.
    destruct (json_number_finish_sound _ _ _ _ FINISH) as [SIGN [INTEGER [TAIL [FRACTION EXPONENT]]]].
    split; [exact SIGN |]. split; [rewrite INTEGER; cbn; f_equal; rewrite <- TAIL; exact BYTES |].
    split.
    + right; exists first, digits; split; [exact INTEGER |]. split; [|exact DIGITS].
      apply andb_true_iff in LEADING; destruct LEADING; apply Z.leb_le in H; apply Z.leb_le in H0; lia.
    + split; assumption.
Qed.

Theorem json_number_lexical_sound bytes parts :
  json_number_lexical bytes = Some parts -> bytes = json_number_parts_wire parts /\ gateway_json_number bytes.
Proof.
  destruct bytes as [|first rest]; [discriminate |]. unfold json_number_lexical.
  destruct (Byte.eq first (Byte.repr 45)) eqn:NEGATIVE.
  - apply json_number_byte_equal in NEGATIVE; subst first; intro PARSED.
    destruct (json_number_integer_after_sound _ _ _ PARSED) as [SIGN [BYTES [INTEGER [FRACTION EXPONENT]]]].
    assert (WIRE : Byte.repr 45 :: rest = json_number_parts_wire parts).
    { unfold json_number_parts_wire; rewrite SIGN; cbn; f_equal; exact BYTES. }
    split; [exact WIRE |]. rewrite WIRE; unfold json_number_parts_wire; constructor; assumption.
  - intro PARSED; destruct (json_number_integer_after_sound _ _ _ PARSED) as [SIGN [BYTES [INTEGER [FRACTION EXPONENT]]]].
    assert (WIRE : first :: rest = json_number_parts_wire parts).
    { unfold json_number_parts_wire; rewrite SIGN; exact BYTES. }
    split; [exact WIRE |]. rewrite WIRE; unfold json_number_parts_wire; constructor; assumption.
Qed.
