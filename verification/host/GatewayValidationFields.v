(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Indexed validation facts retain the exact source name and optional builtin check. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayObjects GatewayOutcome GatewayOutcomeValidationPaths GatewayObjectInstances.
Import ListNotations.
Local Close Scope lean_scope.

Definition gateway_validation_field_kind (index : nat) : gateway_builtin_kind :=
  if (Nat.eqb index 4 || Nat.eqb index 10)%bool then gateway_dict_kind else
  if Nat.eqb index 5 then gateway_long_kind else
  if (Nat.eqb index 8 || Nat.eqb index 9)%bool then gateway_bytes_kind else gateway_unicode_kind.

Definition gateway_validation_field_class dictionary integer bytes unicode (index : nat) : block :=
  if (Nat.eqb index 4 || Nat.eqb index 10)%bool then dictionary else
  if Nat.eqb index 5 then integer else
  if (Nat.eqb index 8 || Nat.eqb index 9)%bool then bytes else unicode.

Definition gateway_validated_field none captured fields index : Prop :=
  exists characters field description kind,
    nth_error gateway_outcome_names index = Some characters /\
    gateway_dictionary_lookup characters fields = Some field /\
    gateway_object_values captured (gateway_dictionary_value field) = Some description /\
    gateway_object_kind description = Some kind /\
    ((gateway_validation_optional index = Int.one /\ gateway_dictionary_value field = Vptr none Ptrofs.zero) \/
      gateway_builtin_accepts (gateway_validation_field_kind index) kind = true).

Definition gateway_validated_fields none captured fields count : Prop :=
  forall index, (index < count)%nat -> gateway_validated_field none captured fields index.

Lemma gateway_validation_field_optional index : gateway_validation_optional index = Int.zero \/ gateway_validation_optional index = Int.one.
Proof.
  unfold gateway_validation_optional; destruct (Nat.eqb index 4 || Nat.eqb index 7 || Nat.eqb index 11 || Nat.eqb index 13)%bool; auto.
Qed.

Theorem gateway_validation_field_class_binding (ge : Clight.genv) dictionary integer bytes unicode index :
  Genv.find_symbol ge _PyDict_Type = Some dictionary -> Genv.find_symbol ge _PyLong_Type = Some integer ->
  Genv.find_symbol ge _PyBytes_Type = Some bytes -> Genv.find_symbol ge _PyUnicode_Type = Some unicode ->
  gateway_builtin_type_address ge (gateway_validation_field_kind index)
    (Vptr (gateway_validation_field_class dictionary integer bytes unicode index) Ptrofs.zero).
Proof.
  intros DICTIONARY INTEGER BYTES UNICODE; unfold gateway_validation_field_kind, gateway_validation_field_class.
  destruct (Nat.eqb index 4 || Nat.eqb index 10)%bool; [constructor; exact DICTIONARY |].
  destruct (Nat.eqb index 5); [constructor; exact INTEGER |].
  destruct (Nat.eqb index 8 || Nat.eqb index 9)%bool; constructor; assumption.
Qed.

Lemma gateway_validation_field_counter index :
  (index < 14)%nat -> Int.add (Int.repr (Z.of_nat index)) Int.one = Int.repr (Z.of_nat (S index)).
Proof.
  intro BOUND; unfold Int.add; rewrite Int.unsigned_repr by (change (0 <= Z.of_nat index <= 4294967295); lia).
  change (Int.repr (Z.of_nat index + 1) = Int.repr (Z.of_nat (S index))).
  f_equal; lia.
Qed.

Theorem gateway_validation_fields_extend none captured fields count :
  gateway_validated_fields none captured fields count -> gateway_validated_field none captured fields count ->
  gateway_validated_fields none captured fields (S count).
Proof.
  intros PREVIOUS CURRENT index BOUND; destruct (Nat.eq_dec index count) as [SAME |OTHER]; [subst; exact CURRENT |apply PREVIOUS; lia].
Qed.
