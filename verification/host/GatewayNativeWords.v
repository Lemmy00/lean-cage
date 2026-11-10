(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: C int operands sign-extend into the exact shared 64-bit word. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewayNativeImport.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.
Local Opaque Nat_of_nat Z.to_nat Nat.pow.

Definition gateway_native_word (value : int64) : Lean.Nat :=
  Nat_of_nat (Z.to_nat (Int64.unsigned value)).
Definition gateway_native_int (value : int) : Lean.Nat :=
  gateway_native_word (Int64.repr (Int.signed value)).
Fixpoint gateway_native_bytes (bytes : list Byte.int) : GatewayNativeImport.List_inst1 Lean.Nat :=
  match bytes with
  | [] => GatewayNativeImport.List_nil_inst1 _
  | byte :: rest => GatewayNativeImport.List_cons_inst1 _ (Nat_of_nat (Z.to_nat (Byte.unsigned byte)))
      (gateway_native_bytes rest)
  end.
Fixpoint gateway_native_byte_vectors (strings : list (list Byte.int))
    : GatewayNativeImport.List_inst1 (GatewayNativeImport.List_inst1 Lean.Nat) := match strings with
  | [] => GatewayNativeImport.List_nil_inst1 _
  | first :: rest => GatewayNativeImport.List_cons_inst1 _ (gateway_native_bytes first) (gateway_native_byte_vectors rest)
  end.

Theorem gateway_native_word_value value :
  Z.of_nat (nat_of_Nat (gateway_native_word value)) = Int64.unsigned value.
Proof.
  unfold gateway_native_word; rewrite nat2Natid, Z2Nat.id;
    [reflexivity |pose proof (Int64.unsigned_range value); lia].
Qed.

Theorem gateway_native_word_bound value :
  (nat_of_Nat (gateway_native_word value) < 2 ^ 64)%nat.
Proof.
  apply Nat2Z.inj_lt; rewrite gateway_native_word_value, Nat2Z.inj_pow.
  change (Int64.unsigned value < 18446744073709551616).
  exact (proj2 (Int64.unsigned_range value)).
Qed.

Theorem gateway_native_int_sign_extended value :
  Z.of_nat (nat_of_Nat (gateway_native_int value)) =
    Int64.unsigned (Int64.repr (Int.signed value)).
Proof. apply gateway_native_word_value. Qed.

Theorem gateway_native_int_negative_one :
  gateway_native_int (Int.neg Int.one) = Nat_of_nat (Z.to_nat 18446744073709551615).
Proof. reflexivity. Qed.

Theorem gateway_native_int_nonnegative value :
  0 <= Int.signed value ->
  Z.of_nat (nat_of_Nat (gateway_native_int value)) = Int.signed value.
Proof.
  intro NONNEGATIVE; rewrite gateway_native_int_sign_extended.
  rewrite Int64.unsigned_repr; [reflexivity |].
  pose proof (Int.signed_range value); change Int.max_signed with 2147483647 in *.
  change Int64.max_unsigned with 18446744073709551615; lia.
Qed.

Theorem gateway_native_repr_int value :
  0 <= value <= Int.max_signed ->
  gateway_native_int (Int.repr value) = Nat_of_nat (Z.to_nat value).
Proof.
  intro RANGE; unfold gateway_native_int, gateway_native_word.
  rewrite Int.signed_repr by (change Int.min_signed with (-2147483648); lia).
  rewrite Int64.unsigned_repr; [reflexivity |].
  change Int.max_signed with 2147483647 in RANGE.
  change Int64.max_unsigned with 18446744073709551615; lia.
Qed.

Definition gateway_native_errno (error : int) : Lean.Nat :=
  gateway_native_word (Int64.repr (- Int.signed error)).

Theorem gateway_native_errno_value error :
  Z.of_nat (nat_of_Nat (gateway_native_errno error)) =
    Int64.unsigned (Int64.repr (- Int.signed error)).
Proof. apply gateway_native_word_value. Qed.
