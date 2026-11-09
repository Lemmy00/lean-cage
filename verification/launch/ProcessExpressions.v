(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Decidable exact source-expression identities used by the caller checker. *)
From compcert Require Import Coqlib Integers Floats Ctypes Cop Clight.

Definition expression_eq (first second : expr) : {first = second} + {first <> second}.
Proof.
  decide equality; try apply type_eq; try apply Pos.eq_dec;
    try apply Int.eq_dec; try apply Int64.eq_dec;
    try apply Float.eq_dec; try apply Float32.eq_dec;
    decide equality.
Defined.

Definition expression_equal (first second : expr) : bool :=
  if expression_eq first second then true else false.

Theorem expression_equal_exact first second :
  expression_equal first second = true <-> first = second.
Proof.
  unfold expression_equal. destruct (expression_eq first second); intuition discriminate.
Qed.
