(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual unsigned capacity guards justify the native copies. *)
From Stdlib Require Import ZArith Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Ctypesdefs Cop Clight.
Require Import ClightSteps LocalAccess.
From HostGateway Require Import GatewayBootstrapLengthBindings.
Open Scope Z_scope.

Theorem gateway_bootstrap_subtract_expression ge environment temporaries memory size tail amount :
  temporaries ! size = Some (Vlong (Int64.repr amount)) ->
  temporaries ! tail = Some (Vlong (Int64.repr 30)) -> 30 <= amount <= 4095 ->
  expression_value ge environment temporaries memory
    (Ebinop Osub (Etempvar size tulong) (Etempvar tail tulong) tulong)
    (Vlong (Int64.repr (amount - 30))).
Proof.
  intros SIZE TAIL RANGE.
  eapply binary_expression_value with (v := Vlong (Int64.repr amount)) (w := Vlong (Int64.repr 30));
    [apply old_expression_value, value_temp; exact SIZE |
     apply old_expression_value, value_temp; exact TAIL |].
  change (Some (Vlong (Int64.sub (Int64.repr amount) (Int64.repr 30))) =
    Some (Vlong (Int64.repr (amount - 30)))).
  unfold Int64.sub; rewrite !Int64.unsigned_repr by
    (change Int64.max_unsigned with 18446744073709551615; lia); reflexivity.
Qed.

Definition bootstrap_extent_test identifier count :=
  Ebinop Ogt (Ebinop Oadd (Etempvar identifier tulong)
    (Esizeof (tarray tschar count) tulong) tulong)
    (Esizeof (tarray tschar 4096) tulong) tint.

Theorem gateway_bootstrap_extent_expression ge environment temporaries memory identifier amount count :
  temporaries ! identifier = Some (Vlong (Int64.repr amount)) ->
  0 <= amount -> 0 <= count -> amount + count <= 4096 ->
  expression_value ge environment temporaries memory
    (bootstrap_extent_test identifier count) (Vint Int.zero).
Proof.
  intros AMOUNT NONNEGATIVE COUNT FIT.
  eapply binary_expression_value with
    (v := Vlong (Int64.add (Int64.repr amount) (Int64.repr count)))
    (w := Vlong (Int64.repr 4096)).
  - eapply binary_expression_value with (v := Vlong (Int64.repr amount)) (w := Vlong (Int64.repr count)).
    + apply old_expression_value, value_temp; exact AMOUNT.
    + pose proof (gateway_bootstrap_sizeof_expression ge environment temporaries memory count) as SIZE.
      rewrite Z.max_r in SIZE by exact COUNT; exact SIZE.
    + reflexivity.
  - apply gateway_bootstrap_sizeof_expression.
  - change (Some (Val.of_bool (Int64.cmpu Cgt
      (Int64.add (Int64.repr amount) (Int64.repr count)) (Int64.repr 4096))) = Some (Vint Int.zero)).
    unfold Int64.add, Int64.cmpu, Int64.ltu.
    rewrite (Int64.unsigned_repr amount), (Int64.unsigned_repr count) by
      (change Int64.max_unsigned with 18446744073709551615; lia).
    rewrite !Int64.unsigned_repr by
      (change Int64.max_unsigned with 18446744073709551615; lia).
    destruct (zlt 4096 (amount + count)); [lia |reflexivity].
Qed.
