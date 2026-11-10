(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Header guard comparisons use the actual unsigned machine words. *)
From Stdlib Require Import ZArith Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Ctypesdefs Cop Clight.
Require Import ClightSteps LocalAccess.
Open Scope Z_scope.

Lemma gateway_response_unsigned_within ge environment temporaries memory identifier word limit:
  0<=limit<=Int.max_signed->Int64.unsigned word<=limit->temporaries!identifier=Some(Vlong word)->
  expression_value ge environment temporaries memory
    (Ecast(Ebinop Ogt(Etempvar identifier tulong)(Econst_int(Int.repr limit)tint)tint)tbool)(Vint Int.zero).
Proof.
  intros LIMIT SMALL LOOK;change(0<=limit<=2147483647)in LIMIT.
  apply old_expression_value;eapply value_cast with(v:=Vint Int.zero);[|reflexivity].
  eapply value_binary;[apply value_temp;exact LOOK|constructor|].
  change (Some (Val.of_bool (Int64.ltu (Int64.repr (Int.signed (Int.repr limit))) word)) = Some (Vint Int.zero)).
  rewrite Int.signed_repr by(change(-2147483648<=limit<=2147483647);lia).
  unfold Int64.ltu;rewrite Int64.unsigned_repr by(change(0<=limit<=18446744073709551615);lia).
  destruct(zlt limit(Int64.unsigned word));[lia|reflexivity].
Qed.
