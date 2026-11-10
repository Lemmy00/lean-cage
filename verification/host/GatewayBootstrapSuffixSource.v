(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual memcmp arguments select the retained filename suffix. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayBootstrapABI GatewayBootstrapValidationSource.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_bootstrap_suffix_pointer offset size :
  30 <= size <= 4095 ->
  Ptrofs.sub (Ptrofs.add offset (Ptrofs.of_int64 (Int64.repr size)))
    (Ptrofs.of_int64 (Int64.repr 30)) =
    Ptrofs.add offset (Ptrofs.repr (size - 30)).
Proof.
  intro SIZE.
  unfold Ptrofs.of_int64.
  rewrite !Int64.unsigned_repr by
    (change Int64.max_unsigned with 18446744073709551615; lia).
  rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc, <- Ptrofs.sub_add_opp.
  unfold Ptrofs.sub; rewrite !Ptrofs.unsigned_repr by
    (change Ptrofs.max_unsigned with 18446744073709551615; lia).
  reflexivity.
Qed.

Theorem gateway_bootstrap_suffix_expression ge environment temporaries memory path object offset size :
  typeof path = tptr tschar \/ typeof path = tarray tschar 4096 ->
  expression_value ge environment temporaries memory path (Vptr object offset) ->
  temporaries ! _size = Some (Vlong (Int64.repr size)) ->
  temporaries ! _tail = Some (Vlong (Int64.repr 30)) -> 30 <= size <= 4095 ->
  expression_value ge environment temporaries memory
    (Ebinop Osub (Ebinop Oadd path (Etempvar _size tulong) (tptr tschar))
      (Etempvar _tail tulong) (tptr tschar))
    (Vptr object (Ptrofs.add offset (Ptrofs.repr (size - 30)))).
Proof.
  intros TYPE PATH SIZE TAIL RANGE.
  eapply binary_expression_value with
    (v := Vptr object (Ptrofs.add offset (Ptrofs.of_int64 (Int64.repr size))))
    (w := Vlong (Int64.repr 30)).
  - eapply binary_expression_value; [exact PATH |apply old_expression_value, value_temp; exact SIZE |].
    destruct TYPE as [TYPE |TYPE]; rewrite TYPE;
      change (Some (Vptr object (Ptrofs.add offset
        (Ptrofs.mul Ptrofs.one (Ptrofs.of_int64 (Int64.repr size))))) =
        Some (Vptr object (Ptrofs.add offset (Ptrofs.of_int64 (Int64.repr size)))));
      rewrite Ptrofs.mul_commut, Ptrofs.mul_one; reflexivity.
  - apply old_expression_value, value_temp; exact TAIL.
  - change (Some (Vptr object (Ptrofs.sub
      (Ptrofs.add offset (Ptrofs.of_int64 (Int64.repr size)))
      (Ptrofs.mul Ptrofs.one (Ptrofs.of_int64 (Int64.repr 30))))) =
      Some (Vptr object (Ptrofs.add offset (Ptrofs.repr (size - 30))))).
    rewrite Ptrofs.mul_commut, Ptrofs.mul_one, gateway_bootstrap_suffix_pointer by exact RANGE.
    reflexivity.
Qed.

Theorem gateway_bootstrap_suffix_call_edge (ge : Clight.genv) function environment temporaries memory
    compared path object offset size suffix symbol continuation :
  environment ! _memcmp = None -> Genv.find_symbol ge _memcmp = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some (gateway_bootstrap_signature gateway_memory_compare_api) ->
  environment ! _suffix = None -> Genv.find_symbol ge _suffix = Some suffix ->
  typeof path = tptr tschar \/ typeof path = tarray tschar 4096 ->
  expression_value ge environment temporaries memory path (Vptr object offset) ->
  temporaries ! _size = Some (Vlong (Int64.repr size)) ->
  temporaries ! _tail = Some (Vlong (Int64.repr 30)) -> 30 <= size <= 4095 ->
  store_edge ge
    (State function (bootstrap_suffix_call compared path) continuation environment temporaries memory)
    (Callstate (gateway_bootstrap_signature gateway_memory_compare_api)
      [Vptr object (Ptrofs.add offset (Ptrofs.repr (size - 30)));
       Vptr suffix Ptrofs.zero; Vlong (Int64.repr 30)]
      (Kcall (Some compared) function environment temporaries continuation) memory).
Proof.
  intros LOCAL SYMBOL FUNCTION SUFFIX_LOCAL SUFFIX_SYMBOL TYPE PATH SIZE TAIL RANGE.
  eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value; eapply value_function;
      [exact LOCAL |exact SYMBOL |reflexivity].
  - eapply cons_argument_values.
    + eapply gateway_bootstrap_suffix_expression; eassumption.
    + reflexivity.
    + eapply cons_argument_values with (v := Vptr suffix Ptrofs.zero).
      * apply old_expression_value; eapply value_function;
          [exact SUFFIX_LOCAL |exact SUFFIX_SYMBOL |reflexivity].
      * reflexivity.
      * eapply cons_argument_values with (v := Vlong (Int64.repr 30));
          [apply old_expression_value, value_temp; exact TAIL |reflexivity |apply no_argument_values].
  - cbn; exact FUNCTION.
  - reflexivity.
Qed.
