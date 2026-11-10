(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Native buffer offsets and the terminating byte use actual source expressions. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess.
From HostGateway Require Import GatewaySource GatewayBootstrapCopySource GatewayBootstrapCopyEdges.
Open Scope Z_scope.

Theorem gateway_bootstrap_array_offset (ge : Clight.genv) environment temporaries memory identifier size object amount :
  environment ! identifier = None -> Genv.find_symbol ge identifier = Some object ->
  temporaries ! size = Some (Vlong (Int64.repr amount)) -> 0 <= amount <= Int64.max_unsigned ->
  expression_value ge environment temporaries memory
    (bootstrap_array_add identifier (Etempvar size tulong)) (Vptr object (Ptrofs.repr amount)).
Proof.
  intros LOCAL SYMBOL SIZE RANGE.
  eapply binary_expression_value with (v := Vptr object Ptrofs.zero) (w := Vlong (Int64.repr amount)).
  - eapply gateway_bootstrap_global_array_reference; eassumption.
  - apply old_expression_value, value_temp; exact SIZE.
  - change (Some (Vptr object (Ptrofs.add Ptrofs.zero
      (Ptrofs.mul Ptrofs.one (Ptrofs.of_int64 (Int64.repr amount))))) =
      Some (Vptr object (Ptrofs.repr amount))).
    unfold Ptrofs.of_int64; rewrite Int64.unsigned_repr by exact RANGE.
    rewrite Ptrofs.add_zero_l, Ptrofs.mul_commut, Ptrofs.mul_one; reflexivity.
Qed.

Theorem actual_bootstrap_root_terminator_edge (ge : Clight.genv) environment temporaries continuation
    before after root amount :
  environment ! _host_root = None -> Genv.find_symbol ge _host_root = Some root ->
  temporaries ! _root_size = Some (Vlong (Int64.repr amount)) -> 0 <= amount <= 4065 ->
  Mem.store Mint8signed before root amount (Vint Int.zero) = Some after ->
  store_edge ge
    (State f_host_bootstrap (bootstrap_copy_statement 1) continuation environment temporaries before)
    (State f_host_bootstrap Sskip continuation environment temporaries after).
Proof.
  intros LOCAL SYMBOL SIZE RANGE STORE.
  eapply assignment_source_edge with (b := root) (ofs := Ptrofs.repr amount)
    (v := Vint Int.zero) (w := Vint Int.zero).
  - apply pointer_location_value; eapply gateway_bootstrap_array_offset;
      [exact LOCAL |exact SYMBOL |exact SIZE |
       change Int64.max_unsigned with 18446744073709551615; lia].
  - apply old_expression_value; constructor.
  - reflexivity.
  - apply assign_loc_value with (chunk := Mint8signed); [reflexivity |].
    unfold Mem.storev; rewrite Ptrofs.unsigned_repr by
      (change Ptrofs.max_unsigned with 18446744073709551615; lia).
    rewrite zle_true; [exact STORE |].
    change Ptrofs.modulus with 18446744073709551616; cbn [size_chunk]; lia.
Qed.
