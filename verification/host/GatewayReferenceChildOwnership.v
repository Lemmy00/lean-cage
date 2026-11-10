(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A real recursive child result is moved into the caller's selected
   temporary while preserving every older source owner, including pointer aliases. *)
From Stdlib Require Import List PeanoNat.
From compcert Require Import Values Memory Clight.
From HostGateway Require Import GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting
  GatewayReferenceMoves GatewayReferenceNormalForm GatewayReferenceThreads.
Import ListNotations.

Theorem gateway_reference_adopt_child {World}python objects decimal_float context initial returned ticket pointer held world destination:
  gateway_reference_ledger_well_formed returned->
  gateway_reference_result_entries context initial returned ticket pointer->
  destination<>gateway_reference_result(gateway_reference_depth context)->
  gateway_reference_take destination(gateway_reference_entries initial)=None->
  @gateway_reference_scope World python objects decimal_float returned held world->
  exists adopted,
    gateway_reference_apply(gateway_reference_move(gateway_reference_result(gateway_reference_depth context))destination)
      (gateway_reference_valid returned)=gateway_reference_valid adopted /\
    gateway_reference_ledger_well_formed adopted /\
    gateway_reference_entries adopted=gateway_reference_entry ticket destination pointer::gateway_reference_entries initial /\
    gateway_reference_next adopted=gateway_reference_next returned /\
    gateway_reference_owns adopted destination ticket pointer /\
    gateway_reference_scope python objects decimal_float adopted held world.
Proof.
  intros FORMED ENTRIES DIFFERENT FREE SCOPE.
  assert(OWNED:gateway_reference_owns returned(gateway_reference_result(gateway_reference_depth context))ticket pointer).
  { unfold gateway_reference_owns;rewrite ENTRIES;left;reflexivity. }
  destruct(gateway_reference_move_scope python objects decimal_float returned
    (gateway_reference_result(gateway_reference_depth context))destination ticket pointer held world FORMED OWNED
    ltac:(apply gateway_reference_take_none;intros entry MEMBER OWNER;rewrite ENTRIES in MEMBER;
      destruct MEMBER as[SAME|MEMBER];[subst entry;cbn in OWNER;congruence|
        exact(proj1(gateway_reference_take_none _ _)FREE entry MEMBER OWNER)])SCOPE)
    as[adopted[MOVE[WELL[CAPTURED[HELD REST]]]]].
  destruct(gateway_reference_head_move returned adopted(gateway_reference_entries initial)ticket
    (gateway_reference_result(gateway_reference_depth context))destination pointer ENTRIES MOVE)as[HEAD NEXT].
  exists adopted;exact(conj MOVE(conj WELL(conj HEAD(conj NEXT(conj CAPTURED HELD))))).
Qed.
