(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Reused immutable pointers retain distinct source-owned references. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers Values Memory.
From HostGateway Require Import GatewayReferenceLedger GatewayReferenceAccounting GatewayPython.
Import ListNotations.
Local Open Scope nat_scope.

Definition gateway_alias_first:=gateway_reference_argument 0 0.
Definition gateway_alias_second:=gateway_reference_argument 0 1.
Definition gateway_alias_entry(ticket:nat)owner pointer:gateway_owned_reference:={|
  gateway_reference_ticket:=ticket;gateway_reference_owner:=owner;gateway_reference_pointer:=pointer|}.
Definition gateway_alias_one pointer:gateway_reference_ledger:={|
  gateway_reference_next:=1;gateway_reference_entries:=[gateway_alias_entry 0 gateway_alias_first pointer]|}.
Definition gateway_alias_two pointer:gateway_reference_ledger:={|
  gateway_reference_next:=2;gateway_reference_entries:=
    [gateway_alias_entry 1 gateway_alias_second pointer;gateway_alias_entry 0 gateway_alias_first pointer]|}.
Definition gateway_alias_released pointer:gateway_reference_ledger:={|
  gateway_reference_next:=2;gateway_reference_entries:=[gateway_alias_entry 1 gateway_alias_second pointer]|}.
Definition gateway_alias_empty:gateway_reference_ledger:={|
  gateway_reference_next:=2;gateway_reference_entries:=[]|}.

Lemma gateway_alias_first_mint pointer:
  gateway_reference_apply(gateway_reference_mint gateway_alias_first pointer)
    (gateway_reference_valid gateway_reference_empty)=gateway_reference_valid(gateway_alias_one pointer).
Proof. reflexivity. Qed.

Lemma gateway_alias_second_mint pointer:
  gateway_reference_apply(gateway_reference_mint gateway_alias_second pointer)
    (gateway_reference_valid(gateway_alias_one pointer))=gateway_reference_valid(gateway_alias_two pointer).
Proof. reflexivity. Qed.

Lemma gateway_alias_release_first pointer:
  gateway_reference_apply(gateway_reference_release gateway_alias_first pointer)
    (gateway_reference_valid(gateway_alias_two pointer))=gateway_reference_valid(gateway_alias_released pointer).
Proof.
  change((if Val.eq pointer pointer then gateway_reference_valid(gateway_alias_released pointer)
    else gateway_reference_invalid gateway_reference_mismatch)=gateway_reference_valid(gateway_alias_released pointer)).
  destruct(Val.eq pointer pointer);[reflexivity|contradiction].
Qed.

Lemma gateway_alias_release_second pointer:
  gateway_reference_apply(gateway_reference_release gateway_alias_second pointer)
    (gateway_reference_valid(gateway_alias_released pointer))=gateway_reference_valid gateway_alias_empty.
Proof.
  change((if Val.eq pointer pointer then gateway_reference_valid gateway_alias_empty
    else gateway_reference_invalid gateway_reference_mismatch)=gateway_reference_valid gateway_alias_empty).
  destruct(Val.eq pointer pointer);[reflexivity|contradiction].
Qed.

Theorem gateway_alias_ledger_useful pointer:
  gateway_reference_ledger_well_formed(gateway_alias_two pointer) /\
  gateway_reference_ledger_well_formed(gateway_alias_released pointer) /\
  gateway_reference_owns(gateway_alias_two pointer)gateway_alias_first 0 pointer /\
  gateway_reference_owns(gateway_alias_two pointer)gateway_alias_second 1 pointer /\
  gateway_reference_owns(gateway_alias_released pointer)gateway_alias_second 1 pointer /\
  gateway_reference_count(gateway_alias_two pointer)pointer=2 /\
  gateway_reference_count(gateway_alias_released pointer)pointer=1 /\
  gateway_reference_apply(gateway_reference_release gateway_alias_first pointer)
    (gateway_reference_valid(gateway_alias_two pointer))=gateway_reference_valid(gateway_alias_released pointer) /\
  gateway_reference_apply(gateway_reference_release gateway_alias_second pointer)
    (gateway_reference_valid(gateway_alias_released pointer))=gateway_reference_valid gateway_alias_empty.
Proof.
  assert(ONE:gateway_reference_ledger_well_formed(gateway_alias_one pointer)).
  { eapply gateway_reference_apply_well_formed;[exact gateway_reference_empty_well_formed|apply gateway_alias_first_mint]. }
  assert(TWO:gateway_reference_ledger_well_formed(gateway_alias_two pointer)).
  { eapply gateway_reference_apply_well_formed;[exact ONE|apply gateway_alias_second_mint]. }
  assert(RELEASED:gateway_reference_ledger_well_formed(gateway_alias_released pointer)).
  { eapply gateway_reference_apply_well_formed;[exact TWO|apply gateway_alias_release_first]. }
  split;[exact TWO|]. split;[exact RELEASED|]. split;[right;left;reflexivity|].
  split;[left;reflexivity|]. split;[left;reflexivity|].
  split.
  - change((if Val.eq pointer pointer then S(if Val.eq pointer pointer then 1 else 0)
      else(if Val.eq pointer pointer then 1 else 0))=2).
    destruct(Val.eq pointer pointer);[reflexivity|contradiction].
  - split.
    + change((if Val.eq pointer pointer then 1 else 0)=1).
      destruct(Val.eq pointer pointer);[reflexivity|contradiction].
    + split;[apply gateway_alias_release_first|apply gateway_alias_release_second].
Qed.

(* This is a logical reference-count projection for an immutable cached object.
   Its stable runtime reference remains when the two C-owned references end. *)
Definition gateway_alias_python(pointer:Values.val)(native:nat):python_world:={|
  python_values:=fun query=>if Val.eq query pointer then Some python_other_value else None;
  python_strong:=fun query=>if Val.eq query pointer then S native else 0;
  python_native_strong:=fun query=>if Val.eq query pointer then native else 0;
  python_runtime_owned:=fun object=>match pointer with Vptr block _=>object=block|_=>False end;
  python_gil:=true;python_pending:=None|}.

Theorem gateway_alias_count_model pointer:
  gateway_reference_counts_fit(gateway_alias_two pointer)(gateway_alias_python pointer 2) /\
  gateway_reference_counts_fit(gateway_alias_released pointer)(gateway_alias_python pointer 1) /\
  gateway_reference_counts_fit gateway_alias_empty(gateway_alias_python pointer 0).
Proof.
  split.
  - intro query;unfold gateway_reference_count;cbn.
    destruct(Val.eq pointer query)as[SAME|DIFFERENT];destruct(Val.eq query pointer);try congruence;cbn;lia.
  - split.
    + intro query;unfold gateway_reference_count;cbn.
      destruct(Val.eq pointer query)as[SAME|DIFFERENT];destruct(Val.eq query pointer);try congruence;cbn;lia.
    + intro query;unfold gateway_reference_count;cbn;lia.
Qed.
