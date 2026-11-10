(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual copy assignment adopts its selected credit into
   the new data cell, and the enclosing return transfers the same allocated instance credit. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers Values Memory Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayObjectThreads GatewayValue
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceMoves GatewayReferenceThreads GatewayReferenceNormalForm
  GatewayReferenceStackBound GatewayReferenceSecondMove.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Lemma gateway_reference_stack_no_cell context ledger object offset:
  gateway_reference_stack_bound context ledger->gateway_reference_take(gateway_reference_cell object offset)(gateway_reference_entries ledger)=None.
Proof.
  intros STACK;apply gateway_reference_take_none;intros entry MEMBER CELL.
  destruct(STACK entry MEMBER)as[invocation[identifier[OWNER VALUE]]];congruence.
Qed.
Lemma gateway_reference_stack_no_result context ledger invocation:
  gateway_reference_stack_bound context ledger->gateway_reference_take(gateway_reference_result invocation)(gateway_reference_entries ledger)=None.
Proof.
  intros STACK;apply gateway_reference_take_none;intros entry MEMBER RESULT.
  destruct(STACK entry MEMBER)as[depth[identifier[OWNER VALUE]]];congruence.
Qed.

Theorem gateway_owned_outcome_adopt_credits {World}python objects decimal_float context older ledger held world object data
    outcome_ticket copy_ticket:
  gateway_reference_stack_bound context older->gateway_reference_ledger_well_formed ledger->
  gateway_reference_entries ledger=
    gateway_reference_entry outcome_ticket(gateway_reference_result(S(gateway_reference_depth context)))(Vptr object Ptrofs.zero)::
    gateway_reference_entry copy_ticket(gateway_reference_temporary(gateway_reference_depth context)_copy)data::gateway_reference_entries older->
  @gateway_reference_scope World python objects decimal_float ledger held world->
  exists adopted final,
    gateway_reference_apply(gateway_reference_move(gateway_reference_temporary(gateway_reference_depth context)_copy)
      (gateway_reference_cell object 16))(gateway_reference_valid ledger)=gateway_reference_valid adopted /\
    gateway_reference_apply(gateway_reference_move(gateway_reference_result(S(gateway_reference_depth context)))
      (gateway_reference_result(gateway_reference_depth context)))(gateway_reference_valid adopted)=gateway_reference_valid final /\
    gateway_reference_ledger_well_formed final /\
    gateway_reference_entries final=
      gateway_reference_entry outcome_ticket(gateway_reference_result(gateway_reference_depth context))(Vptr object Ptrofs.zero)::
      gateway_reference_entry copy_ticket(gateway_reference_cell object 16)data::gateway_reference_entries older /\
    gateway_reference_owns final(gateway_reference_result(gateway_reference_depth context))outcome_ticket(Vptr object Ptrofs.zero) /\
    gateway_reference_owns final(gateway_reference_cell object 16)copy_ticket data /\
    gateway_reference_scope python objects decimal_float final held world /\
    (forall pointer,gateway_reference_count final pointer=gateway_reference_count ledger pointer).
Proof.
  intros STACK WELL ENTRIES SCOPE.
  assert(COPY:gateway_reference_owns ledger(gateway_reference_temporary(gateway_reference_depth context)_copy)copy_ticket data).
  { unfold gateway_reference_owns;rewrite ENTRIES;right;left;reflexivity. }
  assert(OUTCOME:gateway_reference_owns ledger(gateway_reference_result(S(gateway_reference_depth context)))outcome_ticket(Vptr object Ptrofs.zero)).
  { unfold gateway_reference_owns;rewrite ENTRIES;left;reflexivity. }
  assert(DIFFERENT:outcome_ticket<>copy_ticket).
  { intros SAME;pose proof(proj1 WELL)as UNIQUE;rewrite ENTRIES in UNIQUE;inversion UNIQUE as[|head rest ABSENT TAIL];subst.
    apply ABSENT;cbn;left;reflexivity. }
  assert(CELL_FREE:gateway_reference_take(gateway_reference_cell object 16)(gateway_reference_entries ledger)=None).
  { rewrite ENTRIES;cbn[gateway_reference_take gateway_reference_entry gateway_reference_owner].
    destruct(gateway_reference_place_eq(gateway_reference_cell object 16)(gateway_reference_result(S(gateway_reference_depth context))));[discriminate|].
    destruct(gateway_reference_place_eq(gateway_reference_cell object 16)(gateway_reference_temporary(gateway_reference_depth context)_copy));[discriminate|].
    rewrite(gateway_reference_stack_no_cell context older object 16 STACK);reflexivity. }
  assert(RETURN_FREE:gateway_reference_take(gateway_reference_result(gateway_reference_depth context))(gateway_reference_entries ledger)=None).
  { rewrite ENTRIES;cbn[gateway_reference_take gateway_reference_entry gateway_reference_owner].
    destruct(gateway_reference_place_eq(gateway_reference_result(gateway_reference_depth context))
      (gateway_reference_result(S(gateway_reference_depth context))));[injection e;intros;lia|].
    destruct(gateway_reference_place_eq(gateway_reference_result(gateway_reference_depth context))
      (gateway_reference_temporary(gateway_reference_depth context)_copy));[discriminate|].
    rewrite(gateway_reference_stack_no_result context older(gateway_reference_depth context)STACK);reflexivity. }
  destruct(gateway_reference_move_scope python objects decimal_float ledger(gateway_reference_temporary(gateway_reference_depth context)_copy)
    (gateway_reference_cell object 16)copy_ticket data held world WELL COPY CELL_FREE SCOPE)
    as(adopted &ADOPT &ADOPTED_WELL &ADOPTED_COPY &ADOPTED_SCOPE &ADOPTED_COUNTS &RETAINED).
  assert(ADOPTED_ENTRIES:gateway_reference_entries adopted=
    gateway_reference_entry copy_ticket(gateway_reference_cell object 16)data::
    gateway_reference_entry outcome_ticket(gateway_reference_result(S(gateway_reference_depth context)))(Vptr object Ptrofs.zero)::gateway_reference_entries older).
  { exact(proj1(gateway_reference_second_move ledger adopted(gateway_reference_entries older)outcome_ticket
      (gateway_reference_result(S(gateway_reference_depth context)))(Vptr object Ptrofs.zero)copy_ticket
      (gateway_reference_temporary(gateway_reference_depth context)_copy)(gateway_reference_cell object 16)data ltac:(discriminate)ENTRIES ADOPT)). }
  assert(ADOPTED_OUTCOME:gateway_reference_owns adopted(gateway_reference_result(S(gateway_reference_depth context)))outcome_ticket(Vptr object Ptrofs.zero)).
  { apply RETAINED;assumption. }
  assert(ADOPTED_RETURN_FREE:gateway_reference_take(gateway_reference_result(gateway_reference_depth context))(gateway_reference_entries adopted)=None).
  { eapply(gateway_reference_move_keeps_vacant ledger(gateway_reference_temporary(gateway_reference_depth context)_copy)
      (gateway_reference_cell object 16)(gateway_reference_result(gateway_reference_depth context))adopted);
      [exact RETURN_FREE|discriminate|exact ADOPT]. }
  destruct(gateway_reference_move_scope python objects decimal_float adopted(gateway_reference_result(S(gateway_reference_depth context)))
    (gateway_reference_result(gateway_reference_depth context))outcome_ticket(Vptr object Ptrofs.zero)held world ADOPTED_WELL ADOPTED_OUTCOME
    ADOPTED_RETURN_FREE ADOPTED_SCOPE)as(final &RETURN &FINAL_WELL &FINAL_OUTCOME &FINAL_SCOPE &FINAL_COUNTS &FINAL_RETAINED).
  exists adopted,final;split;[exact ADOPT|]. split;[exact RETURN|]. split;[exact FINAL_WELL|]. split.
  - exact(proj1(gateway_reference_second_move adopted final(gateway_reference_entries older)copy_ticket(gateway_reference_cell object 16)data
      outcome_ticket(gateway_reference_result(S(gateway_reference_depth context)))(gateway_reference_result(gateway_reference_depth context))
      (Vptr object Ptrofs.zero)ltac:(discriminate)ADOPTED_ENTRIES RETURN)).
  - split;[exact FINAL_OUTCOME|]. split;[apply FINAL_RETAINED;[congruence|exact ADOPTED_COPY]|].
    split;[exact FINAL_SCOPE|]. intro pointer;rewrite FINAL_COUNTS,ADOPTED_COUNTS;reflexivity.
Qed.
