(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: One PyDict_Next borrow writes only its three actual native outputs. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Ctypes Clight.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayReferences
  GatewayValue GatewayGraphSnapshots GatewayOutcomeValidationContext.
Import ListNotations.
Local Close Scope lean_scope.

(* CPython 3.12.3 Objects/dictobject.c, _PyDict_Next/PyDict_Next:
   https://github.com/python/cpython/blob/v3.12.3/Objects/dictobject.c#L1969-L2052
   The sparse cursor is opaque. EOF writes none of these outputs. A successful
   borrow writes position, key, value in that order; none gains a C-owned credit.
   This single-operation ABI law does not assert completion of the source loop. *)
Inductive gateway_dictionary_next_outputs fields position key value : mem -> val -> mem -> Prop :=
| gateway_dictionary_next_end : forall memory,
    gateway_dictionary_next_outputs fields position key value memory (Vint Int.zero) memory
| gateway_dictionary_next_item : forall memory after_position after_key after field cursor,
    In field fields -> 0 < Int64.signed cursor ->
    Mem.store Mint64 memory position 0 (Vlong cursor) = Some after_position ->
    Mem.store Mptr after_position key 0 (gateway_dictionary_key field) = Some after_key ->
    Mem.store Mptr after_key value 0 (gateway_dictionary_value field) = Some after ->
    gateway_dictionary_next_outputs fields position key value memory (Vint Int.one) after.

Record gateway_dictionary_iteration_runtime {World Event} (backend : gateway_backend World Event)
    (python : World -> python_world) (objects : World -> gateway_object_heap) : Prop := {
  gateway_runtime_dictionary_next : forall before world dictionary fields position key value cursor result after next observed,
    gateway_objects_ready (python world) (objects world) before ->
    gateway_rooted (python world) (objects world) dictionary ->
    gateway_object_values (objects world) dictionary = Some (gateway_dict_object fields) ->
    gateway_object_private (objects world) dictionary = true ->
    gateway_native_private (python world) position -> gateway_native_private (python world) key ->
    gateway_native_private (python world) value ->
    Mem.load Mint64 before position 0 = Some (Vlong cursor) ->
    Mem.valid_access before Mint64 position 0 Writable ->
    Mem.valid_access before Mptr key 0 Writable -> Mem.valid_access before Mptr value 0 Writable ->
    gateway_object_operation backend gateway_api_dict_next
      [dictionary; Vptr position Ptrofs.zero; Vptr key Ptrofs.zero; Vptr value Ptrofs.zero]
      before world result after next observed ->
    exists borrowed,
      gateway_observer_return (python world) (objects world) before (python next) (objects next) borrowed /\
      gateway_dictionary_next_outputs fields position key value borrowed result after
}.

Lemma gateway_dictionary_outputs_context {World} python objects decimal_float ledger held reserved captured original protected source environment
    fields position key value before world result after :
  @gateway_outcome_validation_context World python objects decimal_float ledger held reserved captured original protected source environment before world ->
  gateway_native_private (python world) position -> gateway_native_private (python world) key ->
  gateway_native_private (python world) value ->
  (forall position_offset, ~ protected position position_offset) ->
  (forall key_offset, ~ protected key key_offset) -> (forall value_offset, ~ protected value value_offset) ->
  gateway_dictionary_next_outputs fields position key value before result after ->
  gateway_outcome_validation_context python objects decimal_float ledger held reserved captured original protected source environment after world.
Proof.
  intros CONTEXT POSITION KEY VALUE POSITION_OUTSIDE KEY_OUTSIDE VALUE_OUTSIDE OUTPUT.
  inversion OUTPUT as [memory |memory after_position after_key final field cursor MEMBER RANGE STORE_POSITION STORE_KEY STORE_VALUE]; subst.
  - exact CONTEXT.
  - eapply gateway_validation_context_native_store with (before := after_key); [|exact VALUE |exact VALUE_OUTSIDE |exact STORE_VALUE].
    eapply gateway_validation_context_native_store with (before := after_position); [|exact KEY |exact KEY_OUTSIDE |exact STORE_KEY].
    eapply gateway_validation_context_native_store; [exact CONTEXT |exact POSITION |exact POSITION_OUTSIDE |exact STORE_POSITION].
Qed.

Theorem gateway_actual_dictionary_next_context {World Event} (backend : gateway_backend World Event)
    python objects decimal_float ledger held reserved captured original protected source environment
    (runtime : gateway_dictionary_iteration_runtime backend python objects)
    before world dictionary fields position key value cursor result after next observed :
  gateway_outcome_validation_context python objects decimal_float ledger held reserved captured original protected source environment before world ->
  gateway_rooted (python world) (objects world) dictionary ->
  gateway_object_values (objects world) dictionary = Some (gateway_dict_object fields) ->
  gateway_object_private (objects world) dictionary = true ->
  gateway_native_private (python world) position -> gateway_native_private (python world) key ->
  gateway_native_private (python world) value ->
  (forall position_offset, ~ protected position position_offset) ->
  (forall key_offset, ~ protected key key_offset) -> (forall value_offset, ~ protected value value_offset) ->
  Mem.load Mint64 before position 0 = Some (Vlong cursor) ->
  Mem.valid_access before Mint64 position 0 Writable ->
  Mem.valid_access before Mptr key 0 Writable -> Mem.valid_access before Mptr value 0 Writable ->
  gateway_object_operation backend gateway_api_dict_next
    [dictionary; Vptr position Ptrofs.zero; Vptr key Ptrofs.zero; Vptr value Ptrofs.zero]
    before world result after next observed ->
  gateway_outcome_validation_context python objects decimal_float ledger held reserved captured original protected source environment after next /\
    (result = Vint Int.zero \/ result = Vint Int.one).
Proof.
  intros CONTEXT ROOT DICTIONARY PRIVATE POSITION KEY VALUE POSITION_OUTSIDE KEY_OUTSIDE VALUE_OUTSIDE
    CURSOR POSITION_ACCESS KEY_ACCESS VALUE_ACCESS OPERATION.
  destruct (gateway_runtime_dictionary_next _ _ _ runtime before world dictionary fields position key value cursor result after next observed
    (gateway_validation_ready _ _ _ _ _ _ _ _ _ _ _ _ _ CONTEXT) ROOT DICTIONARY PRIVATE POSITION KEY VALUE CURSOR
    POSITION_ACCESS KEY_ACCESS VALUE_ACCESS OPERATION) as [borrowed [OBSERVER OUTPUT]].
  pose proof (gateway_validation_context_observer _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CONTEXT OBSERVER) as BORROWED.
  assert (LIVE_POSITION : Mem.valid_block before position) by (eapply Mem.valid_access_valid_block; eapply Mem.valid_access_implies; [exact POSITION_ACCESS |constructor]).
  assert (LIVE_KEY : Mem.valid_block before key) by (eapply Mem.valid_access_valid_block; eapply Mem.valid_access_implies; [exact KEY_ACCESS |constructor]).
  assert (LIVE_VALUE : Mem.valid_block before value) by (eapply Mem.valid_access_valid_block; eapply Mem.valid_access_implies; [exact VALUE_ACCESS |constructor]).
  split.
  - eapply gateway_dictionary_outputs_context;
      [exact BORROWED | | | |exact POSITION_OUTSIDE |exact KEY_OUTSIDE |exact VALUE_OUTSIDE |exact OUTPUT].
    all: eapply gateway_observer_native_retained; eassumption.
  - inversion OUTPUT; auto.
Qed.
