(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual fresh private copy supplies all received field and metadata views. *)
From Stdlib Require Import List Lia.
From compcert Require Import Values Memory.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayValue GatewayValueOwnership
  GatewayGraphSnapshots GatewayObjectThreads GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceRuntime
  GatewayReferenceHeld GatewayReferenceThreads GatewayOutcomeCopyPool GatewayOutcomeFields GatewayOutcomeMetadata.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_actual_private_outcome_copy_views {World Event}(backend:gateway_backend World Event)
    python objects decimal_float(constructors:gateway_objects_runtime backend python objects decimal_float)
    ledger owner held reserved original fields wires metadata_field metadata wire before world result after next observed:
  gateway_reference_ledger_well_formed ledger->
  (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count ledger pointer<=python_native_strong(python world)pointer)%nat)->
  gateway_reference_take owner(gateway_reference_entries ledger)=None->
  gateway_reference_held python objects decimal_float ledger held world->gateway_objects_ready(python world)(objects world)before->
  (0<python_native_strong(python world)original)%nat->
  gateway_object_values(objects world)original=Some(gateway_dict_object fields)->
  gateway_private_tree(objects world)original->gateway_destructible(objects world)original->
  gateway_dictionary_heap decimal_float(objects world)fields wires->
  gateway_dictionary_lookup gateway_outcome_json_name fields=Some metadata_field->gateway_dictionary_value metadata_field=metadata->
  gateway_value_heap decimal_float(objects world)metadata wire->
  gateway_object_operation backend gateway_api_dict_copy[original]before world result after next observed->result<>Vnullptr->
  exists final,
    gateway_reference_apply(gateway_reference_mint owner result)(gateway_reference_valid ledger)=gateway_reference_valid final /\
    gateway_reference_ledger_well_formed final /\gateway_reference_owns final owner(gateway_reference_next ledger)result /\
    gateway_reference_scope python objects decimal_float final held next /\gateway_objects_ready(python next)(objects next)after /\
    gateway_outcome_fields_view python objects decimal_float result fields wires next /\
    gateway_outcome_metadata_view python objects decimal_float result fields metadata_field metadata wire next /\
    (forall field,In field fields->
      ~gateway_object_reachable(objects next)(gateway_dictionary_key field)result /\
      ~gateway_object_reachable(objects next)(gateway_dictionary_value field)result) /\
    ~gateway_object_reachable(objects next)metadata result /\
    gateway_graph_snapshot(objects world)(objects next)original /\
    (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count final pointer<=python_native_strong(python next)pointer)%nat) /\
    gateway_constructor_return(python world)(objects world)before result(python next)(objects next)after(gateway_dict_object fields).
Proof.
  intros WELL BUDGET VACANT HELD READY OWNED VALUE PRIVATE DESTROY RECEIVED METADATA META_VALUE WIRE OPERATION NONNULL.
  assert(ROOT:gateway_rooted(python world)(objects world)original)by(constructor;exact OWNED).
  destruct(gateway_actual_private_outcome_copy_pool backend python objects decimal_float constructors ledger owner held reserved original fields
    before world result after next observed WELL BUDGET VACANT HELD READY ROOT VALUE ltac:(apply PRIVATE;constructor)OPERATION NONNULL)
    as(final &MINT &FINAL_WELL &FINAL_OWNED &FINAL_HELD &FINAL_BUDGET &RETURN).
  assert(FIT:gateway_reference_counts_fit final(python next))by(intro pointer;specialize(FINAL_BUDGET pointer);lia).
  pose proof(gateway_constructor_reference_credit _ _ _ _ _ _ _ _ RETURN)as CREDIT.
  destruct(gateway_constructor_all_private_frames _ _ _ _ _ _ _ _ RETURN)as[VALUES PRIVACY].
  assert(EFFECT:gateway_reference_thread_effect python objects world next).
  { constructor;[|exact VALUES|exact PRIVACY]. intro pointer.
    destruct(Val.eq pointer result)as[SAME|OTHER];[subst pointer;rewrite(gateway_reference_credit_target _ _ _ CREDIT);lia|
      rewrite(gateway_reference_credit_other _ _ _ CREDIT pointer OTHER);lia]. }
  assert(INITIAL_FIELDS:gateway_outcome_fields_view python objects decimal_float original fields wires world).
  { constructor;[exact OWNED|exact VALUE|apply PRIVATE;constructor|].
    eapply gateway_received_dictionary_field_views;eassumption. }
  assert(FINAL_FIELDS:gateway_outcome_fields_view python objects decimal_float original fields wires next)
    by(eapply gateway_outcome_fields_view_frame;eassumption).
  assert(COPY_OWNED:(0<python_native_strong(python next)result)%nat).
  { pose proof(gateway_reference_owned_count_positive _ _ _ _ FINAL_OWNED);specialize(FIT result);lia. }
  assert(NEXT_ROOT:gateway_rooted(python next)(objects next)original).
  { constructor;pose proof(gateway_reference_thread_counts _ _ _ _ EFFECT original);lia. }
  assert(MEMBER:In metadata_field fields)by(exact(proj1(gateway_dictionary_lookup_member _ _ _ METADATA))).
  destruct(gateway_outcome_child_subtree _ _ _ _ metadata VALUE MEMBER ltac:(right;symmetry;exact META_VALUE)PRIVATE DESTROY)
    as[META_PRIVATE META_DESTROY].
  assert(INITIAL_METADATA:gateway_outcome_metadata_view python objects decimal_float original fields metadata_field metadata wire world).
  { constructor;[exact OWNED|exact VALUE|apply PRIVATE;constructor|exact METADATA|exact META_VALUE|exact META_PRIVATE|exact META_DESTROY|exact WIRE]. }
  assert(FINAL_METADATA:gateway_outcome_metadata_view python objects decimal_float original fields metadata_field metadata wire next)
    by(eapply gateway_outcome_metadata_view_frame;eassumption).
  assert(SNAPSHOT:gateway_graph_snapshot(objects world)(objects next)original).
  { eapply gateway_graph_snapshot_retained;[exact PRIVATE|exact DESTROY|exact ROOT|exact NEXT_ROOT|exact VALUES|exact PRIVACY|
      apply gateway_graph_snapshot_refl]. }
  assert(OUTSIDE:~gateway_object_reachable(objects next)original result).
  { intro REACHED;eapply(gateway_outcome_copy_not_in_original _ _ _ _ _ _ _ _ _ READY ROOT RETURN).
    eapply gateway_graph_snapshot_backward;[exact DESTROY|exact SNAPSHOT|exact REACHED]. }
  assert(FIELD_CHILDREN:forall field,In field fields->
    gateway_object_reachable(objects next)original(gateway_dictionary_key field) /\
    gateway_object_reachable(objects next)original(gateway_dictionary_value field)).
  { intros field FIELD;split;eapply gateway_reachable_child;[constructor|exact(gateway_outcome_fields_value _ _ _ _ _ _ _ FINAL_FIELDS)| |
      constructor|exact(gateway_outcome_fields_value _ _ _ _ _ _ _ FINAL_FIELDS)|].
    all:unfold gateway_object_children,gateway_dictionary_children;apply in_flat_map;exists field;split;[exact FIELD|];cbn;auto. }
  exists final;split;[exact MINT|]. split;[exact FINAL_WELL|]. split;[exact FINAL_OWNED|].
  split;[exact(conj FIT FINAL_HELD)|]. split;[exact(conj(gateway_constructor_valid _ _ _ _ _ _ _ _ RETURN)
    (conj(gateway_constructor_gil _ _ _ _ _ _ _ _ RETURN)(gateway_constructor_clear _ _ _ _ _ _ _ _ RETURN)))|]. split.
  - constructor;[exact COPY_OWNED|exact(gateway_constructor_value _ _ _ _ _ _ _ _ RETURN)|
      exact(gateway_constructor_private _ _ _ _ _ _ _ _ RETURN)|exact(gateway_outcome_fields_received _ _ _ _ _ _ _ FINAL_FIELDS)].
  - split.
    + constructor;[exact COPY_OWNED|exact(gateway_constructor_value _ _ _ _ _ _ _ _ RETURN)|
        exact(gateway_constructor_private _ _ _ _ _ _ _ _ RETURN)|exact METADATA|exact META_VALUE|
        exact(gateway_outcome_view_tree _ _ _ _ _ _ _ _ _ FINAL_METADATA)|
        exact(gateway_outcome_view_destructible _ _ _ _ _ _ _ _ _ FINAL_METADATA)|
        exact(gateway_outcome_view_wire _ _ _ _ _ _ _ _ _ FINAL_METADATA)].
    + split.
      * intros field FIELD;destruct(FIELD_CHILDREN field FIELD)as[KEY ITEM];split;intro REACHED.
        -- apply OUTSIDE;eapply gateway_reachable_trans;[exact KEY|exact REACHED].
        -- apply OUTSIDE;eapply gateway_reachable_trans;[exact ITEM|exact REACHED].
      * split.
        -- intro REACHED;apply OUTSIDE;eapply gateway_reachable_trans;[|exact REACHED].
           rewrite<-META_VALUE;exact(proj2(FIELD_CHILDREN metadata_field MEMBER)).
        -- exact(conj SNAPSHOT(conj FINAL_BUDGET RETURN)).
Qed.
