(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Releasing a decoded graph preserves a separate unpublished Outcome allocation. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayValueOwnership GatewayObjectThreads GatewayGraphSnapshots
  GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceHeld GatewayReferenceRetained GatewayReferenceThreads GatewayReferenceBalance
  GatewayPublicReferences GatewayReferenceBorrowedGraph GatewayAttachedReferences GatewayOutcomeAllocation GatewayOutcomeFields GatewayOutcomeMetadata.
Import ListNotations.
Local Close Scope lean_scope.

(* This is one SDK call's allocation/representation frame. Its input is a
   source-created private instance outside the released builtin graph. It gives
   no frame for an already-public instance or a whole cleanup/helper run. *)
Record gateway_outcome_private_reference_runtime {World Event}(backend:gateway_backend World Event)
    (python:World->python_world)(objects:World->gateway_object_heap)
    (instances:World->Values.val->option Values.val)(owned:World->Values.val->Prop):Prop:={
  gateway_outcome_private_reference:forall before world data object result after next observed,
    gateway_objects_ready(python world)(objects world)before->
    gateway_rooted(python world)(objects world)data->gateway_private_tree(objects world)data->gateway_destructible(objects world)data->
    gateway_outcome_private_cell python owned before world object->
    (0<python_native_strong(python world)(Vptr object Ptrofs.zero))%nat->
    (0<python_native_strong(python next)(Vptr object Ptrofs.zero))%nat->
    ~gateway_object_reachable(objects world)data(Vptr object Ptrofs.zero)->
    gateway_object_operation backend gateway_api_decref[data]before world result after next observed->
    gateway_outcome_private_cell python owned after next object /\
    instances next(Vptr object Ptrofs.zero)=instances world(Vptr object Ptrofs.zero) /\
    Mem.unchanged_on(gateway_outcome_cell_region object)before after
}.

Definition gateway_reference_without_held ticket(held:list gateway_held_value):list gateway_held_value:=
  filter(fun captured=>negb(Nat.eqb(gateway_held_ticket captured)ticket))held.

Lemma gateway_reference_without_held_kept ticket held captured:
  In captured(gateway_reference_without_held ticket held)->In captured held /\gateway_held_ticket captured<>ticket.
Proof.
  unfold gateway_reference_without_held;rewrite filter_In;intros[MEMBER DIFFERENT];split;[exact MEMBER|].
  apply Bool.negb_true_iff in DIFFERENT;apply Nat.eqb_neq;exact DIFFERENT.
Qed.

Lemma gateway_reference_without_held_scope {World}python objects decimal_float ledger held world ticket:
  @gateway_reference_scope World python objects decimal_float ledger held world->
  gateway_reference_scope python objects decimal_float ledger(gateway_reference_without_held ticket held)world.
Proof.
  intros[FIT HELD];split;[exact FIT|]. apply Forall_forall;intros captured MEMBER;apply Forall_forall with(x:=captured)in HELD;
    [exact HELD|exact(proj1(gateway_reference_without_held_kept _ _ _ MEMBER))].
Qed.

Theorem gateway_new_allocation_outside_captured_graph {World}(python:World->python_world)(objects:World->gateway_object_heap)before world next object original initial:
  @gateway_objects_ready(python world)(objects world)before->gateway_rooted(python world)(objects world)original->
  ~Mem.valid_block before object->gateway_destructible initial original->
  gateway_graph_snapshot initial(objects world)original->gateway_graph_snapshot initial(objects next)original->
  ~gateway_object_reachable(objects next)original(Vptr object Ptrofs.zero).
Proof.
  intros READY ROOT FRESH SAFE EARLIER LATER REACHED.
  pose proof(gateway_graph_snapshot_backward _ _ _ SAFE LATER _ REACHED)as OLD.
  pose proof(gateway_graph_snapshot_forward _ _ _ EARLIER _ OLD)as CURRENT.
  assert(LIVE:gateway_rooted(python world)(objects world)(Vptr object Ptrofs.zero))
    by(eapply gateway_reachable_rooted;eassumption).
  destruct(proj2(proj2(proj2(proj2(proj1 READY))))(Vptr object Ptrofs.zero)LIVE)as[block[offset[SAME POINTER]]].
  injection SAME as SAME OFFSET;subst block offset.
  apply FRESH;apply Mem.weak_valid_pointer_spec in POINTER;destruct POINTER as[POSITION|POSITION];
    apply Mem.valid_pointer_nonempty_perm in POSITION;eapply Mem.perm_valid_block;exact POSITION.
Qed.

Theorem gateway_actual_decoded_graph_release_keeps_outcome {World Event}(backend:gateway_backend World Event)
    python objects instances owned decimal_float
    (references:gateway_public_reference_runtime backend python objects)
    (cells:gateway_outcome_private_reference_runtime backend python objects instances owned)
    ledger data_place data_ticket data object outcome_place outcome_ticket copy_place copy_ticket copy fields wires metadata_field metadata wire
    class held reserved before world result after next observed:
  gateway_reference_ledger_well_formed ledger->gateway_reference_scope python objects decimal_float ledger held world->
  gateway_reference_owns ledger data_place data_ticket data->
  gateway_reference_owns ledger outcome_place outcome_ticket(Vptr object Ptrofs.zero)->
  gateway_reference_owns ledger copy_place copy_ticket copy->outcome_ticket<>data_ticket->copy_ticket<>data_ticket->
  gateway_objects_ready(python world)(objects world)before->gateway_private_tree(objects world)data->gateway_destructible(objects world)data->
  gateway_outcome_private_cell python owned before world object->Mem.load AST.Mptr before object 16=Some copy->
  instances world(Vptr object Ptrofs.zero)=Some class->~gateway_object_reachable(objects world)data(Vptr object Ptrofs.zero)->
  gateway_outcome_fields_view python objects decimal_float copy fields wires world->
  gateway_outcome_metadata_view python objects decimal_float copy fields metadata_field metadata wire world->
  (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count ledger pointer<=python_native_strong(python world)pointer)%nat)->
  gateway_object_operation backend gateway_api_decref[data]before world result after next observed->
  exists final,
    gateway_reference_apply(gateway_reference_release data_place data)(gateway_reference_valid ledger)=gateway_reference_valid final /\
    gateway_reference_ledger_well_formed final /\gateway_reference_scope python objects decimal_float final(gateway_reference_without_held data_ticket held)next /\
    gateway_reference_owns final outcome_place outcome_ticket(Vptr object Ptrofs.zero) /\gateway_reference_owns final copy_place copy_ticket copy /\
    gateway_objects_ready(python next)(objects next)after /\gateway_outcome_private_cell python owned after next object /\
    Mem.load AST.Mptr after object 16=Some copy /\instances next(Vptr object Ptrofs.zero)=Some class /\
    gateway_outcome_fields_view python objects decimal_float copy fields wires next /\
    gateway_outcome_metadata_view python objects decimal_float copy fields metadata_field metadata wire next /\
    (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count final pointer<=python_native_strong(python next)pointer)%nat).
Proof.
  intros WELL SCOPE DATA OUTCOME COPY DIFFERENT COPY_DIFFERENT READY PRIVATE SAFE CELL LOAD CLASS OUTSIDE FIELDS METADATA BUDGET OPERATION.
  pose proof(gateway_reference_without_held_scope python objects decimal_float ledger held world data_ticket SCOPE)as FILTERED.
  destruct(gateway_public_release_keeps_independent_graphs backend python objects decimal_float references ledger data_place data_ticket data
    (gateway_reference_without_held data_ticket held)before world result after next observed WELL(proj1 SCOPE)DATA
    (gateway_normal_attached _ _ _ READY)(proj2 FILTERED)
    ltac:(intros captured MEMBER;exact(proj2(gateway_reference_without_held_kept _ _ _ MEMBER)))OPERATION)
    as(final &RELEASE &FINAL_WELL &FIT &HELD &EFFECT &RETAINED).
  assert(FINAL_OUTCOME:gateway_reference_owns final outcome_place outcome_ticket(Vptr object Ptrofs.zero))by(apply RETAINED;assumption).
  assert(FINAL_COPY:gateway_reference_owns final copy_place copy_ticket copy)by(apply RETAINED;assumption).
  assert(OUTCOME_ROOT:gateway_rooted(python world)(objects world)(Vptr object Ptrofs.zero))by(eapply gateway_reference_owned_rooted;[exact(proj1 SCOPE)|exact OUTCOME]).
  assert(DATA_ROOT:gateway_rooted(python world)(objects world)data)by(eapply gateway_reference_owned_rooted;[exact(proj1 SCOPE)|exact DATA]).
  assert(POSITIVE:(0<python_native_strong(python world)(Vptr object Ptrofs.zero))%nat).
  { pose proof(gateway_reference_owned_count_positive _ _ _ _ OUTCOME);pose proof(proj1 SCOPE(Vptr object Ptrofs.zero));lia. }
  assert(NEXT_POSITIVE:(0<python_native_strong(python next)(Vptr object Ptrofs.zero))%nat).
  { pose proof(gateway_reference_owned_count_positive _ _ _ _ FINAL_OUTCOME);specialize(FIT(Vptr object Ptrofs.zero));lia. }
  assert(COPY_POSITIVE:(0<python_native_strong(python next)copy)%nat).
  { pose proof(gateway_reference_owned_count_positive _ _ _ _ FINAL_COPY);specialize(FIT copy);lia. }
  destruct(gateway_outcome_private_reference _ _ _ _ _ cells before world data object result after next observed
    READY DATA_ROOT PRIVATE SAFE CELL POSITIVE NEXT_POSITIVE OUTSIDE OPERATION)as[NEXT_CELL[NEXT_CLASS FRAME]].
  assert(NEXT_READY:gateway_objects_ready(python next)(objects next)after).
  { destruct(gateway_attached_reference_ready _ _ _ _ _ _ _ EFFECT)as[VALID GIL];split;[exact VALID|]. split;[exact GIL|].
    rewrite(gateway_attached_reference_pending _ _ _ _ _ _ _ EFFECT);exact(proj2(proj2 READY)). }
  exists final;split;[exact RELEASE|]. split;[exact FINAL_WELL|]. split;[exact(conj FIT HELD)|].
  split;[exact FINAL_OUTCOME|]. split;[exact FINAL_COPY|]. split;[exact NEXT_READY|]. split;[exact NEXT_CELL|]. split.
  - eapply Mem.load_unchanged_on;[exact FRAME|intros;split;[reflexivity|exact H]|exact LOAD].
  - split;[rewrite NEXT_CLASS;exact CLASS|]. split.
    + eapply gateway_outcome_fields_view_kept;[exact FIELDS|exact COPY_POSITIVE|
        exact(gateway_attached_reference_values _ _ _ _ _ _ _ EFFECT)|exact(gateway_attached_reference_privacy _ _ _ _ _ _ _ EFFECT)].
    + split.
      * eapply gateway_outcome_metadata_view_kept;[exact METADATA|exact COPY_POSITIVE|
          exact(gateway_attached_reference_values _ _ _ _ _ _ _ EFFECT)|exact(gateway_attached_reference_privacy _ _ _ _ _ _ _ EFFECT)].
      * eapply gateway_reference_balance_reservations;[exact BUDGET|].
        eapply gateway_reference_balance_release;[exact WELL|exact DATA|exact RELEASE|
          exact(gateway_attached_reference_owned _ _ _ _ _ _ _ EFFECT)|exact(gateway_attached_reference_others _ _ _ _ _ _ _ EFFECT)].
Qed.
