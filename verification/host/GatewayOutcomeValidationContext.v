(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Validation retains the received private graph and older source credits. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Clight.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayValue GatewayValueFrame
  GatewayObjectDiscipline GatewayObjectThreads GatewayThreadRuntime GatewayStreamInterface GatewayLocalRuntime
  GatewayGraphSnapshots GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceHeld GatewayReferenceThreads
  GatewayReferenceObservers GatewayReferenceDictionarySnapshots GatewayOutcomeMetadata GatewayFramedRuntime GatewayNativeRegions.
Import ListNotations.
Local Close Scope lean_scope.

Record gateway_outcome_validation_context {World} (python : World -> python_world)
    (objects : World -> gateway_object_heap) decimal_float ledger held reserved captured original protected source environment memory world : Prop := {
  gateway_validation_ready : gateway_objects_ready (python world) (objects world) memory;
  gateway_validation_environment : gateway_native_environment
    (fun current object => gateway_native_private (python current) object) world memory environment;
  gateway_validation_scope : gateway_reference_scope python objects decimal_float ledger held world;
  gateway_validation_budget : forall pointer,
    (count_occ Val.eq reserved pointer + gateway_reference_count ledger pointer <= python_native_strong (python world) pointer)%nat;
  gateway_validation_credit : (0 < python_native_strong (python world) original)%nat;
  gateway_validation_private : gateway_private_tree (objects world) original;
  gateway_validation_destructible : gateway_destructible (objects world) original;
  gateway_validation_snapshot : gateway_graph_snapshot captured (objects world) original;
  gateway_validation_regions : gateway_native_region_owned
    (fun current object => gateway_native_private (python current) object) protected memory world;
  gateway_validation_region_frame : Mem.unchanged_on protected source memory;
  gateway_validation_slots : forall identifier object ty, environment ! identifier = Some (object, ty) ->
    Mem.valid_access memory Mint64 object 0 Writable;
  gateway_validation_slots_outside : forall identifier object ty, environment ! identifier = Some (object, ty) ->
    forall position, ~ protected object position
}.

Theorem gateway_validation_context_effect {World} python objects decimal_float ledger held reserved captured original protected source environment
    before world after next :
  @gateway_outcome_validation_context World python objects decimal_float ledger held reserved captured original protected source environment before world ->
  gateway_objects_ready (python next) (objects next) after ->
  gateway_reference_thread_effect python objects world next ->
  python_private_frame (python world) before after ->
  (forall object, Mem.valid_block before object -> gateway_native_private (python world) object -> gateway_native_private (python next) object) ->
  gateway_outcome_validation_context python objects decimal_float ledger held reserved captured original protected source environment after next.
Proof.
  intros CONTEXT READY EFFECT FRAME RETAINED.
  destruct CONTEXT as [BEFORE ENVIRONMENT SCOPE BUDGET CREDIT PRIVATE DESTROY SNAPSHOT REGIONS REGION_FRAME SLOTS OUTSIDE].
  assert (NEXT_CREDIT : (0 < python_native_strong (python next) original)%nat).
  { pose proof (gateway_reference_thread_counts _ _ _ _ EFFECT original); lia. }
  assert (ROOT : gateway_rooted (python world) (objects world) original) by (constructor; exact CREDIT).
  assert (NEXT_ROOT : gateway_rooted (python next) (objects next) original) by (constructor; exact NEXT_CREDIT).
  destruct (gateway_private_tree_preserved _ _ _ _ _ PRIVATE DESTROY ROOT NEXT_ROOT
    (gateway_reference_thread_values _ _ _ _ EFFECT) (gateway_reference_thread_privacy _ _ _ _ EFFECT)) as [NEXT_PRIVATE NEXT_DESTROY].
  constructor; [exact READY | | | |exact NEXT_CREDIT |exact NEXT_PRIVATE |exact NEXT_DESTROY | | | | |exact OUTSIDE].
  - intros identifier object ty LOOK; destruct (ENVIRONMENT identifier object ty LOOK) as [LIVE NATIVE]; split.
    + eapply Mem.valid_block_unchanged_on; [exact FRAME |exact LIVE].
    + apply RETAINED; assumption.
  - eapply gateway_reference_scope_thread_effect; eassumption.
  - intro pointer; specialize (BUDGET pointer); pose proof (gateway_reference_thread_counts _ _ _ _ EFFECT pointer); lia.
  - exact (gateway_graph_snapshot_retained (python world) (objects world) (python next) (objects next) captured original
      PRIVATE DESTROY ROOT NEXT_ROOT (gateway_reference_thread_values _ _ _ _ EFFECT)
      (gateway_reference_thread_privacy _ _ _ _ EFFECT) SNAPSHOT).
  - intros object position MEMBER; destruct (REGIONS object position MEMBER) as [LIVE NATIVE]; split.
    + eapply Mem.valid_block_unchanged_on; eassumption.
    + apply RETAINED; assumption.
  - eapply Mem.unchanged_on_trans; [exact REGION_FRAME |].
    eapply Mem.unchanged_on_implies; [exact FRAME |].
    intros object position MEMBER LIVE; exact (proj2 (REGIONS object position MEMBER)).
  - intros identifier object ty LOOK; destruct (SLOTS identifier object ty LOOK) as [PERMISSION ALIGN]; split; [|exact ALIGN].
    intros position RANGE; eapply Mem.perm_unchanged_on; [exact FRAME | |apply PERMISSION; exact RANGE].
    exact (proj2 (ENVIRONMENT identifier object ty LOOK)).
Qed.

Theorem gateway_validation_context_observer {World} python objects decimal_float ledger held reserved captured original protected source environment
    before world after next :
  @gateway_outcome_validation_context World python objects decimal_float ledger held reserved captured original protected source environment before world ->
  gateway_observer_return (python world) (objects world) before (python next) (objects next) after ->
  gateway_outcome_validation_context python objects decimal_float ledger held reserved captured original protected source environment after next.
Proof.
  intros CONTEXT OBSERVER.
  assert (EFFECT : gateway_reference_thread_effect python objects world next).
  { constructor.
    - intro pointer; rewrite (gateway_observer_references _ _ _ _ _ _ OBSERVER pointer) by (intro EMPTY; inversion EMPTY); lia.
    - exact (gateway_observer_values _ _ _ _ _ _ OBSERVER).
    - exact (gateway_observer_privacy _ _ _ _ _ _ OBSERVER). }
  eapply gateway_validation_context_effect;
    [exact CONTEXT |exact (gateway_observer_ready _ _ _ _ _ _ OBSERVER) |exact EFFECT |
     exact (gateway_observer_native _ _ _ _ _ _ OBSERVER) |
     exact (gateway_observer_native_retained _ _ _ _ _ _ OBSERVER)].
Qed.

Theorem gateway_validation_context_native_store {World} python objects decimal_float ledger held reserved captured original protected source environment
    before world after chunk object offset value :
  @gateway_outcome_validation_context World python objects decimal_float ledger held reserved captured original protected source environment before world ->
  gateway_native_private (python world) object -> (forall position, ~ protected object position) ->
  Mem.store chunk before object offset value = Some after ->
  gateway_outcome_validation_context python objects decimal_float ledger held reserved captured original protected source environment after world.
Proof.
  intros CONTEXT NATIVE UNPROTECTED STORE;
    destruct CONTEXT as [READY ENVIRONMENT SCOPE BUDGET CREDIT PRIVATE DESTROY SNAPSHOT REGIONS REGION_FRAME SLOTS OUTSIDE].
  constructor; try assumption.
  - eapply gateway_owned_native_store_ready; eassumption.
  - intros identifier block ty LOOK; destruct (ENVIRONMENT identifier block ty LOOK) as [LIVE PRIVATE_BLOCK].
    split; [eapply Mem.store_valid_block_1; eassumption |exact PRIVATE_BLOCK].
  - intros block position MEMBER; destruct (REGIONS block position MEMBER) as [LIVE PRIVATE_BLOCK].
    split; [eapply Mem.store_valid_block_1; eassumption |exact PRIVATE_BLOCK].
  - eapply Mem.unchanged_on_trans; [exact REGION_FRAME |].
    eapply Mem.store_unchanged_on; [exact STORE |].
    intros position RANGE MEMBER; exact (UNPROTECTED position MEMBER).
  - intros; eapply Mem.store_valid_access_1; [exact STORE |eapply SLOTS; eassumption].
Qed.

Theorem gateway_validation_context_ambient {World Event} (backend : gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime : gateway_thread_runtime backend io (fun current object => gateway_native_private (python current) object) stable
      (gateway_python_discipline python objects detached) thread_errno)
    (references : gateway_reference_thread_contract backend (fun current object => gateway_native_private (python current) object) stable
      (gateway_python_discipline python objects detached) heap_allocation python objects)
    ledger held reserved captured original protected source environment :
  gateway_ambient_closed backend
    (gateway_outcome_validation_context python objects decimal_float ledger held reserved captured original protected source environment).
Proof.
  intros before world after next CONTEXT INTERFERENCE.
  pose proof (gateway_validation_ready _ _ _ _ _ _ _ _ _ _ _ _ _ CONTEXT) as READY.
  destruct (gateway_thread_ambient _ _ _ _ _ _ runtime None before world after next READY INTERFERENCE) as [NORMAL [ACCESS FRAME]].
  pose proof (@gateway_reference_thread_ambient World Event backend
    (fun current object => gateway_native_private (python current) object) stable
    (gateway_python_discipline python objects detached) heap_allocation python objects references
    None before world after next READY INTERFERENCE) as EFFECT.
  assert (PRIVATE_FRAME : python_private_frame (python world) before after).
  { eapply Mem.unchanged_on_implies; [exact FRAME |].
    intros object position PRIVATE; split; [left; exact PRIVATE |cbn; tauto]. }
  eapply gateway_validation_context_effect; [exact CONTEXT |exact NORMAL |exact EFFECT |exact PRIVATE_FRAME |].
  intros object LIVE NATIVE; exact (proj1 ACCESS object LIVE NATIVE).
Qed.

(* Pure receive inputs are transported by the same retained graph; only the
   subsequent actual SDK operation can create the private dictionary copy. *)
Theorem gateway_validation_received_inputs {World} python objects decimal_float ledger held reserved captured original protected source environment
    memory world fields wires metadata_field metadata wire :
  @gateway_outcome_validation_context World python objects decimal_float ledger held reserved captured original protected source environment memory world ->
  gateway_object_values captured original = Some (gateway_dict_object fields) ->
  gateway_dictionary_heap decimal_float captured fields wires ->
  gateway_dictionary_lookup gateway_outcome_json_name fields = Some metadata_field ->
  gateway_dictionary_value metadata_field = metadata -> gateway_value_heap decimal_float captured metadata wire ->
  gateway_object_values (objects world) original = Some (gateway_dict_object fields) /\
    gateway_dictionary_heap decimal_float (objects world) fields wires /\ gateway_value_heap decimal_float (objects world) metadata wire.
Proof.
  intros CONTEXT VALUE RECEIVED LOOKUP META WIRE.
  pose proof (gateway_validation_snapshot _ _ _ _ _ _ _ _ _ _ _ _ _ CONTEXT) as SNAPSHOT.
  split; [rewrite SNAPSHOT by constructor; exact VALUE |split].
  - eapply gateway_graph_snapshot_dictionary; eassumption.
  - destruct (gateway_value_tree_map decimal_float captured (objects world)) as [MAP _].
    eapply MAP with (root := original); [exact WIRE | |].
    + eapply gateway_reachable_child; [constructor |exact VALUE |].
      unfold gateway_object_children, gateway_dictionary_children; apply in_flat_map; exists metadata_field; split.
      * exact (proj1 (gateway_dictionary_lookup_member _ _ _ LOOKUP)).
      * rewrite META; cbn; auto.
    + intros pointer value REACHED DESCRIPTION; rewrite SNAPSHOT by exact REACHED; exact DESCRIPTION.
Qed.
