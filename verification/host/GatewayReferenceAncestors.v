(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Constructor freshness and retained snapshots produce the exact
   mutable ancestor exclusions used by recursive container source consumers. *)
From Stdlib Require Import List Lia.
From compcert Require Import Values.
From HostGateway Require Import GatewayPython GatewayObjects GatewayReferences GatewayValue GatewayObjectThreads GatewayGraphSnapshots
  GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceThreads GatewayReferenceGraphCapture
  GatewayReferenceContainerScope GatewayReferenceValueProperties GatewayReferenceSnapshotInputs.
Import ListNotations.

Definition gateway_reference_mutable_target held pointer:Prop:=
  exists captured wire initial value,In captured held /\gateway_held_view captured=gateway_held_graph_value wire initial /\
    gateway_object_values initial(gateway_held_object captured)=Some value /\gateway_mutable_container value /\
    pointer=gateway_held_object captured.

Lemma gateway_reference_avoids_targets held heap root:
  gateway_reference_avoids_old_mutable held heap root<->
  forall pointer,gateway_reference_mutable_target held pointer->~gateway_object_reachable heap root pointer.
Proof.
  split.
  - intros AVOID pointer[captured[wire[initial[value[MEMBER[VIEW[LOOKUP[MUTABLE SAME]]]]]]]];subst pointer.
    eapply AVOID;eassumption.
  - intros AVOID captured MEMBER wire initial VIEW value LOOKUP MUTABLE.
    apply AVOID;exists captured,wire,initial,value;repeat split;assumption||reflexivity.
Qed.

Lemma gateway_reference_target_sublist held selected pointer:
  (forall captured,In captured selected->In captured held)->gateway_reference_mutable_target selected pointer->
  gateway_reference_mutable_target held pointer.
Proof.
  intros SUBSET[captured[wire[initial[value[MEMBER REST]]]]];exists captured,wire,initial,value;split;[apply SUBSET;exact MEMBER|exact REST].
Qed.

Theorem gateway_reference_fresh_snapshot_exclusion {World}python objects decimal_float ledger held world pointer:
  @gateway_reference_scope World python objects decimal_float ledger held world->gateway_reference_graphs_only held->
  (forall captured,In captured held->~gateway_object_reachable(objects world)(gateway_held_object captured)pointer)->
  gateway_reference_snapshots_avoid held pointer.
Proof.
  intros SCOPE GRAPHS OUTSIDE captured MEMBER wire initial VIEW REACHED.
  destruct captured as[ticket root description];cbn in VIEW|-*;subst description.
  destruct(gateway_reference_graph_snapshot _ _ _ _ _ _ _ _ _ _ SCOPE MEMBER)as[DESTROY SNAPSHOT].
  apply(OUTSIDE _ MEMBER);eapply gateway_graph_snapshot_forward;[exact SNAPSHOT|exact REACHED].
Qed.

Theorem gateway_reference_scope_ticket_bound {World}python objects decimal_float ledger held world captured:
  gateway_reference_ledger_well_formed ledger->@gateway_reference_scope World python objects decimal_float ledger held world->
  In captured held->(gateway_held_ticket captured<gateway_reference_next ledger)%nat.
Proof.
  intros[UNIQUE[OWNERS BOUNDS]]SCOPE MEMBER.
  destruct(gateway_reference_capture_member _ _ _ _ _ _ _ SCOPE MEMBER)as[[owner OWNED]REST].
  exact(proj1(Forall_forall _ _)BOUNDS _ OWNED).
Qed.

Lemma gateway_reference_parent_target held ticket parent values initial pointers:
  gateway_object_values initial parent=Some(gateway_list_object pointers)->
  gateway_reference_mutable_target
    (held++[gateway_reference_graph_capture ticket parent
      (GatewayImport.LeanCage_Host_GatewayResponseCode_Value_array(GatewayValue.gateway_wire_values values))initial])parent.
Proof.
  intro LOOKUP;exists(gateway_reference_graph_capture ticket parent
    (GatewayImport.LeanCage_Host_GatewayResponseCode_Value_array(gateway_wire_values values))initial),
    (GatewayImport.LeanCage_Host_GatewayResponseCode_Value_array(gateway_wire_values values)),initial,(gateway_list_object pointers);split.
  - apply in_or_app;right;left;reflexivity.
  - split;[reflexivity|]. split;[exact LOOKUP|]. split;[exact I|reflexivity].
Qed.
