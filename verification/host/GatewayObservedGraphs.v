(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Public received snapshots use actual operation frames, not private-tree authority. *)
From Stdlib Require Import List PeanoNat.
From compcert Require Import Values.
From HostGateway Require Import GatewayPython GatewayObjects GatewayReferences GatewayValue GatewayValueFrame GatewayGraphSnapshots
  GatewayObjectThreads GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceMoves.
Import ListNotations.
Local Close Scope lean_scope.

Definition gateway_reference_observed {World}(objects:World->gateway_object_heap)
    decimal_float ledger(captured:list gateway_held_value)world:Prop:=
  Forall(fun item=>(exists place,gateway_reference_owns ledger place(gateway_held_ticket item)(gateway_held_object item)) /\
    gateway_held_description_holds decimal_float(objects world)(gateway_held_object item)(gateway_held_view item))captured.

Theorem gateway_observed_description_frame decimal_float heap next_heap root description:
  gateway_held_description_holds decimal_float heap root description->
  gateway_reachable_values_frame heap next_heap root->
  gateway_held_description_holds decimal_float next_heap root description.
Proof.
  intros DESCRIPTION FRAME;destruct description as[wire|scalar|wire initial];cbn in DESCRIPTION|-*.
  - eapply(proj1(gateway_value_tree_map decimal_float heap next_heap));[exact DESCRIPTION|constructor|exact FRAME].
  - destruct DESCRIPTION as[LOOKUP CHILDREN];split;[eapply FRAME;[constructor|exact LOOKUP]|exact CHILDREN].
  - destruct DESCRIPTION as[WIRE[DESTROY SNAPSHOT]];split.
    + eapply(proj1(gateway_value_tree_map decimal_float heap next_heap));[exact WIRE|constructor|exact FRAME].
    + split;[exact DESTROY|]. intros object REACHED.
      destruct(DESTROY object REACHED)as(value &kind &LOOKUP &KIND &SAFE).
      rewrite LOOKUP;eapply FRAME.
      * eapply gateway_graph_snapshot_forward;[exact SNAPSHOT|exact REACHED].
      * rewrite SNAPSHOT;assumption.
Qed.

Theorem gateway_reference_observed_frame {World}(objects:World->gateway_object_heap)
    decimal_float ledger next_ledger captured world next:
  gateway_reference_observed objects decimal_float ledger captured world->
  (forall item,In item captured->exists place,
    gateway_reference_owns next_ledger place(gateway_held_ticket item)(gateway_held_object item))->
  (forall item,In item captured->gateway_reachable_values_frame(objects world)(objects next)(gateway_held_object item))->
  gateway_reference_observed objects decimal_float next_ledger captured next.
Proof.
  intros OBSERVED OWNED FRAME;apply Forall_forall;intros item MEMBER.
  pose proof(proj1(Forall_forall _ _)OBSERVED item MEMBER)as[BEFORE DESCRIPTION].
  split;[apply OWNED;exact MEMBER|]. eapply gateway_observed_description_frame;[exact DESCRIPTION|apply FRAME;exact MEMBER].
Qed.

Theorem gateway_reference_observed_move {World}(objects:World->gateway_object_heap)
    decimal_float ledger from to ticket pointer captured world:
  gateway_reference_ledger_well_formed ledger->gateway_reference_owns ledger from ticket pointer->
  gateway_reference_take to(gateway_reference_entries ledger)=None->
  gateway_reference_observed objects decimal_float ledger captured world->
  exists final,
    gateway_reference_apply(gateway_reference_move from to)(gateway_reference_valid ledger)=gateway_reference_valid final /\
    gateway_reference_ledger_well_formed final /\gateway_reference_owns final to ticket pointer /\
    gateway_reference_observed objects decimal_float final captured world /\
    (forall value,gateway_reference_count final value=gateway_reference_count ledger value).
Proof.
  intros WELL OWNED VACANT OBSERVED.
  destruct(gateway_reference_move_selected ledger from to ticket pointer WELL OWNED)
    as(final &MOVE &FINAL_WELL &RESULT &RETAINED &COUNTS).
  - intros item MEMBER OWNER;exfalso;exact(proj1(gateway_reference_take_none _ _)VACANT item MEMBER OWNER).
  - exists final;split;[exact MOVE|]. split;[exact FINAL_WELL|]. split;[exact RESULT|]. split;[|exact COUNTS].
    eapply gateway_reference_observed_frame;[exact OBSERVED| |].
    + intros item MEMBER;pose proof(proj1(Forall_forall _ _)OBSERVED item MEMBER)as[[place BEFORE]DESCRIPTION].
      destruct(Nat.eq_dec(gateway_held_ticket item)ticket)as[SAME|DIFFERENT].
      * rewrite SAME in BEFORE.
        destruct(gateway_reference_owned_ticket_unique _ _ _ _ _ _ WELL OWNED BEFORE)as[OWNER VALUE].
        rewrite VALUE,SAME;exists to;exact RESULT.
      * exists place;apply RETAINED;assumption.
    + intros;unfold gateway_reachable_values_frame;intros;assumption.
Qed.
