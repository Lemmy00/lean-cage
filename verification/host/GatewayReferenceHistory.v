(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Overwritten owning C globals retain explicit unreleased allocations. *)
From Stdlib Require Import List PeanoNat.
From HostGateway Require Import GatewayMachine GatewayReferenceLedger.
Import ListNotations.

Record gateway_abandoned_reference := {
  gateway_abandoned_source_position : nat;
  gateway_abandoned_owner : gateway_owned_reference
}.

Record gateway_reference_history := {
  gateway_history_active : gateway_reference_status;
  gateway_history_abandoned : list gateway_abandoned_reference
}.

Inductive gateway_history_action :=
| gateway_history_current (action:gateway_reference_action)
| gateway_history_assign (from to:gateway_reference_place)
| gateway_history_clear (owner:gateway_reference_place).

Definition gateway_history_apply position action history:gateway_reference_history:=
  match gateway_history_active history with
  |gateway_reference_invalid _=>history
  |gateway_reference_valid ledger=>
    match action with
    |gateway_history_current current=>
      {|gateway_history_active:=gateway_reference_apply current(gateway_reference_valid ledger);
        gateway_history_abandoned:=gateway_history_abandoned history|}
    |gateway_history_clear owner=>
      match gateway_reference_take owner(gateway_reference_entries ledger)with
      |None=>history
      |Some(old,remaining)=>
        {|gateway_history_active:=gateway_reference_valid
            {|gateway_reference_next:=gateway_reference_next ledger;gateway_reference_entries:=remaining|};
          gateway_history_abandoned:=
            {|gateway_abandoned_source_position:=position;gateway_abandoned_owner:=old|}::
              gateway_history_abandoned history|}
      end
    |gateway_history_assign from to=>
      match gateway_reference_take from(gateway_reference_entries ledger)with
      |None=>{|gateway_history_active:=gateway_reference_invalid gateway_reference_missing;
          gateway_history_abandoned:=gateway_history_abandoned history|}
      |Some(selected,remaining)=>
        let moved:={|gateway_reference_ticket:=gateway_reference_ticket selected;
          gateway_reference_owner:=to;gateway_reference_pointer:=gateway_reference_pointer selected|}in
        match gateway_reference_take to remaining with
        |None=>{|gateway_history_active:=gateway_reference_valid
            {|gateway_reference_next:=gateway_reference_next ledger;gateway_reference_entries:=moved::remaining|};
          gateway_history_abandoned:=gateway_history_abandoned history|}
        |Some(old,rest)=>{|gateway_history_active:=gateway_reference_valid
            {|gateway_reference_next:=gateway_reference_next ledger;gateway_reference_entries:=moved::rest|};
          gateway_history_abandoned:=
            {|gateway_abandoned_source_position:=position;gateway_abandoned_owner:=old|}::
              gateway_history_abandoned history|}
        end
      end
    end
  end.

Definition gateway_history_selector(World Event:Type):Type:=
  nat->gateway_state World->gateway_event Event->gateway_state World->gateway_reference_history->gateway_history_action.

Inductive gateway_history_execution {World Event}(backend:gateway_backend World Event)ge
    (select:gateway_history_selector World Event):
    nat->gateway_state World->gateway_reference_history->list(gateway_event Event)->
      gateway_state World->gateway_reference_history->Prop:=
| gateway_history_execution_nil:forall position state history,
    gateway_history_execution backend ge select position state history[]state history
| gateway_history_execution_cons:forall position first history event middle rest last final,
    gateway_step backend ge first event middle->
    gateway_history_execution backend ge select(S position)middle
      (gateway_history_apply position(select position first event middle history)history)rest last final->
    gateway_history_execution backend ge select position first history(event::rest)last final.

Theorem gateway_history_execution_erases {World Event}(backend:gateway_backend World Event)ge select
    position first history events last final:
  gateway_history_execution backend ge select position first history events last final->
  gateway_steps backend ge first events last.
Proof. intro RUN;induction RUN;[constructor|econstructor;eassumption]. Qed.

Theorem gateway_history_execution_covers {World Event}(backend:gateway_backend World Event)ge select first events last:
  gateway_steps backend ge first events last->forall position history,
  exists final,gateway_history_execution backend ge select position first history events last final.
Proof.
  intro RUN;induction RUN;intros position history.
  - exists history;constructor.
  - destruct(IHRUN(S position)(gateway_history_apply position(select position first observed middle history)history))
      as[final TAIL].
    exists final;econstructor;eassumption.
Qed.

Theorem gateway_history_execution_append {World Event}(backend:gateway_backend World Event)ge select
    position first history prefix middle intermediate suffix last final:
  gateway_history_execution backend ge select position first history prefix middle intermediate->
  gateway_history_execution backend ge select(position+length prefix)middle intermediate suffix last final->
  gateway_history_execution backend ge select position first history(prefix++suffix)last final.
Proof.
  intro PREFIX;induction PREFIX;cbn;intro SUFFIX.
  - rewrite Nat.add_0_r in SUFFIX;exact SUFFIX.
  - econstructor;[exact H|]. apply IHPREFIX.
    rewrite Nat.add_succ_r in SUFFIX;exact SUFFIX.
Qed.

Theorem gateway_history_invalid_sticky position action reason retired:
  gateway_history_apply position action
    {|gateway_history_active:=gateway_reference_invalid reason;gateway_history_abandoned:=retired|}=
    {|gateway_history_active:=gateway_reference_invalid reason;gateway_history_abandoned:=retired|}.
Proof. reflexivity. Qed.
