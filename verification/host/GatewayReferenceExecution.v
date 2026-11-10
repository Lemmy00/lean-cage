(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Ghost ownership covers the same physical prefixes, including loss. *)
From Stdlib Require Import List.
From HostGateway Require Import GatewayMachine GatewayReferenceLedger.
Import ListNotations.

Definition gateway_reference_selector (World Event:Type):Type:=
  gateway_state World->gateway_event Event->gateway_state World->
    gateway_reference_status->gateway_reference_action.

Inductive gateway_reference_execution {World Event}(backend:gateway_backend World Event)ge
    (select:gateway_reference_selector World Event) :
    gateway_state World->gateway_reference_status->list(gateway_event Event)->
      gateway_state World->gateway_reference_status->Prop:=
| gateway_reference_execution_nil:forall state status,
    gateway_reference_execution backend ge select state status[]state status
| gateway_reference_execution_cons:forall first status event middle remaining last final,
    gateway_step backend ge first event middle->
    gateway_reference_execution backend ge select middle
      (gateway_reference_apply(select first event middle status)status)remaining last final->
    gateway_reference_execution backend ge select first status(event::remaining)last final.

Theorem gateway_reference_execution_erases {World Event}(backend:gateway_backend World Event)ge
    select first status events last final:
  gateway_reference_execution backend ge select first status events last final->
  gateway_steps backend ge first events last.
Proof. intro RUN;induction RUN;[constructor|econstructor;eassumption]. Qed.

Theorem gateway_reference_execution_covers {World Event}(backend:gateway_backend World Event)ge
    select first events last:
  gateway_steps backend ge first events last->
  forall status,exists final,gateway_reference_execution backend ge select first status events last final.
Proof.
  intro RUN;induction RUN;intro status.
  - exists status;constructor.
  - destruct(IHRUN(gateway_reference_apply(select first observed middle status)status))as[final TAIL].
    exists final;econstructor;eassumption.
Qed.

Theorem gateway_reference_execution_append {World Event}(backend:gateway_backend World Event)ge
    select first status prefix middle intermediate suffix last final:
  gateway_reference_execution backend ge select first status prefix middle intermediate->
  gateway_reference_execution backend ge select middle intermediate suffix last final->
  gateway_reference_execution backend ge select first status(prefix++suffix)last final.
Proof. intro PREFIX;induction PREFIX;intro SUFFIX;cbn;eauto using gateway_reference_execution_cons. Qed.

Theorem gateway_reference_execution_split {World Event}(backend:gateway_backend World Event)ge
    select first status prefix suffix last final:
  gateway_reference_execution backend ge select first status(prefix++suffix)last final->
  exists middle intermediate,
    gateway_reference_execution backend ge select first status prefix middle intermediate /\
    gateway_reference_execution backend ge select middle intermediate suffix last final.
Proof.
  revert first status;induction prefix as[|event prefix IH];intros first status RUN;cbn in RUN.
  - exists first,status;split;[constructor|exact RUN].
  - inversion RUN as[|start initial observed following rest terminal finalStatus STEP TAIL];subst.
    destruct(IH _ _ TAIL)as[middle[intermediate[PREFIX SUFFIX]]].
    exists middle,intermediate;split;[econstructor;eassumption|exact SUFFIX].
Qed.

Theorem gateway_reference_invalid_stays_invalid {World Event}(backend:gateway_backend World Event)ge
    select first reason events last final:
  gateway_reference_execution backend ge select first(gateway_reference_invalid reason)events last final->
  final=gateway_reference_invalid reason.
Proof.
  revert first;induction events as[|event rest IH];intros first RUN.
  - inversion RUN;reflexivity.
  - inversion RUN as[|start initial observed following remaining terminal status STEP TAIL];subst.
    eapply IH;cbn[gateway_reference_apply]in TAIL;exact TAIL.
Qed.

Theorem gateway_reference_execution_valid_prefix {World Event}(backend:gateway_backend World Event)ge
    select first status prefix middle intermediate suffix last final:
  gateway_reference_execution backend ge select first status prefix middle intermediate->
  gateway_reference_execution backend ge select middle intermediate suffix last(gateway_reference_valid final)->
  exists ledger,intermediate=gateway_reference_valid ledger.
Proof.
  intros PREFIX SUFFIX;destruct intermediate as[ledger|reason];[eauto|].
  pose proof(gateway_reference_invalid_stays_invalid _ _ _ _ _ _ _ _ SUFFIX);discriminate.
Qed.

Theorem gateway_reference_execution_well_formed {World Event}(backend:gateway_backend World Event)ge
    select first ledger events last final:
  gateway_reference_ledger_well_formed ledger->
  gateway_reference_execution backend ge select first(gateway_reference_valid ledger)events last
    (gateway_reference_valid final)->gateway_reference_ledger_well_formed final.
Proof.
  revert first ledger;induction events as[|event rest IH];intros first ledger FORMED RUN.
  - inversion RUN;subst;exact FORMED.
  - inversion RUN as[|start initial observed following remaining terminal status STEP TAIL];subst.
    remember(gateway_reference_apply(select first event following(gateway_reference_valid ledger))
      (gateway_reference_valid ledger))as intermediate eqn:APPLY.
    destruct intermediate as[next|reason].
    + eapply IH;[eapply gateway_reference_apply_well_formed;[exact FORMED|symmetry;exact APPLY]|exact TAIL].
    + pose proof(gateway_reference_invalid_stays_invalid _ _ _ _ _ _ _ _ TAIL);discriminate.
Qed.

(* The selector is proof-only. No theorem here certifies an unclassified action
   as an owned reference operation or excludes its physical execution. *)
