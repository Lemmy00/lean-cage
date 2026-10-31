(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.reads: Every loop step preserves the exact observed prefix or reaches classification. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Clight.
Require Import Slice IO Machine ClightSteps StoreSteps WriteAll Deterministic ResultLayout
  LibraryMachine LibraryPreservation LibraryControl ReceiverSource ReceiverReadSource
  ReceiverReadMemory ReceiverReadControl ReceiverRouting ReceiverReadReturns.
Import ListNotations.
Open Scope Z_scope.

Definition receiver_event_bytes ev := match ev with
  |original_event(io_step q(transfer bytes _))|original_event(partial_loss q bytes _)=>
    match operation q with reading=>bytes|writing=>[] end
  |_=>[] end.
Definition receiver_read_trace events := flat_map receiver_event_bytes events.
Inductive receiver_prefix cell b fd original bad k (P : mem -> Prop) bytes : machine -> Prop :=
| receiver_prefix_live : forall s,receiver_routed cell b fd original bad k P bytes s ->
    receiver_prefix cell b fd original bad k P bytes(live s)
| receiver_prefix_dead : forall m,P m -> receiver_buffer cell b m bytes ->
    receiver_prefix cell b fd original bad k P bytes(dead m).

Definition receiver_at_stop cell b original bad k (P : mem -> Prop) bytes s :=
  exists le m reason,s=receiver_closed_state b le k m /\ receiver_stop_valid reason bytes /\
    P m /\ receiver_buffer cell b m bytes /\
    receiver_registers original(receiver_bad bad reason)bytes le.

Theorem receiver_endpoint_step : forall cell b fd original bad k P bytes s ev target,
  receiver_reads_preserve cell b fd P -> receiver_descriptor b fd P ->
  receiver_endpoint cell b fd original bad k P bytes s -> library_step result_ge cell(live s)ev target ->
  receiver_at_stop cell b original bad k P bytes s \/
  receiver_prefix cell b fd original bad k P(bytes++receiver_event_bytes ev)target.
Proof.
  intros cell b fd original bad k P bytes s ev target PRESERVE DESCRIPTOR END STEP.
  inversion END as[le m SHORT PM BUFFER REGS|le m error SHORT PM BUFFER REGS N LOAD|
    le m reason VALID PM BUFFER REGS];subst s.
  - right.
    assert(OWN : owned(receiver_request b cell fd(Z.of_nat(length bytes)))m)
      by(eapply receiver_read_owned;eassumption).
    destruct(receiver_read_original _ _ _ _ _ _ _ _ _ _ STEP)as[old[EV ORIGINAL]];subst ev.
    assert(RUN : Machine.step result_ge(cell_of(receiver_request b cell fd(Z.of_nat(length bytes))))
      (live(read_call_state(receiver_request b cell fd(Z.of_nat(length bytes)))(receiver_read_cont b le k)m))old target).
    { rewrite receiver_request_cell;exact ORIGINAL. }
    destruct(read_call_cases _ (receiver_request b cell fd(Z.of_nat(length bytes))) _ _ _ _ eq_refl OWN RUN)
      as[[reply[after[EFFECT[EV TARGET]]]]|[[EV TARGET]|[[EV TARGET]|[part[error[after[EFFECT[EV TARGET]]]]]]]];
      subst old target;cbn [receiver_event_bytes operation receiver_request];try rewrite app_nil_r.
    + apply receiver_prefix_live.
      change(receiver_routed cell b fd original bad k P(bytes++receiver_reply_bytes reply)
        (Returnstate(Vlong(returned reply))(receiver_read_cont b le k)after)).
      eapply receiver_return_routed;eassumption.
    + apply receiver_prefix_live;exists(receiver_read_state b cell fd(Z.of_nat(length bytes))le k m);
        split;[constructor|exact END].
    + apply receiver_prefix_dead;assumption.
    + apply receiver_prefix_dead.
      * eapply PRESERVE;eassumption.
      * eapply receiver_buffer_transfer;eassumption.
  - right;destruct(receiver_errno_cases _ _ _ _ _ _ _ _ STEP)as[[EV TARGET]|[EV TARGET]];
      subst ev target;cbn [receiver_event_bytes];rewrite app_nil_r.
    + apply receiver_prefix_live;eapply receiver_errno_return_routed;eassumption.
    + apply receiver_prefix_dead;assumption.
  - left;exists le,m,reason;split;[reflexivity|]. split;[exact VALID|].
    split;[exact PM|]. split;[exact BUFFER|exact REGS].
Qed.

Theorem receiver_routed_step : forall cell b fd original bad k P bytes s ev target,
  receiver_reads_preserve cell b fd P -> receiver_descriptor b fd P ->
  receiver_routed cell b fd original bad k P bytes s -> library_step result_ge cell(live s)ev target ->
  receiver_at_stop cell b original bad k P bytes s \/
  receiver_prefix cell b fd original bad k P(bytes++receiver_event_bytes ev)target.
Proof.
  intros cell b fd original bad k P bytes s ev target PRESERVE DESCRIPTOR ROUTED STEP.
  pose proof(receiver_routed_facts _ _ _ _ _ _ _ _ _ ROUTED)as[PM BUFFER].
  destruct ROUTED as[last[PATH END]];inversion PATH as[|start mid finish EDGE TAIL];subst.
  - eapply receiver_endpoint_step;eassumption.
  - right;pose proof EDGE as[IN _].
    destruct(internal_boundary_unchanged _ _ _ _ _ IN STEP)as[old[EV ORIGINAL]];subst ev.
    destruct(machine_edge_cases _ _ _ _ _ _ EDGE ORIGINAL)as[[EV TARGET]|[EV TARGET]];
      subst old target;cbn [receiver_event_bytes];rewrite app_nil_r.
    + apply receiver_prefix_live;exists last;split;assumption.
    + apply receiver_prefix_dead;assumption.
Qed.

Theorem receiver_prefix_facts : forall cell b fd original bad k P bytes target,
  receiver_prefix cell b fd original bad k P bytes target ->
  P(routine_memory target) /\ receiver_buffer cell b(routine_memory target)bytes.
Proof.
  intros cell b fd original bad k P bytes target PREFIX;inversion PREFIX;subst;
    [eapply receiver_routed_facts;exact H|split;assumption].
Qed.
