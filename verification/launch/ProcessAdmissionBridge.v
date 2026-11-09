(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.provenance: Actual live source executions establish the physical lease classifiers. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Clight.
Require Import IO Machine LibraryMachine.
From EntryNative Require Import NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessAdmissionEvents ProcessOwnership.
Import ListNotations.

Lemma process_original_terminal ge cell state event target :
  (event=loss_step \/exists request bytes error,event=partial_loss request bytes error) ->
  process_step ge cell state(process_entry(entry_library(original_event event)))target ->
  exists memory,target=dead memory.
Proof.
  intros[EVENT|[request[bytes[error EVENT]]]]STEP;subst event;
    inversion STEP;subst;try discriminate;
    match goal with REAL:entry_handoff_step _ _ _ _ _|-_=>inversion REAL;subst;try discriminate end;
    match goal with REAL:library_step _ _ _ _ _|-_=>inversion REAL;subst;try discriminate end;
    match goal with REAL:Machine.step _ _ _ _ _|-_=>inversion REAL;subst;try discriminate end;eauto.
Qed.

Lemma admission_lease_step_flags ge cell state event target child status offset :
  admission_lease_event child status offset event ->process_step ge cell state event target ->
  (forall memory,target<>dead memory) ->
  process_nonreaping event=true /\process_file_frame_event event=true.
Proof.
  intros CLASS STEP LIVE.
  destruct event as[native|requested actual position options observation|request pid address data returned|
    requested actual position options|request pid address data| |clock output position observation|clock output position|auxiliary];
    cbn[admission_lease_event admission_passive_event]in CLASS;try contradiction.
  - destruct native as[library|output position value returned|output position value|descriptor flags returned|
      descriptor flags|path arguments environment returned|path arguments environment|path arguments environment|];
      cbn[admission_passive_event]in CLASS;try contradiction;try solve[split;reflexivity].
    destruct library;cbn[admission_passive_event]in CLASS;try contradiction.
    destruct ev;try solve[split;reflexivity].
    all:exfalso;match goal with
      REAL:process_step ?environment ?tls ?initial(process_entry(entry_library(original_event ?original)))?last|-_=>
      destruct(process_original_terminal environment tls initial original last
        ltac:(first[left;reflexivity|right;repeat eexists;reflexivity])REAL)as[memory SAME]
      end;exact(LIVE memory SAME).
  - destruct CLASS as[REQUEST[STATUS[OFFSET[OPTIONS OBSERVED]]]].
    destruct observation;cbn[process_nonreaping process_file_frame_event];[split;reflexivity|tauto].
  - split;reflexivity.
Qed.

Theorem admission_lease_live_member_flags ge cell initial events final child status offset event :
  process_steps ge cell initial events(live final) ->In event events ->
  admission_lease_event child status offset event ->
  process_nonreaping event=true /\process_file_frame_event event=true.
Proof.
  intro RUN;remember(live final)as last eqn:FINAL;revert event FINAL.
  induction RUN as[state|first head middle rest last STEP RUN IH];intros event FINAL MEMBER CLASS;
    [contradiction|].
  destruct MEMBER as[SAME|MEMBER].
  - subst head;eapply admission_lease_step_flags;[exact CLASS|exact STEP|].
    intros memory DEAD;subst middle.
    destruct(process_dead_steps _ _ _ _ _ RUN)as[_ IMPOSSIBLE];congruence.
  - eapply IH;[exact FINAL|exact MEMBER|exact CLASS].
Qed.

Theorem admission_lease_sublist_flags ge cell initial events final child status offset before selected after :
  process_steps ge cell initial events(live final) ->events=before++selected++after ->
  Forall(admission_lease_event child status offset)selected ->
  Forall(fun event=>process_nonreaping event=true /\process_file_frame_event event=true)selected.
Proof.
  intros RUN EVENTS CLASS;apply Forall_forall;intros event MEMBER.
  eapply admission_lease_live_member_flags with(child:=child)(status:=status)(offset:=offset);[exact RUN| |].
  - rewrite EVENTS;apply in_or_app;right;apply in_or_app;left;exact MEMBER.
  - rewrite Forall_forall in CLASS;exact(CLASS event MEMBER).
Qed.

Lemma admission_quiet_flags event :admission_quiet_event event ->
  process_nonreaping event=true /\process_file_frame_event event=true.
Proof. intros[SAME|SAME];subst event;split;reflexivity. Qed.

Lemma admission_quiet_scope world parent event :admission_quiet_event event ->
  process_scope_frame_event world parent event.
Proof. intros[SAME|SAME];subst event;split;[reflexivity|exact I|reflexivity|exact I]. Qed.
