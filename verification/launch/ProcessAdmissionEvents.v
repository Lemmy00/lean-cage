(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: The actual admission prefix contains no child-reaping operation. *)
From Stdlib Require Import List ZArith.
From compcert Require Import Integers AST Values Memory Clight.
Require Import Machine LibraryMachine.
From EntryNative Require Import NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessPaths ProcessStatus.
Import ListNotations.
Open Scope Z_scope.

Definition admission_passive_event event : Prop :=
  match event with
  |process_entry(entry_library(original_event _))=>True
  |process_entry(entry_formatted _ _ _ _)=>True
  |process_entry entry_primitive_wait|process_waiting=>True
  |_=>False
  end.

Definition admission_lease_event child status offset event : Prop :=
  match event with
  |process_waited requested actual position options observation=>
    requested=child /\actual=status /\position=offset /\options=Int.zero /\
      match observation with
      |wait_failed _=>True
      |wait_status got word=>got=child /\admission_is_stopped word=true /\admission_is_sigstop word=true
      end
  |_=>admission_passive_event event
  end.

Definition admission_quiet_event event :=event=process_source_event \/event=process_waiting.

Lemma admission_repeat_forall(P:process_event->Prop)event count :
  P event ->Forall P(repeat event count).
Proof. intro GOOD;induction count;cbn;constructor;assumption. Qed.

Lemma admission_source_passive count : Forall admission_passive_event(repeat process_source_event count).
Proof. apply admission_repeat_forall;exact I. Qed.

Lemma admission_waiting_passive count : Forall admission_passive_event(repeat process_waiting count).
Proof. apply admission_repeat_forall;exact I. Qed.

Lemma admission_original_passive events :
  Forall admission_passive_event(map(fun event=>process_entry(entry_library(original_event event)))events).
Proof. apply Forall_forall;intros event MEMBER;apply in_map_iff in MEMBER as[original[SAME IN]];subst;exact I. Qed.

Lemma admission_passive_leases child status offset events :
  Forall admission_passive_event events ->Forall(admission_lease_event child status offset)events.
Proof.
  intro EVENTS;apply Forall_forall;intros event MEMBER.
  apply Forall_forall with(x:=event)in EVENTS;[|exact MEMBER].
  destruct event;cbn in *;try contradiction;exact EVENTS.
Qed.

Lemma admission_source_quiet count :Forall admission_quiet_event(repeat process_source_event count).
Proof. apply admission_repeat_forall;left;reflexivity. Qed.

Lemma admission_waiting_quiet count :Forall admission_quiet_event(repeat process_waiting count).
Proof. apply admission_repeat_forall;right;reflexivity. Qed.

Lemma admission_pure_quiet events :Forall(fun event=>event=process_source_event)events ->
  Forall admission_quiet_event events.
Proof. intro EVENTS;eapply Forall_impl;[|exact EVENTS];intros event SAME;left;exact SAME. Qed.
