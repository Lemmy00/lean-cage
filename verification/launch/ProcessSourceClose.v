(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.pid: The actual close callback adds no cgroup-writing source operation. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers Values Memory Events Clight.
Require Import Machine LibraryMachine ProcessEffects.
From EntryNative Require Import NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessPrimitiveCases ProcessCallee ProcessOwnership ProcessPhysicalTrace.
From EntryNamespace Require Import NamespaceMachine NamespaceLibrary NamespacePaths.
Import ListNotations.

Lemma source_namespace_terminal_step ge cell value memory event target:
  namespace_step ge cell(live(Returnstate value Kstop memory))event target ->
  event=namespace_process(process_entry(entry_library(original_event loss_step))) /\target=dead memory.
Proof.
  intro STEP;inversion STEP;subst;try discriminate.
  - match goal with BASE:process_step _ _ _ _ _|-_=>
      destruct(process_stopped_return_only_loss _ _ _ _ _ _ BASE)as[EVENT TARGET]end;subst;auto.
  - match goal with READY:namespace_ready _|-_=>inversion READY end.
Qed.

Lemma source_namespace_terminal_constant ge cell value before events returned after:
  namespace_steps ge cell(live(Returnstate value Kstop before))events
    (live(Returnstate returned Kstop after)) ->events=[] /\returned=value /\after=before.
Proof.
  intro RUN;inversion RUN;subst;[auto|].
  match goal with STEP:namespace_step _ _ _ _ _|-_=>
    destruct(source_namespace_terminal_step _ _ _ _ _ _ STEP)as[EVENT TARGET]end;subst.
  match goal with TAIL:namespace_steps _ _ (dead _) _ _|-_=>
    destruct(namespace_dead_steps _ _ _ _ _ TAIL)as[EMPTY IMPOSSIBLE];discriminate end.
Qed.

Theorem source_namespace_close_events ge cell before fd events returned after:
  namespace_steps ge cell(live(Callstate close_definition[Vint fd]Kstop before))events
    (live(Returnstate returned Kstop after)) ->
  exists waiting reply,
    events=repeat(namespace_process(process_entry(entry_library library_wait)))waiting++
      [namespace_process(process_entry(entry_library(close_returned fd reply)))] /\
    returned=Vint(close_value reply).
Proof.
  revert before;induction events as[|event events IH];intros before RUN.
  - inversion RUN;discriminate.
  - inversion RUN as[|first head middle rest last STEP TAIL];subst.
    destruct(namespace_close_cases _ _ _ _ _ _ _ STEP)
      as[[reply[observed[EFFECT[EVENT TARGET]]]]|[[EVENT TARGET]|[EVENT TARGET]]];subst.
    + destruct(source_namespace_terminal_constant _ _ _ _ _ _ _ TAIL)as[EVENTS[RETURNED MEMORY]];subst.
      exists 0%nat,reply;cbn;auto.
    + destruct(IH _ TAIL)as[waiting[reply[EVENTS RETURNED]]].
      exists(S waiting),reply;cbn;split;[congruence|exact RETURNED].
    + destruct(namespace_dead_steps _ _ _ _ _ TAIL)as[EMPTY IMPOSSIBLE];discriminate.
Qed.

Theorem source_namespace_close_quiet ge cell before fd events returned after:
  namespace_steps ge cell(live(Callstate close_definition[Vint fd]Kstop before))events
    (live(Returnstate returned Kstop after)) ->
  exists originals,events=map namespace_process originals /\
    Forall(fun event=>process_quiet_event event=true)originals.
Proof.
  intro RUN;destruct(source_namespace_close_events _ _ _ _ _ _ _ RUN)as[waiting[reply[EVENTS RETURNED]]].
  exists(repeat(process_entry(entry_library library_wait))waiting++[process_entry(entry_library(close_returned fd reply))]).
  split.
  - rewrite EVENTS,map_app,map_repeat;reflexivity.
  - apply Forall_app;split;[apply Forall_forall;intros event MEMBER;apply repeat_spec in MEMBER;subst event|].
    + reflexivity.
    + constructor;[reflexivity|constructor].
Qed.

Theorem source_namespace_guard_close_quiet ge cell before fd count callback returned after:
  namespace_steps ge cell(live(Callstate close_definition[Vint fd]Kstop before))callback
    (live(Returnstate returned Kstop after)) ->
  exists originals,repeat namespace_source_event count++callback=map namespace_process originals /\
    Forall(fun event=>process_quiet_event event=true)originals.
Proof.
  intro RUN;destruct(source_namespace_close_quiet _ _ _ _ _ _ _ RUN)as[originals[EVENTS QUIET]].
  exists(repeat(process_entry(entry_library(original_event(source_step E0))))count++originals);split.
  - rewrite map_app,map_repeat,<-EVENTS;reflexivity.
  - apply Forall_app;split;[|exact QUIET].
    apply Forall_forall;intros event MEMBER;apply repeat_spec in MEMBER;subst event;reflexivity.
Qed.
