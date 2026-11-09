(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Retain unexpected events when projecting actual descriptor operations. *)
From Stdlib Require Import List.
From compcert Require Import Integers Events.
Require Import Machine LibraryMachine.
From EntryNative Require Import NativeHandoffMachine.
Import ListNotations.

Inductive handoff_flag_return :=
| handoff_flag_event (descriptor flags returned:int)
| handoff_unexpected_event (event:entry_handoff_event).
Definition handoff_event_flags event : list handoff_flag_return :=
  match event with
  | entry_flags_returned descriptor flags returned=>[handoff_flag_event descriptor flags returned]
  | entry_formatted _ _ _ _ | entry_primitive_wait=>[]
  | entry_library(original_event(source_step []))=>[]
  | entry_library(original_event wait_step) | entry_library library_wait=>[]
  | entry_library(strcmp_returned _ _ _)=>[]
  | _=>[handoff_unexpected_event event]
  end.
Definition handoff_flags_projection events := flat_map handoff_event_flags events.
Lemma handoff_flags_projection_app first second :
  handoff_flags_projection(first++second)=handoff_flags_projection first++handoff_flags_projection second.
Proof. apply flat_map_app. Qed.
Definition handoff_expected_flags input_fd output_fd errors_fd failure :=
  [handoff_flag_event input_fd Int.zero Int.zero;handoff_flag_event output_fd Int.zero Int.zero;
   handoff_flag_event errors_fd Int.zero Int.zero;handoff_flag_event failure Int.zero Int.zero;
   handoff_flag_event Int.one Int.one Int.zero].
