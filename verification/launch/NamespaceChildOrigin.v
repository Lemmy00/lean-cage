(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.release: Actual child-source failure writes cannot supply a grant from the parent's endpoint. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers Values.
From LeanImport Require Import Lean.
Require Import IO Machine.
From EntryProcess Require Import ProcessMachine ProcessImport ProcessJournal ProcessSourceRecording ProcessSourceTables.
From EntryNamespace Require Import NamespaceObjects NamespaceKernel NamespaceChannel NamespacePhysical NamespaceSocket NamespaceSocketTick
  NamespaceSourceOwnership NamespaceWriteOrigin NamespaceDescriptorFrame.
Import ListNotations.
Local Close Scope lean_scope.

Lemma child_origin_skipn(A:Type)(P:A->Prop)count values:Forall P values ->Forall P(skipn count values).
Proof.
  revert values;induction count;intros values GOOD;[exact GOOD|destruct values;cbn;[constructor|]].
  inversion GOOD;subst;apply IHcount;assumption.
Qed.

Theorem actual_child_endpoint_send_impossible operation groups physical_child runs cursor worlds ticks final final_worlds
    child program run offset tick channel fd bytes lost binding failure:
  SourceTableSchedule(SourcePrimitive operation groups physical_child)runs cursor worlds ticks final final_worlds ->
  SourceProgramOwner runs child program ->nth_error runs program=Some run ->
  nth_error ticks offset=Some tick ->SourceIO runs tick ->
  (exists reference,LeanCage_Entry_CallerPhysical_Tick_source tick=
    ProcessImport.Option_some_inst1 LeanCage_Entry_CallerPhysical_SourceReference reference) ->
  physical_tick_projection channel tick=(physical_tick_table tick,
    channel_sent(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey child))fd bytes lost) ->
  physical_tick_table tick(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey child))fd=Some binding ->
  descriptor_object binding=release_endpoint channel parent_endpoint ->
  Forall(fun event=>namespace_after_fork_event event=true)(source_events run) ->
  (forall event io,In event(source_events run) ->namespace_socket_io event=Some io ->
    IO.operation(source_socket_request io)=writing ->descriptor(source_socket_request io)=failure) ->
  excludes_parent_at(namespace_table(worlds program))channel failure ->Logic.False.
Proof.
  intros RUN OWNER PROGRAM SELECTED IO REFERENCE PROJECT PRESENT OBJECT PROFILE WRITES INITIAL.
  destruct(actual_parent_send_resolves_program runs(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey child))program run
    tick channel fd bytes lost PROGRAM(actual_program_owner_produces_key_domain _ _ _ OWNER)IO PROJECT REFERENCE)
    as[ordinal[event[io[EVENT[SOCKET[WRITING[DESCRIPTOR[BYTES[LOST SOURCE]]]]]]]]].
  assert(DESCRIPTOR':fd=failure).
  { rewrite <-DESCRIPTOR;eapply WRITES;[eapply nth_error_In;exact EVENT|exact SOCKET|exact WRITING]. }
  rewrite DESCRIPTOR' in PRESENT.
  pose proof(source_table_selected_slot_exclusion _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    RUN SELECTED SOURCE PROGRAM(child_origin_skipn _ _ _ _ PROFILE)INITIAL)as EXCLUDED.
  assert(ACTOR:source_actor run=child)by(eapply source_owner_actor;eassumption).
  rewrite ACTOR in EXCLUDED;exact(EXCLUDED binding PRESENT OBJECT).
Qed.
