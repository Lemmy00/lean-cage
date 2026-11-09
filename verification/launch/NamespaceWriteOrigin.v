(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.release: Resolve the actual queued release send in the same source and physical history. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Integers Values Memory.
From LeanImport Require Import Lean.
Require Import IO Machine.
From EntryProcess Require Import ProcessMachine ProcessImport ProcessJournal.
From EntryNamespace Require Import NamespaceObjects NamespaceChannel NamespacePhysical NamespaceSocket NamespaceSocketTick NamespaceSourceOwnership.
Import ListNotations.
Local Close Scope lean_scope.

(* A task executes its one recorded C program instance. This binding concerns
   every operation of that task, independently of descriptors or authorization. *)
Definition SourceProgramForKey runs parent program:=forall selected run,
  nth_error runs selected=Some run ->
  nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey(source_actor run))=parent ->selected=program.

Lemma physical_read_cannot_be_send tables actor channel number wanted bytes parent fd sent lost:
  physical_select tables actor channel number(fun descriptor=>channel_read actor descriptor wanted bytes)<>
    channel_sent parent fd sent lost.
Proof.
  unfold physical_select;destruct(physical_descriptor number)as[actual|];[|discriminate].
  destruct(tables actor actual)as[binding|];[|discriminate].
  destruct(descriptor_object binding);[discriminate|].
  destruct(Nat.eqb _ channel);discriminate.
Qed.

Lemma physical_send_has_socket_write channel tick parent fd bytes lost:
  physical_tick_projection channel tick=(physical_tick_table tick,channel_sent parent fd bytes lost) ->
  exists actor number values acknowledgement,
    ProcessImport.socket tick=LeanCage_Entry_CallerPhysical_SocketObservation_wrote actor number values acknowledgement.
Proof.
  unfold physical_tick_projection.
  destruct(ProcessImport.socket tick)as[|actor number requested values|actor number values acknowledgement|toParent toChild]eqn:SOCKET;
    cbn beta iota zeta;try discriminate.
  - destruct(physical_bytes_valid values);[|discriminate].
    intro PROJECT;injection PROJECT as EVENT;exfalso;eapply physical_read_cannot_be_send;exact EVENT.
  - intros PROJECT;exists actor,number,values,acknowledgement;reflexivity.
Qed.

Theorem actual_parent_send_resolves_program runs parent program run tick channel fd bytes lost:
  nth_error runs program=Some run ->SourceProgramForKey runs parent program ->SourceIO runs tick ->
  physical_tick_projection channel tick=(physical_tick_table tick,channel_sent parent fd bytes lost) ->
  (exists reference,LeanCage_Entry_CallerPhysical_Tick_source tick=
    ProcessImport.Option_some_inst1 LeanCage_Entry_CallerPhysical_SourceReference reference) ->
  exists ordinal event io,
    nth_error(source_events run)ordinal=Some event /\namespace_socket_io event=Some io /\
    operation(source_socket_request io)=writing /\descriptor(source_socket_request io)=fd /\
    source_socket_bytes io=bytes /\source_socket_lost io=lost /\
    LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference program ordinal.
Proof.
  intros PROGRAM DOMAIN IO PROJECT[reference REFERENCE].
  destruct(physical_send_has_socket_write _ _ _ _ _ _ PROJECT)as[actor[number[values[acknowledgement SOCKET]]]].
  assert(RECORDED:SourceSocketTick runs tick).
  { destruct(IO actor number values acknowledgement SOCKET)as[ACTUAL|OUTSIDE OBSERVED].
    - exists actor,number,values,acknowledgement;exact ACTUAL.
    - rewrite REFERENCE in OUTSIDE;discriminate. }
  destruct(actual_sent_tick_has_source_write _ _ _ _ _ _ _ RECORDED PROJECT)
    as[actual[selected[ordinal[event[io[ACTUAL[EVENT[SOCKET_EVENT[WRITING[REFERENCE'[ACTOR[FD[BYTES LOST]]]]]]]]]]]]].
  assert(SAME_PROGRAM:selected=program)by(apply DOMAIN with(run:=actual);[exact ACTUAL|symmetry;exact ACTOR]).
  subst selected;assert(SAME_RUN:actual=run)by congruence;subst actual.
  exists ordinal,event,io;repeat split;try assumption;try symmetry;assumption.
Qed.

Theorem actual_program_owner_produces_key_domain runs actor program:
  SourceProgramOwner runs actor program ->
  SourceProgramForKey runs(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor))program.
Proof.
  intros OWNER selected run PROGRAM SAME;eapply actual_source_program_for_key;eassumption.
Qed.

Theorem actual_holder_send_has_source owner child tick channel sender fd bytes lost:
  LeanCage_Entry_CallerPhysical_WriteSourceOrExternal owner child tick ->
  (sender=nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey owner) \/
    sender=nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey child)) ->
  physical_tick_projection channel tick=(physical_tick_table tick,channel_sent sender fd bytes lost) ->
  exists reference,LeanCage_Entry_CallerPhysical_Tick_source tick=
    ProcessImport.Option_some_inst1 LeanCage_Entry_CallerPhysical_SourceReference reference.
Proof.
  intros ORIGIN HOLDER PROJECT.
  destruct(physical_send_has_socket_write _ _ _ _ _ _ PROJECT)
    as[actor[number[values[acknowledgement SOCKET]]]].
  assert(SENDER:sender=nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor)).
  { unfold physical_tick_projection in PROJECT;rewrite SOCKET in PROJECT.
    destruct(physical_bytes_valid values);[|discriminate].
    cbn beta iota zeta in PROJECT;injection PROJECT as EVENT.
    exact(proj1(physical_select_write_fields _ _ _ _ _ _ _ _ _ _ EVENT)). }
  assert(WHO:actor=owner\/actor=child).
  { destruct HOLDER as[PARENT|CHILD];[left|right];apply actual_task_key_injective;congruence. }
  unfold LeanCage_Entry_CallerPhysical_WriteSourceOrExternal in ORIGIN.
  assert(WROTE:Lean.eq(ProcessImport.socket tick)
    (LeanCage_Entry_CallerPhysical_SocketObservation_wrote actor number values acknowledgement))
    by(rewrite SOCKET;constructor).
  specialize(ORIGIN actor number values acknowledgement WROTE).
  destruct(LeanCage_Entry_CallerPhysical_Tick_source tick)as[|reference]eqn:SOURCE.
  - cut Lean.sEmpty;[destruct 1|].
    destruct ORIGIN as[REFERENCE|OTHER].
    + destruct REFERENCE as[selected PRESENT];inversion PRESENT.
    + destruct OTHER as[PARENT CHILD];destruct WHO as[SAME|SAME];subst actor.
      * destruct(PARENT(Lean.eq_refl owner)).
      * destruct(CHILD(Lean.eq_refl child)).
  - exists reference;reflexivity.
Qed.
