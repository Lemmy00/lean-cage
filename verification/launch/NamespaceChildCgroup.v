(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.pid: Inherited cgroup authority does not turn the actual child failure writes into placements. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Clight.
From LeanImport Require Import Lean.
Require Import IO Machine.
From EntryNative Require Import NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessImport ProcessJournal ProcessCallerConnection ProcessCgroupRecording
  ProcessSourceRecording ProcessSourceTables.
From EntryNamespace Require Import NamespaceObjects NamespaceKernel NamespaceMachine NamespaceStructure NamespacePaths
  NamespaceMemory NamespaceChildResult NamespaceForkPrefix NamespaceFork NamespaceForkInputs NamespacePhysical NamespaceHandles
  NamespaceSocket NamespaceTraceRegion NamespaceGuestFlags NamespaceChildWrites NamespaceDescriptorFrame NamespaceSourceOwnership.
Import ListNotations.
Local Close Scope lean_scope.

Lemma child_source_write_failure runs program run tick ordinal actor fd bytes lost failure:
  nth_error runs program=Some run ->SourceIO runs tick ->
  LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference program ordinal ->
  (forall event io,In event(source_events run) ->namespace_socket_io event=Some io ->
    IO.operation(source_socket_request io)=writing ->descriptor(source_socket_request io)=failure) ->
  ProcessImport.socket tick=LeanCage_Entry_CallerPhysical_SocketObservation_wrote actor fd bytes lost ->
  actor=source_actor run /\fd=native_descriptor_number failure.
Proof.
  intros PROGRAM IO REFERENCE WRITES SOCKET;destruct(IO _ _ _ _ SOCKET)as[WRITE|OUTSIDE _];
    [|rewrite REFERENCE in OUTSIDE;discriminate].
  destruct WRITE as[actual selected index event io ACTUAL EVENT REQUEST WRITING ACTOR FD BYTES LOST OBSERVED SOURCE].
  change(LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference selected index)in SOURCE.
  assert(SAME:source_reference selected index=source_reference program ordinal)by congruence.
  destruct(source_reference_injective _ _ _ _ SAME)as[SELECTED ORDINAL];subst selected.
  assert(ACTUAL_RUN:actual=run)by congruence;subst actual.
  assert(DESCRIPTOR:descriptor(source_socket_request io)=failure).
  { eapply WRITES;[eapply nth_error_In;exact EVENT|exact REQUEST|exact WRITING]. }
  split;[exact ACTOR|rewrite FD,DESCRIPTOR;reflexivity].
Qed.

Theorem child_source_failure_write_outside_cgroup operation groups child runs cursor worlds ticks final final_worlds
    program run offset tick ordinal channel failure:
  SourceTableSchedule(SourcePrimitive operation groups child)runs cursor worlds ticks final final_worlds ->
  SourceProgramOwner runs child program ->nth_error runs program=Some run ->cursor program=0%nat ->
  nth_error ticks offset=Some tick ->SourceIO runs tick ->
  LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference program ordinal ->
  Forall(fun event=>namespace_after_fork_event event=true)(source_events run) ->
  (forall event io,In event(source_events run) ->namespace_socket_io event=Some io ->
    IO.operation(source_socket_request io)=writing ->descriptor(source_socket_request io)=failure) ->
  (0<=Int.signed failure)%Z ->
  namespace_table(worlds program)failure=Some(endpoint_binding channel child_endpoint) ->
  LeanCage_Entry_CallerPhysical_WriteOutsideCgroup(recorded_cgroup_objects groups)tick.
Proof.
  intros TABLES OWNER PROGRAM CURSOR SELECTED IO SOURCE PROFILE WRITES NONNEGATIVE FAILURE.
  pose proof(source_table_selected_object_frame operation groups child runs cursor worlds ticks final final_worlds
    offset tick program ordinal run TABLES SELECTED SOURCE PROGRAM ltac:(rewrite CURSOR;exact PROFILE))as FRAME.
  assert(ACTOR:source_actor run=child)by(eapply source_owner_actor;eassumption).
  rewrite ACTOR in FRAME.
  intros actor fd bytes lost code BOUND WROTE PRESENT.
  assert(SOCKET:ProcessImport.socket tick=LeanCage_Entry_CallerPhysical_SocketObservation_wrote actor fd bytes lost)
    by(destruct WROTE;reflexivity).
  destruct(child_source_write_failure _ _ _ _ _ _ _ _ _ _ PROGRAM IO SOURCE WRITES SOCKET)as[WRITER DESCRIPTOR].
  rewrite ACTOR in WRITER;subst actor fd.
  assert(LOOKUP:ProcessImport.objects tick(LeanCage_Entry_CallerPhysical_taskKey child)(native_descriptor_number failure)=
      ProcessImport.Option_some_inst1 Lean.Nat code)by(destruct PRESENT;reflexivity).
  assert(CURRENT:exists binding,physical_tick_table tick(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey child))failure=
    Some binding /\descriptor_object binding=physical_object(nat_of_Nat code)).
  { unfold physical_tick_table.
    assert(VALID:Z.leb 0(Int.signed failure)=true)by(apply Z.leb_le;exact NONNEGATIVE).
    rewrite VALID,Nat2natid,LOOKUP;eexists;split;reflexivity. }
  destruct CURRENT as[binding[PRESENT' OBJECT]].
  destruct(FRAME _ _ PRESENT')as[original[INITIAL SAME]].
  rewrite FAILURE in INITIAL;inversion INITIAL;subst original.
  assert(CODE:physical_object(nat_of_Nat code)=release_endpoint channel child_endpoint)
    by(cbn[endpoint_binding descriptor_object]in SAME;congruence).
  unfold recorded_cgroup_objects;rewrite CODE;constructor.
Qed.

Theorem actual_same_fork_child_write_outside_cgroup operation groups child runs cursor worlds ticks final final_worlds
    scope first second failure reply le before world snapshot parent child_memory run program offset tick ordinal
    channel path arguments environment:
  SourceTableSchedule(SourcePrimitive operation groups child)runs cursor worlds ticks final final_worlds ->
  SourceProgramOwner runs child program ->nth_error runs program=Some run ->cursor program=0%nat ->
  scope_history scope=[] ->
  ChildPrefixResult scope(child_signal_log scope first second failure reply)
    (Callstate namespace_fork_definition[](child_fork_cont(storage_pair(scope_storage scope))le(scope_continuation scope))before) ->
  fork_matches world snapshot ->NativeForkCopy(scope_cell scope)before parent child_memory ->
  source_cell run=scope_cell scope ->
  source_before run=live(Returnstate(Vint Int.zero)
    (child_fork_cont(storage_pair(scope_storage scope))le(scope_continuation scope))child_memory) ->
  In(namespace_guest_event(entry_image path arguments environment))(source_events run) ->
  worlds program=namespace_fork_child world snapshot ->
  fork_inherited_table snapshot failure=Some(endpoint_binding channel child_endpoint) ->
  nth_error ticks offset=Some tick ->SourceIO runs tick ->
  LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference program ordinal ->
  LeanCage_Entry_CallerPhysical_WriteOutsideCgroup(recorded_cgroup_objects groups)tick.
Proof.
  intros TABLES OWNER PROGRAM CURSOR HISTORY FRONTIER MATCH COPY CELL START IMAGE WORLD FAILURE SELECTED IO SOURCE.
  assert(RUN:namespace_steps namespace_ge(scope_cell scope)
    (live(Returnstate(Vint Int.zero)(child_fork_cont(storage_pair(scope_storage scope))le(scope_continuation scope))child_memory))
    (source_events run)(source_after run)).
  { pose proof(source_executed run)as ACTUAL;rewrite CELL,START in ACTUAL;exact ACTUAL. }
  pose proof(actual_child_image_source_has_no_capability_export scope first second failure reply le before world snapshot parent
    child_memory(source_events run)(source_after run)path arguments environment HISTORY FRONTIER MATCH COPY RUN IMAGE)as PROFILE.
  pose proof(actual_child_branch_write_descriptors scope first second failure reply le before world snapshot parent
    child_memory(source_events run)(source_after run)path arguments environment HISTORY FRONTIER MATCH COPY RUN IMAGE)as WRITES.
  assert(NONNEGATIVE:(0<=Int.signed failure)%Z).
  { destruct(actual_common_fork_inputs _ _ _ _ _ _ _ FRONTIER)as[REG[FD[VALID REST]]];exact VALID. }
  eapply(child_source_failure_write_outside_cgroup operation groups child runs cursor worlds ticks final final_worlds
    program run offset tick ordinal channel failure);try eassumption.
  rewrite WORLD;change(namespace_table world failure=Some(endpoint_binding channel child_endpoint)).
  destruct MATCH as[MP[MT INHERITED]];rewrite <-INHERITED;exact FAILURE.
Qed.
