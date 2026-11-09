(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.receipt: Classify writers by their actual recorded actor and source program. *)
From Stdlib Require Import List Arith Lia ZArith.
From compcert Require Import Integers Values Clight.
From LeanImport Require Import Lean.
From EntryProcess Require Import ProcessImport ProcessJournal ProcessJournalLiveness ProcessCgroupRecording.
From EntryNamespace Require Import NamespaceObjects NamespacePhysical NamespaceSourceOwnership NamespaceMachine NamespacePaths
  NamespaceMemory NamespaceChildResult NamespaceForkPrefix NamespaceKernel NamespaceWorldTrace NamespaceForkWorld NamespaceTraceRegion.
Import ListNotations.
Local Close Scope lean_scope.

Lemma source_identity_different left right:
  nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey left)<>
    nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey right) ->
  (Lean.eq left right ->Lean.sEmpty).
Proof.
  intros DIFFERENT SAME.
  assert(KEY:Lean.eq(LeanCage_Entry_CallerPhysical_taskKey left)
    (LeanCage_Entry_CallerPhysical_taskKey right))by(destruct SAME;constructor).
  exact(journal_nat_contradiction _ _ DIFFERENT KEY).
Qed.

Theorem actual_common_fork_failure_endpoint scope events before_world fork_world first second failure reply
    child_temps memory snapshot channel:
  scope_history scope=[] ->
  ChildPrefixResult scope(namespace_fd_events events)
    (Callstate namespace_fork_definition[]
      (child_fork_cont(storage_pair(scope_storage scope))child_temps(scope_continuation scope))memory) ->
  namespace_fd_events events=child_signal_log scope first second failure reply ->
  namespace_kernel_steps before_world events fork_world ->fork_matches fork_world snapshot ->
  fork_inherited_table snapshot first=Some(endpoint_binding channel parent_endpoint) ->
  fork_inherited_table snapshot failure=Some(endpoint_binding channel child_endpoint).
Proof.
  intros HISTORY FRONTIER LOG KERNEL MATCH PEER.
  destruct(source_common_fork_world scope events before_world fork_world first second failure reply child_temps memory
    HISTORY FRONTIER LOG KERNEL)
    as[created[inherited[WORLD[DEFAULT[MASK[D0[D1[MINIMUM[PARENT[CHILD REST]]]]]]]]]].
  assert(TABLE:namespace_table fork_world=inherited).
  { rewrite WORLD;unfold child_fork_world,namespace_default_action;rewrite Int.eq_true;reflexivity. }
  destruct MATCH as[ACTOR[TARGET INHERITED]].
  assert(SAME:created=channel).
  { rewrite INHERITED,TABLE,PARENT in PEER;unfold endpoint_binding in PEER;inversion PEER;reflexivity. }
  subst created;rewrite INHERITED,TABLE;exact CHILD.
Qed.

Lemma source_holder_write_not_external owner child tick actor fd bytes lost:
  LeanCage_Entry_CallerPhysical_WriteSourceOrExternal owner child tick ->
  (actor=owner \/actor=child) ->
  ProcessImport.socket tick=LeanCage_Entry_CallerPhysical_SocketObservation_wrote actor fd bytes lost ->
  LeanCage_Entry_CallerPhysical_Tick_source tick=
    ProcessImport.Option_none_inst1 LeanCage_Entry_CallerPhysical_SourceReference ->Lean.sEmpty.
Proof.
  intros ORIGIN HOLDER SOCKET SOURCE.
  assert(WROTE:Lean.eq(ProcessImport.socket tick)
    (LeanCage_Entry_CallerPhysical_SocketObservation_wrote actor fd bytes lost))by(rewrite SOCKET;constructor).
  specialize(ORIGIN actor fd bytes lost WROTE).
  destruct ORIGIN as[[reference REFERENCE]|[PARENT CHILD]].
  - rewrite SOURCE in REFERENCE.
    eapply(journal_eq_test _
      (fun value=>match value with Option_none_inst1 _=>true|Option_some_inst1 _ _=>false end)
      (Option_none_inst1 LeanCage_Entry_CallerPhysical_SourceReference)
      (Option_some_inst1 LeanCage_Entry_CallerPhysical_SourceReference reference));
      [reflexivity|reflexivity|exact REFERENCE].
  - destruct HOLDER as[SAME|SAME];subst actor;
      [destruct(PARENT(Lean.eq_refl owner))|destruct(CHILD(Lean.eq_refl child))].
Qed.

Theorem actual_source_writer_cgroup_classification groups runs owner child parent_program child_program tick:
  SourceProgramOwner runs owner parent_program ->SourceProgramOwner runs child child_program ->
  SourceIO runs tick ->LeanCage_Entry_CallerPhysical_WriteSourceOrExternal owner child tick ->
  (forall ordinal,LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference parent_program ordinal ->
    LeanCage_Entry_CallerPhysical_WriteOutsideCgroup(recorded_cgroup_objects groups)tick) ->
  (forall ordinal,LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference child_program ordinal ->
    LeanCage_Entry_CallerPhysical_WriteOutsideCgroup(recorded_cgroup_objects groups)tick) ->
  (forall actor,
    nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor)<>nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey owner) ->
    nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor)<>nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey child) ->
    LeanCage_Entry_CallerPhysical_CgroupAbsent(recorded_cgroup_objects groups)tick actor) ->
  LeanCage_Entry_CallerPhysical_WriteOutsideCgroup(recorded_cgroup_objects groups)tick.
Proof.
  intros PARENT_OWNER CHILD_OWNER IO ORIGIN PARENT CHILD FOREIGN actor fd bytes lost object BOUND WROTE PRESENT.
  assert(SOCKET:ProcessImport.socket tick=LeanCage_Entry_CallerPhysical_SocketObservation_wrote actor fd bytes lost)
    by(destruct WROTE;reflexivity).
  destruct(Nat.eq_dec(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor))
    (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey owner)))as[SAME|NOT_PARENT].
  - apply actual_task_key_injective in SAME;subst actor.
    destruct(IO _ _ _ _ SOCKET)as[SOURCE|OUTSIDE _].
    + destruct(source_owned_write_reference _ _ _ _ _ _ _ PARENT_OWNER SOURCE)as[ordinal REFERENCE].
      exact(PARENT ordinal REFERENCE owner fd bytes lost object BOUND WROTE PRESENT).
    + destruct(source_holder_write_not_external owner child tick owner fd bytes lost ORIGIN
        (or_introl(Logic.eq_refl owner))SOCKET OUTSIDE).
  - destruct(Nat.eq_dec(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor))
      (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey child)))as[SAME|NOT_CHILD].
    + apply actual_task_key_injective in SAME;subst actor.
      destruct(IO _ _ _ _ SOCKET)as[SOURCE|OUTSIDE _].
      * destruct(source_owned_write_reference _ _ _ _ _ _ _ CHILD_OWNER SOURCE)as[ordinal REFERENCE].
        exact(CHILD ordinal REFERENCE child fd bytes lost object BOUND WROTE PRESENT).
      * destruct(source_holder_write_not_external owner child tick child fd bytes lost ORIGIN
          (or_intror(Logic.eq_refl child))SOCKET OUTSIDE).
    + exact(FOREIGN actor NOT_PARENT NOT_CHILD fd object BOUND PRESENT).
Qed.
