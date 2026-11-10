import FilesystemStagingOpeningSource
import FilesystemRootReopen
import FilesystemPrimitiveRootOpening

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: An actual stage open uses its source-returned public
-- selection or the same earlier acknowledged root mkdir. No root/owner/FD role is assumed.
theorem actual_staging_reopen_custody {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    (namespaceLaws : PassiveNamespaceContract kernel) (descriptors : DescriptorContract kernel)
    (aliases : DirectoryAliasContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (environment : InterferenceContract kernel)
    (sdk : RuntimeDescriptorContract runtime) (accounts : AccountContract kernel hostUid)
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    (targets : OpenTargetContract kernel semantics initial.allocated dataObjects)
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {currentNative : NativeProcesses}
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative)
    {trailing : List (ActorTick runtime)} (whole : all = processed ++ tick :: trailing)
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    (call : StagingOpeningCall adapter.occurrence.logicalBefore request) (opening : request.op = .openAt) :
    Nonempty (RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after currentNative) := by
  have selected : all[processed.length]? = some tick := by
    rw [whole, List.getElem?_append_right (by omega)]
    simp only [Nat.sub_self, List.getElem?_cons_zero]
  obtain ⟨route⟩ := actual_fresh_opening call.selection.parent call.active opening
  cases route with
  | alias empty operation =>
    have sourceTrace : adapter.occurrence.logicalBefore =
        (call.context ++ (call.source.identifying ++ call.source.selecting ++
          call.selection.displaying).map Program.filesystemEvent) ++
        call.selection.selecting.map Program.filesystemEvent ++ [] := by
      have mapped := congrArg (fun events : List (Request × Option Reply) =>
        call.context ++ (call.source.identifying ++ call.source.selecting ++
          call.selection.displaying ++ call.selection.selecting).map Program.filesystemEvent ++
          events.map Program.filesystemPrefixEvent) empty
      exact call.source_trace.trans (mapped.trans (by simp only [List.map_nil, List.map_append, List.append_assoc]))
    obtain ⟨phase⟩ := primitive_filesystem_phase adapter call.selection.selected sourceTrace
    obtain ⟨parent⟩ := Lowered.parent_recorded descriptors _ phase.phase.rawBefore.length
      call.source.target true phase.phase.actual
    have noTail : phase.rawTail = [] :=
      PrimitiveFilesystem.chunks_identity phase.chunks (by intro event impossible; cases impossible)
    have retaining : ∀ event ∈ phase.phase.rawAfter, RetainingEvent event := by
      intro event member
      have suffix := phase.suffix
      rw [noTail, List.nil_append] at suffix
      rw [suffix] at member
      exact adapter_namespace_prefix_retaining adapter (.inl opening) event member
    have retained := actor_retaining_event_handles descriptors phase.phase.tail retaining
    have parentReference : engine.references request.first = some parent.directory.handle := by
      have sameFD := congrArg Request.first operation
      change (tick.before.project engine).handles request.first = some parent.directory.handle
      rw [sameFD, retained]
      exact parent.directory.live
    have flags : request.second = directoryFlags := congrArg Request.second operation
    have component : Directories.component request.left = true := by
      rw [operation]
      change Directories.component (ByteArray.mk #[46]) = true
      simp [Directories.component, ByteArray.isEmpty, ByteArray.size, Array.contains_eq_mem]
    have publicName : PrivateNames.reservedBytes request.left = false := by
      rw [operation]
      change PrivateNames.reservedBytes ".".toUTF8 = false
      decide
    obtain ⟨next, caps, catalogue⟩ := relative_read_prefix_current namespaceLaws descriptors lifetimes references
      accounts objects metadata lookup targets journal selected action present opening (.inl flags)
      parentReference component publicName prior.current.source.custody
    have actual := selected_filesystem_step tick action present
    have passive : NamespacePassive request := by simp only [NamespacePassive, opening]; exact .inr flags
    have entries := namespaceLaws.operation _ _ _ _ actual passive
    have ownership : CustodyOwnershipStep next.catalogue tick
        prior.current.source.custody.caps.family next.caps.family := by
      apply nonremoving_ownership_step
      · intro parent name object bound
        rwa [entries]
      · intro object allocated
        rw [caps]
        rfl
    let nextSource := prior.current.source.advance next (by rw [catalogue]; exact fun _ member => member) ownership
    have labels : ExistingLabels tick.before.shared tick.after.shared
        prior.current.source.custody.caps.family next.caps.family := by
      rw [caps]
      exact unchanged_existing_labels _ _ _
    refine ⟨prior.sourceStep sdk lifetimes nextSource ?_ labels catalogue ownership
      (no_root_use_of_other_operation action (by rw [opening]; decide))⟩
    intro owner handles closeExec directory impossible
    rw [impossible] at action
    cases action
  | child container openingEvents opened inside active trace =>
    obtain ⟨child⟩ := actual_new_child_opening call.selection.parent.uid container.fd
      PrivateNames.prefixText active opening
    let made : Request := {
      op := .mkdirAt
      first := container.fd
      second := 448
      left := (PrivateNames.prefixText ++ Snapshot.hex child.random).toUTF8 }
    let context := call.context ++ (call.source.identifying ++ call.source.selecting ++
      call.selection.displaying ++ call.selection.selecting ++ openingEvents ++ child.randomEvents).map Program.filesystemEvent
    have logical : adapter.occurrence.logicalBefore = context ++ [.returned (.filesystem made) child.made] := by
      have outer := congrArg (fun events : List (Request × Option Reply) => call.context ++
        (call.source.identifying ++ call.source.selecting ++ call.selection.displaying ++
          call.selection.selecting).map Program.filesystemEvent ++ events.map Program.filesystemPrefixEvent) trace
      have inner := congrArg (fun events : List (Request × Option Reply) => call.context ++
        (call.source.identifying ++ call.source.selecting ++ call.selection.displaying ++
          call.selection.selecting).map Program.filesystemEvent ++
          (Publication.completed openingEvents ++ events).map Program.filesystemPrefixEvent) child.trace
      exact call.source_trace.trans (outer.trans (inner.trans (by
        simp only [context, made, List.map_append, completed_filesystem_events, List.map_cons, List.map_nil,
          Program.filesystemPrefixEvent, List.append_assoc])))
    obtain ⟨source, sourceContext⟩ := primitive_mkdir_before_open_exact adapter logical rfl child.acknowledged.1 opening
    obtain ⟨earlier⟩ := source.selected journal selected present
    have earlierAction : earlier.tick.action.eventFor actor =
        some (Program.filesystemPrefixEvent (made, some child.made)) := by
      simp only [earlier.action, ActorAction.eventFor, ↓reduceIte, Program.filesystemPrefixEvent]
    obtain ⟨earlierAdapter, exactOccurrence⟩ := actual_primitive_adapter_from_source descriptors lifetimes
      references environment journal earlier.selected earlierAction earlier.present earlier.occurrence
    have exactContext : earlierAdapter.occurrence.logicalBefore = source.context :=
      congrArg (fun value => value.logicalBefore) exactOccurrence
    have earlierCall : StagingCall earlierAdapter.occurrence.logicalBefore made := by
      have actualCall := call.mkdir_source container openingEvents opened child
      exact (exactContext.trans sourceContext).symm ▸ actualCall
    obtain ⟨parentSource⟩ := primitive_staging_parent descriptors aliases earlierAdapter earlierCall rfl
    have parentBefore : earlier.input.references made.first = some parentSource.container.handle := by
      have sameFD := congrArg Request.first parentSource.source.child.child.operation
      change (earlier.tick.before.project earlier.input).handles made.first = some parentSource.container.handle
      rw [sameFD]
      exact parentSource.container.live
    have atMade : source.observation.before.handles made.first = some parentSource.container.handle := by
      rw [earlier.before]
      exact parentBefore
    have parentCurrent := source.parent_current descriptors rfl atMade
    let use : PrimitiveRootUse runtime initial all earlier.tick := {
      actor
      engine := earlier.input
      request := made
      reply := child.made
      action := earlierAction
      present := earlier.present
      mkdir := rfl
      component := child.component
      parent := parentSource.container.handle
      reference := parentBefore
      accepted := child.acknowledged
      adapter := earlierAdapter
      invocation := .inr ⟨earlierCall⟩ }
    have earlierAt : processed[earlier.position]? = some earlier.tick := by
      simpa only [whole, List.getElem?_append_left earlier.earlier] using earlier.selected
    have flags : request.second = directoryFlags := congrArg Request.second child.operation
    have name : request.left = use.request.left := by
      have same : request.left = (PrivateNames.prefixText ++ Snapshot.hex child.random).toUTF8 :=
        congrArg Request.left child.operation
      exact same
    have reference : engine.references request.first = some use.parent := by
      have sameFD := congrArg Request.first child.operation
      change engine.references request.first = some parentSource.container.handle
      rw [sameFD]
      exact parentCurrent
    have reserved : PrivateNames.reservedBytes request.left = true := by
      rw [child.operation]
      exact private_prefix_reserved _
    have notDot : request.left ≠ ".".toUTF8 := by
      intro same
      rw [same] at reserved
      exact Bool.noConfusion reserved
    have notUp : request.left ≠ "..".toUTF8 := by
      intro same
      rw [same] at reserved
      exact Bool.noConfusion reserved
    exact root_reopen_custody namespaceLaws descriptors lifetimes references sdk accounts objects metadata lookup
      targets journal prior earlierAt use selected action present opening flags name reference notDot notUp earlier.probes

end LeanCage.Host.Kernel
