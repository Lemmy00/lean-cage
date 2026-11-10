import FilesystemRunOpeningSource
import FilesystemPrimitiveRootOpening
import FilesystemRootReopen
import FilesystemAnchorTargets

namespace LeanCage.Host.Kernel
open Filesystem

private theorem temporary_open_requests :
    RequestProgram (fun request => request.op = .openAt → request = {
      op := .openAt, first := cwd, second := directoryFlags, left := "/tmp".toUTF8 })
      Directories.temporaryParent := by
  unfold Directories.temporaryParent
  apply RequestProgram.call (by intro invalid; cases invalid)
  intro reply
  dsimp only [Filesystem.Program.bind]
  split
  · exact .pure _
  · apply request_bind
    · unfold Directories.openAt
      apply RequestProgram.call (by intro _; rfl)
      intro reply
      split
      · exact .pure _
      · unfold Directories.inspect
        apply RequestProgram.call (by intro invalid; cases invalid)
        intro reply
        repeat' first
          | exact .pure _
          | split
          | exact RequestProgram.call (by intro invalid; cases invalid) (fun _ => .pure _)
    · intro value
      cases value <;> exact .pure _

-- §FS-host-boundary.ownership: This local application case derives both possible opens
-- from RunDirectory.create and the SAME earlier mkdir, global position and retained parent.
-- No directory role, catalogue entry, current name binding or quiet interval is assumed.
theorem actual_run_reopen_custody {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    (namespaceLaws : PassiveNamespaceContract kernel) (descriptors : DescriptorContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (environment : InterferenceContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (accounts : AccountContract kernel hostUid) (objects : ObjectLifetimeContract runtime)
    (metadata : LiveMetadataContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    (targets : OpenTargetContract kernel semantics initial.allocated dataObjects)
    (anchor : TemporaryAnchor initial) (anchorLookup : TemporaryLookupContract kernel anchor)
    (temporaryTargets : TemporaryTargetContract targets anchor)
    (journal : ActorJournal runtime (Population.empty initial) all final)
    (anchors : SystemAnchorJournal runtime anchor semantics (Population.empty initial) all final)
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {currentNative : NativeProcesses}
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative)
    {trailing : List (ActorTick runtime)} (whole : all = processed ++ tick :: trailing)
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    (invocation : RunCreationPrefix adapter.occurrence.logicalBefore request none)
    (opening : request.op = .openAt) :
    Nonempty (RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after currentNative) := by
  have selected : all[processed.length]? = some tick := by
    rw [whole, List.getElem?_append_right (by omega)]
    simp only [Nat.sub_self, List.getElem?_cons_zero]
  obtain ⟨route⟩ := actual_run_directory_opening invocation.active opening
  cases route with
  | selecting active =>
    have operation := request_prefix temporary_open_requests active (request, none) (by simp) opening
    have flags : request.second = directoryFlags := congrArg Request.second operation
    have base : request.first = cwd := congrArg Request.first operation
    have name : request.left = "/tmp".toUTF8 := congrArg Request.left operation
    obtain ⟨next, caps, catalogue⟩ := temporary_directory_ownership_prefix namespaceLaws descriptors
      lifetimes references accounts objects metadata lookup targets anchor temporaryTargets journal anchors
      selected action present opening flags base name prior.current.source
    have actual := selected_filesystem_step tick action present
    have passive : NamespacePassive request := by simp only [NamespacePassive, opening]; exact .inr flags
    have entries := namespaceLaws.operation _ _ _ _ actual passive
    have labels : ExistingLabels tick.before.shared tick.after.shared
        prior.current.source.custody.caps.family next.custody.caps.family := by
      rw [caps]
      exact unchanged_existing_labels _ _ _
    have ownership : CustodyOwnershipStep next.custody.catalogue tick
        prior.current.source.custody.caps.family next.custody.caps.family := by
      apply nonremoving_ownership_step
      · intro parent name object bound
        rwa [entries]
      · intro object allocated
        rw [caps]
        rfl
    refine ⟨prior.sourceStep sdk lifetimes next ?_ labels catalogue ownership
      (no_root_use_of_other_operation action (by rw [opening]; decide))⟩
    intro owner handles closeExec directory impossible
    rw [impossible] at action
    cases action
  | child container path uid selecting selectedParent inside active trace =>
    let context := invocation.context ++ selecting.map Program.filesystemEvent
    have sourceTrace : adapter.occurrence.logicalBefore = context ++ inside.map Program.filesystemPrefixEvent := by
      apply invocation.trace.trans
      have mapped := congrArg (fun events : List (Request × Option Reply) =>
        invocation.context ++ events.map Program.filesystemPrefixEvent) trace
      exact mapped.trans (by simp only [List.map_append, completed_filesystem_events, List.append_assoc, context])
    obtain ⟨receipt⟩ := primitive_new_child_reopen adapter uid container.fd PrivateNames.prefixText
      active sourceTrace opening
    have mkdir : receipt.made.op = .mkdirAt := by rw [receipt.madeExact]
    obtain ⟨earlier⟩ := receipt.source.selected journal selected present
    have earlierAction : earlier.tick.action.eventFor actor =
        some (Program.filesystemPrefixEvent (receipt.made, some receipt.child.made)) := by
      simp only [earlier.action, ActorAction.eventFor, ↓reduceIte, Program.filesystemPrefixEvent]
    obtain ⟨earlierAdapter, exactOccurrence⟩ := actual_primitive_adapter_from_source descriptors lifetimes
      references environment journal earlier.selected earlierAction earlier.present earlier.occurrence
    have exactContext : earlierAdapter.occurrence.logicalBefore = receipt.source.context :=
      congrArg (fun value => value.logicalBefore) exactOccurrence
    have sourceContext : earlierAdapter.occurrence.logicalBefore = invocation.context ++
        selecting.map Program.filesystemEvent ++ receipt.child.randomEvents.map Program.filesystemEvent :=
      exactContext.trans receipt.sourceContext
    have actualInvocation := run_root_mkdir_invocation container path uid selectedParent receipt.child invocation.context
    have sameCall : (earlierAdapter.occurrence.logicalBefore, receipt.made) =
        (invocation.context ++ selecting.map Program.filesystemEvent ++
          receipt.child.randomEvents.map Program.filesystemEvent, {
            op := .mkdirAt, first := container.fd, second := 448,
            left := (PrivateNames.prefixText ++ Snapshot.hex receipt.child.random).toUTF8 }) :=
      Prod.ext sourceContext receipt.madeExact
    have earlierInvocation : RunCreationPrefix earlierAdapter.occurrence.logicalBefore receipt.made none :=
      Eq.mp (congrArg (fun call : List Program.Event × Request => RunCreationPrefix call.1 call.2 none) sameCall).symm actualInvocation
    obtain ⟨parentSource⟩ := primitive_run_parent_observations earlierAdapter earlierInvocation mkdir
    have earlierAt : processed[earlier.position]? = some earlier.tick := by
      simpa only [whole, List.getElem?_append_left earlier.earlier] using earlier.selected
    obtain ⟨family, rest, graph, wellFormed, boundaries, suffix⟩ :=
      prior.current.source.custody.history.selected earlierAt
    obtain ⟨parent, parentBefore, raw, sameObject, publicParent⟩ := primitive_run_parent_anchor descriptors
      anchor anchorLookup parentSource (fun _ _ _ _ sampled => system_anchor_source_snapshot anchors sampled) graph
    have atMade : receipt.source.observation.before.handles receipt.made.first = some parent := by
      rw [earlier.before]
      exact parentBefore
    have parentCurrent := receipt.source.parent_current descriptors mkdir atMade
    let use : PrimitiveRootUse runtime initial all earlier.tick := {
      actor
      engine := earlier.input
      request := receipt.made
      reply := receipt.child.made
      action := earlierAction
      present := earlier.present
      mkdir
      component := by rw [receipt.madeExact]; exact receipt.child.component
      parent
      reference := parentBefore
      accepted := receipt.child.acknowledged
      adapter := earlierAdapter
      invocation := .inl ⟨earlierInvocation⟩ }
    have flags : request.second = directoryFlags := congrArg Request.second receipt.child.operation
    have name : request.left = use.request.left := by
      change request.left = receipt.made.left
      exact (congrArg Request.left receipt.child.operation).trans
        (congrArg Request.left receipt.madeExact).symm
    have reference : engine.references request.first = some use.parent := by
      change engine.references request.first = some parent
      have sameFD : request.first = receipt.made.first :=
        (congrArg Request.first receipt.child.operation).trans
          (congrArg Request.first receipt.madeExact).symm
      rw [sameFD]
      exact parentCurrent
    have reserved : PrivateNames.reservedBytes request.left = true := by
      rw [receipt.child.operation]
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
