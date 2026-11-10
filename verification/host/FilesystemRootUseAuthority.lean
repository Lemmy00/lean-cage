import FilesystemRegisteredCustody
import FilesystemAnchorHistory
import FilesystemStagingParents
import FilesystemPublicParents

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: The actual source constructs every root name with
-- the reserved prefix; this lexical result does not assert filesystem freshness.
theorem PrimitiveRootUse.reserved {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    (use : PrimitiveRootUse runtime initial all tick) : PrivateNames.reservedBytes use.request.left = true := by
  rcases use.invocation with branch | branch
  · obtain ⟨invocation⟩ := branch
    obtain ⟨call⟩ := actual_run_child_call invocation.active use.mkdir
    have name : use.request.left = (PrivateNames.prefixText ++ Snapshot.hex call.child.random).toUTF8 :=
      congrArg Request.left call.child.operation
    rw [name]
    exact private_prefix_reserved _
  · obtain ⟨invocation⟩ := branch
    have name : use.request.left = (PrivateNames.prefixText ++ Snapshot.hex invocation.child.child.random).toUTF8 :=
      congrArg Request.left invocation.child.child.operation
    rw [name]
    exact private_prefix_reserved _

-- §FS-host-boundary.ownership: Every genuine root-call use selects a public parent
-- from its actual /tmp open or complete retained-CWD traversal. This classifies the
-- source operation; it is not an initial parent-role or no-private-effect premise.
theorem PrimitiveRootUse.parent_public {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (aliases : DirectoryAliasContract kernel)
    (lifetimes : LifetimeContract runtime)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    (dataLookup : DynamicDataLookupContract kernel semantics initial.allocated dataObjects)
    (cwdLookup : WorkingDirectoryContract kernel initial.allocated dataObjects)
    (journal : ActorJournal runtime (Population.empty initial) all final)
    (anchor : TemporaryAnchor initial) (anchorLookup : TemporaryLookupContract kernel anchor)
    (anchors : SystemAnchorJournal runtime anchor semantics (Population.empty initial) all final)
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {native : NativeProcesses}
    (state : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before native)
    {position : Nat} (selected : all[position]? = some tick) {trailing : List (ActorTick runtime)}
    (whole : all = processed ++ tick :: trailing) (count : processed.length = position)
    (use : PrimitiveRootUse runtime initial all tick) :
    state.current.source.custody.caps.family use.parent.object = none := by
  rcases use.invocation with branch | branch
  · obtain ⟨invocation⟩ := branch
    obtain ⟨source⟩ := primitive_run_parent_observations use.adapter invocation use.mkdir
    obtain ⟨parent, live, raw, object, publicParent⟩ := primitive_run_parent_anchor descriptors anchor anchorLookup source
      (fun ordinal reply before after sampled => system_anchor_source_snapshot anchors sampled)
      state.current.source.custody.namespaceState.graph
    have identity : parent = use.parent := Option.some.inj (live.symm.trans use.reference)
    simpa only [identity] using publicParent
  · obtain ⟨invocation⟩ := branch
    obtain ⟨source⟩ := primitive_staging_parent descriptors aliases use.adapter invocation use.mkdir
    obtain ⟨parent, live, publicParent⟩ := Lowered.parent_history_public descriptors aliases lifetimes dataLookup cwdLookup
      journal selected use.present whole count state.current.source.custody.history source.selection.rawBefore.length
      source.source.source.source.target true source.selection.actual source.selectionLimit
    have same : parent = source.parent.directory.handle := Option.some.inj (live.symm.trans source.parentAtSelection)
    have argument : use.request.first = source.source.child.container.fd :=
      congrArg Request.first source.source.child.child.operation
    have original : use.engine.references source.source.child.container.fd = some use.parent := by
      rw [← argument]
      exact use.reference
    have container : use.parent = source.container.handle := Option.some.inj (original.symm.trans source.container.live)
    simpa only [same, container, source.sameParent] using publicParent

-- §FS-host-boundary.ownership: A private descendant mkdir cannot masquerade as a
-- root creation in the registry. Both parent identities come from the SAME current
-- source row; the actual root-use producer above derives their contradictory labels.
theorem no_root_use_with_private_parent {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (aliases : DirectoryAliasContract kernel)
    (lifetimes : LifetimeContract runtime)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    (dataLookup : DynamicDataLookupContract kernel semantics initial.allocated dataObjects)
    (cwdLookup : WorkingDirectoryContract kernel initial.allocated dataObjects)
    (journal : ActorJournal runtime (Population.empty initial) all final)
    (anchor : TemporaryAnchor initial) (anchorLookup : TemporaryLookupContract kernel anchor)
    (anchors : SystemAnchorJournal runtime anchor semantics (Population.empty initial) all final)
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {native : NativeProcesses}
    (state : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before native)
    {position : Nat} (selected : all[position]? = some tick) {trailing : List (ActorTick runtime)}
    (whole : all = processed ++ tick :: trailing) (count : processed.length = position)
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply} {parent : Handle} {scope : ObjectId}
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) (live : engine.references request.first = some parent)
    (label : state.current.source.custody.caps.family parent.object = some scope) :
    ¬ Nonempty (PrimitiveRootUse runtime initial all tick) := by
  rintro ⟨use⟩
  have publicParent := use.parent_public descriptors aliases lifetimes dataLookup cwdLookup journal anchor anchorLookup anchors
    state selected whole count
  obtain ⟨sameActor, sameRequest, sameObserved⟩ := filesystem_action_origin_unique action use.action
  have before : tick.before.actors actor = some use.engine := by rw [sameActor]; exact use.present
  have sameEngine := Option.some.inj (before.symm.trans present)
  have reference : engine.references request.first = some use.parent := by
    rw [← sameEngine, sameRequest]
    exact use.reference
  have sameParent : use.parent = parent := Option.some.inj (reference.symm.trans live)
  rw [sameParent, label] at publicParent
  cases publicParent

end LeanCage.Host.Kernel
