import FilesystemRegisteredCustody
import FilesystemPassiveCustody

namespace LeanCage.Host.Kernel
open Filesystem

private def retained_source_step {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (sdk : RuntimeDescriptorContract runtime) (lifetimes : LifetimeContract runtime)
    {initial : World} {all processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {native : NativeProcesses}
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before native)
    (next : CustodyPrefix runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after)
    (caps : next.caps = prior.current.source.custody.caps.retain tick.after.shared)
    (catalogue : next.catalogue = prior.current.source.custody.catalogue)
    {actor : ActorId} {request : Request} {observed : Option Reply}
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (notMkdir : request.op ≠ .mkdirAt) (entries : tick.after.shared.entries = tick.before.shared.entries) :
    RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after native := by
  have labels : ExistingLabels tick.before.shared tick.after.shared
      prior.current.source.custody.caps.family next.caps.family := by
    rw [caps]
    exact unchanged_existing_labels _ _ _
  have ownership : CustodyOwnershipStep next.catalogue tick prior.current.source.custody.caps.family next.caps.family :=
    nonremoving_ownership_step _ (by intro parent name object bound; rwa [entries])
      (by intro object allocated; rw [caps]; rfl)
  let nextSource := prior.current.source.advance next (by rw [catalogue]; exact fun _ member => member) ownership
  refine prior.sourceStep sdk lifetimes nextSource ?_ labels catalogue ownership ?_
  · intro query handles closeExec directory impossible
    rw [impossible] at action
    cases action
  · exact no_root_use_of_other_operation action notMkdir

-- §FS-host-boundary.ownership: Actual raw reads/probes/writes and closes extend all
-- registered histories together, including error/loss and partial descriptor retirement.
theorem passive_registered_custody {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {hostUid : Nat} {semantics : NameSemanticsView}
    {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : PassiveNamespaceContract kernel) (descriptors : DescriptorContract kernel)
    (retirement : DescriptorRetirementContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (sdk : RuntimeDescriptorContract runtime)
    (accounts : AccountContract kernel hostUid) (objects : ObjectLifetimeContract runtime)
    (metadata : LiveMetadataContract runtime child) {native : NativePrimitive kernel}
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply} (selected : all[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) (passive : NamespacePassive request)
    (kind : RetainsDescriptors request.op ∨ request.op = .close ∨ request.op = .dirClose)
    {foreignReferences : ForeignReferences} {currentNative : NativeProcesses}
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative) :
    Nonempty (RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after currentNative) := by
  obtain ⟨next, caps, catalogue⟩ := passive_reference_prefix_current namespaceLaws descriptors retirement lifetimes
    references accounts objects metadata lookup journal selected action present passive kind prior.current.source.custody
  refine ⟨retained_source_step sdk lifetimes prior next caps catalogue action ?_ ?_⟩
  · intro mkdir
    simp only [NamespacePassive, mkdir] at passive
  · exact namespaceLaws.operation (tick.before.project engine) tick.after.shared request observed
      (selected_filesystem_step tick action present) passive

-- §FS-host-boundary.ownership: Relative caller/private descendant reads derive ownership
-- from the same retained parent, checked nonreserved component and current registered graph.
theorem relative_read_registered_custody {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {hostUid : Nat} {semantics : NameSemanticsView}
    {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : PassiveNamespaceContract kernel) (descriptors : DescriptorContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (sdk : RuntimeDescriptorContract runtime) (accounts : AccountContract kernel hostUid)
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime child)
    {native : NativePrimitive kernel} (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} (targets : OpenTargetContract kernel semantics initial.allocated dataObjects)
    {final : Population} {all processed : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply} {parent : Handle} (selected : all[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) (opening : request.op = .openAt)
    (flags : request.second = directoryFlags ∨ request.second = readFlags)
    (parentLive : engine.references request.first = some parent)
    (component : Directories.component request.left = true) (publicName : PrivateNames.reservedBytes request.left = false)
    {foreignReferences : ForeignReferences} {currentNative : NativeProcesses}
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative) :
    Nonempty (RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after currentNative) := by
  obtain ⟨next, caps, catalogue⟩ := relative_read_prefix_current namespaceLaws descriptors lifetimes references
    accounts objects metadata lookup targets journal selected action present opening flags parentLive component publicName
    prior.current.source.custody
  refine ⟨retained_source_step sdk lifetimes prior next caps catalogue action (by rw [opening]; decide) ?_⟩
  apply namespaceLaws.operation (tick.before.project engine) tick.after.shared request observed
    (selected_filesystem_step tick action present)
  simpa only [NamespacePassive, opening] using flags.symm

end LeanCage.Host.Kernel
