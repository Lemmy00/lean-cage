import FilesystemAllocationCustody
import FilesystemRegisteredPassive

namespace LeanCage.Host.Kernel
open Filesystem

-- §AR-host-boundary.primitives: A single relative open cannot produce a target
-- using an absent dirfd. An absolute operand is excluded by the checked component;
-- the inherited-CWD sentinel has its own source/lookup consumer.
structure RelativeOpenParentContract {kernel : Contract} {semantics : NameSemanticsView}
    {initialObjects : ObjectId → Bool} {dataObjects : ObjectId → Prop}
    (targets : OpenTargetContract kernel semantics initialObjects dataObjects) : Prop where
  resolved : ∀ before after request observed object,
    kernel.step before request observed after → request.op = .openAt →
    (request.second = directoryFlags ∨ request.second = readFlags) →
    Directories.component request.left = true → request.first ≠ cwd →
    targets.target before request observed after object →
    ∃ parent, before.handles request.first = some parent

-- §FS-host-boundary.ownership: This source case covers invalid/closed dirfds too.
-- A committed allocation supplies its actual resolved parent; every resulting
-- private reference inherits that parent's already-proved catalogue owner.
theorem relative_read_resolved_custody {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    (namespaceLaws : PassiveNamespaceContract kernel) (descriptors : DescriptorContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (sdk : RuntimeDescriptorContract runtime) (accounts : AccountContract kernel hostUid)
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} (targets : OpenTargetContract kernel semantics initial.allocated dataObjects)
    (parents : RelativeOpenParentContract targets)
    {final : Population} {all processed : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {currentNative : NativeProcesses}
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative)
    {position : Nat} (selected : all[position]? = some tick) {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply}
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) (opening : request.op = .openAt)
    (flags : request.second = directoryFlags ∨ request.second = readFlags)
    (component : Directories.component request.left = true) (publicName : PrivateNames.reservedBytes request.left = false)
    (relative : request.first ≠ cwd) :
    Nonempty (RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after currentNative) := by
  have actual := selected_filesystem_step tick action present
  apply owned_allocation_registered_custody namespaceLaws descriptors lifetimes references sdk accounts objects metadata
    lookup journal prior selected action present (by simpa only [NamespacePassive, opening] using flags.symm)
  intro fd handle live
  rcases targets.introduced _ _ _ _ _ _ actual opening live with old | introduced
  · exact .inl old
  · right
    intro scope label
    obtain ⟨parent, parentLive⟩ := parents.resolved _ _ _ _ _ actual opening flags component relative introduced.2
    exact relative_open_target_owned targets prior.current.source.custody.namespaceState.graph
      (registered_boundaries_exact prior.current.source.custody.namespaceState.boundaries prior.current.source.custody.names)
      prior.current.source.custody.references present actual introduced.2 opening flags parentLive component publicName label

end LeanCage.Host.Kernel
