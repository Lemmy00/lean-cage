import FilesystemBootstrapSource
import FilesystemAllocationCustody
import FilesystemNativeLaunchHistory

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.caller: Release installation identifies the actual executable
-- of this native handoff. It need not be the effective request's selected bundle.
structure BootstrapExecutableSelection {initial : World} (catalogue : BootstrapCatalogue initial)
    (processes : NativeProcesses) (actor : ActorId) where
  handoff : NativeHandoff
  current : processes.handoffs actor = some handoff
  token : handoff.token = actor
  root : String
  authorized : catalogue.roots root
  identified : catalogue.files root "bin/leancage-host" handoff.execution.image

-- §AR-host-boundary.primitives: One /proc/self/exe open observes the same current
-- process image as the native handoff. Old descriptors remain exact; every
-- introduced reference resolves that actual image, including committed reply loss.
structure ExecutableOpenObservation {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    (tick : ActorTick runtime) (actor : ActorId) (engine : EngineState)
    (observed : Option Reply) (image : ObjectId) : Prop where
  action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent ({op := .selfExecutable}, observed))
  present : tick.before.actors actor = some engine
  introduced : ∀ fd handle, tick.after.shared.handles fd = some handle →
    engine.references fd = some handle ∨ handle.object = image

-- §FS-host-boundary.ownership: The running-image observation supplies no namespace
-- safety conclusion. Public custody follows from the actual installed image's
-- initialized lifetime and the SAME selected native handoff binding.
theorem executable_registered_custody {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    (namespaceLaws : PassiveNamespaceContract kernel) (descriptors : DescriptorContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (sdk : RuntimeDescriptorContract runtime) (accounts : AccountContract kernel hostUid)
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} (catalogue : BootstrapCatalogue initial)
    {final : Population} {all processed : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {currentNative : NativeProcesses}
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative)
    {position : Nat} (selected : all[position]? = some tick) {actor : ActorId} {engine : EngineState}
    {observed : Option Reply} (selection : BootstrapExecutableSelection catalogue currentNative actor)
    (actual : ExecutableOpenObservation runtime tick actor engine observed selection.handoff.execution.image) :
    Nonempty (RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after currentNative) := by
  apply passive_allocation_registered_custody namespaceLaws descriptors lifetimes references sdk accounts objects
    metadata lookup journal prior selected actual.action actual.present (by trivial)
  intro fd handle live
  rcases actual.introduced fd handle live with old | same
  · exact .inl old
  · right
    rw [same]
    exact family_initial_public prior.current.source.custody.namespaceState.graph _
      (catalogue.initialized selection.root "bin/leancage-host" selection.handoff.execution.image selection.identified)

end LeanCage.Host.Kernel
