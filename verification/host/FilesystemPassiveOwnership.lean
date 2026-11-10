import FilesystemPassiveCustody
import FilesystemOwnershipPrefix

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: The same actual passive call extends removal provenance
-- alongside namespace/reference custody; no completed-history safety premise is supplied.
theorem passive_reference_ownership_prefix {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {hostUid : Nat} {semantics : NameSemanticsView}
    {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : PassiveNamespaceContract kernel) (descriptors : DescriptorContract kernel)
    (retirement : DescriptorRetirementContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (accounts : AccountContract kernel hostUid)
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime child)
    {native : NativePrimitive kernel} (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply} (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) (passive : NamespacePassive request)
    (kind : RetainsDescriptors request.op ∨ request.op = .close ∨ request.op = .dirClose)
    {processed : List (ActorTick runtime)} {foreignReferences : ForeignReferences}
    (prior : OwnershipPrefix runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences processed tick.before) :
    ∃ after : OwnershipPrefix runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after,
      after.custody.caps = prior.custody.caps.retain tick.after.shared ∧
        after.custody.catalogue = prior.custody.catalogue := by
  obtain ⟨next, caps, catalogue⟩ := passive_reference_prefix_current namespaceLaws descriptors retirement lifetimes references accounts objects metadata lookup
      journal selected action present passive kind prior.custody
  have actual := selected_filesystem_step tick action present
  have unchanged := namespaceLaws.operation (tick.before.project engine) tick.after.shared request observed actual passive
  have ownership : CustodyOwnershipStep next.catalogue tick prior.custody.caps.family next.caps.family :=
    nonremoving_ownership_step next.catalogue (by intro parent name object bound; rw [unchanged]; exact bound)
      (by intro object allocated; rw [caps]; rfl)
  have included : ∀ record ∈ prior.custody.catalogue, record ∈ next.catalogue := by
    rw [catalogue]
    exact fun _ member => member
  exact ⟨prior.advance next included ownership, caps, catalogue⟩

-- §FS-host-boundary.ownership: The same actual passive call extends removal provenance
-- alongside namespace/reference custody; no completed-history safety premise is supplied.
theorem relative_read_ownership_prefix {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {hostUid : Nat} {semantics : NameSemanticsView}
    {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : PassiveNamespaceContract kernel) (descriptors : DescriptorContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (accounts : AccountContract kernel hostUid) (objects : ObjectLifetimeContract runtime)
    (metadata : LiveMetadataContract runtime child) {native : NativePrimitive kernel}
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} (targets : OpenTargetContract kernel semantics initial.allocated dataObjects)
    {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply} {parent : Handle}
    (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) (opening : request.op = .openAt)
    (flags : request.second = directoryFlags ∨ request.second = readFlags)
    (parentLive : engine.references request.first = some parent)
    (component : Directories.component request.left = true) (publicName : PrivateNames.reservedBytes request.left = false)
    {processed : List (ActorTick runtime)} {foreignReferences : ForeignReferences}
    (prior : OwnershipPrefix runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences processed tick.before) :
    ∃ after : OwnershipPrefix runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after,
      after.custody.caps = prior.custody.caps.retain tick.after.shared ∧
        after.custody.catalogue = prior.custody.catalogue := by
  obtain ⟨next, caps, catalogue⟩ := relative_read_prefix_current namespaceLaws descriptors lifetimes references accounts objects metadata lookup targets
      journal selected action present opening flags parentLive component publicName prior.custody
  have actual := selected_filesystem_step tick action present
  have passive : NamespacePassive request := by simpa only [NamespacePassive, opening] using flags.symm
  have unchanged := namespaceLaws.operation (tick.before.project engine) tick.after.shared request observed actual passive
  have ownership : CustodyOwnershipStep next.catalogue tick prior.custody.caps.family next.caps.family :=
    nonremoving_ownership_step next.catalogue (by intro parent name object bound; rw [unchanged]; exact bound)
      (by intro object allocated; rw [caps]; rfl)
  have included : ∀ record ∈ prior.custody.catalogue, record ∈ next.catalogue := by
    rw [catalogue]
    exact fun _ member => member
  exact ⟨prior.advance next included ownership, caps, catalogue⟩

end LeanCage.Host.Kernel
