import FilesystemCreationState
import FilesystemCustodyPrefix
import FilesystemSourceKinds
import FilesystemDescriptorEffects
import FilesystemOpenTargets
import FilesystemRunCreation

namespace LeanCage.Host.Kernel
open Filesystem

-- §AR-host-boundary.primitives: This law describes just one raw non-mutating operation.
-- Reads may change contents, offsets and metadata observations; stored names remain unchanged.
structure PassiveNamespaceContract (kernel : Contract) : Prop where
  operation : ∀ before after request observed, kernel.step before request observed after →
    NamespacePassive request → after.entries = before.entries

-- §FS-host-boundary.ownership: The actual retained or closing source call extends the SAME
-- custody prefix. The primitive law cannot supply an owner or a completed source transcript.
theorem passive_reference_prefix_current {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
    (prior : CustodyPrefix runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences processed tick.before) :
    ∃ next : CustodyPrefix runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after,
      next.caps = prior.caps.retain tick.after.shared ∧ next.catalogue = prior.catalogue := by
  have actual := selected_filesystem_step tick action present
  have filesystem := selected_filesystem_action_family action
  have safe := selected_primitive_action_authority journal selected
  have requestSafe : AuthoritySafeRequest request := by
    intro setting
    unfold NamespacePassive at passive
    rw [setting] at passive
    exact False.elim passive
  have state := source_unchanged_filesystem_custody accounts objects metadata actual filesystem safe requestSafe
    prior.namespaceState.project (namespaceLaws.operation (tick.before.project engine) tick.after.shared request observed actual passive)
  have names := filesystem_registered_root_names lookup filesystem safe prior.namespaceState.registry prior.names
  have coverage := catalogue_retained_covers (world := tick.after.shared) prior.coverage
  have valid := catalogue_advance_valid prior.valid (fun object allocated =>
    kernel.allocation_monotone (tick.before.project engine) tick.after.shared request observed object actual allocated)
  have owned : EngineReferencesOwned runtime ticks tick.after prior.caps.family prior.catalogue := by
    rcases kind with retaining | closing
    · exact retained_filesystem_references_owned descriptors action retaining prior.consistent
        (unchanged_existing_labels _ _ _) (by intro record member; exact member) prior.references
    · exact closed_filesystem_references_owned retirement action closing prior.consistent
        (unchanged_existing_labels _ _ _) (by intro record member; exact member) prior.references
  exact ⟨prior.advance descriptors lifetimes references (prior.caps.retain tick.after.shared) prior.catalogue
    state names coverage valid owned .same, rfl, rfl⟩

-- §AR-host-boundary.interfaces: Preserve the original consumer while the current sibling
-- retains its exact next capabilities and catalogue for the joint ownership fold.
theorem passive_reference_prefix {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
    (prior : CustodyPrefix runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences processed tick.before) :
    Nonempty (CustodyPrefix runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after) := by
  obtain ⟨next, caps, catalogue⟩ := passive_reference_prefix_current namespaceLaws descriptors retirement lifetimes references accounts objects metadata lookup
      journal selected action present passive kind prior
  exact ⟨next⟩

-- §FS-host-boundary.ownership: A checked public component is authorized by the current
-- graph and source-retained parent. Mount/dot/up results and unacknowledged opens stay present.
theorem relative_read_prefix_current {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
    (prior : CustodyPrefix runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences processed tick.before) :
    ∃ next : CustodyPrefix runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after,
      next.caps = prior.caps.retain tick.after.shared ∧ next.catalogue = prior.catalogue := by
  have actual := selected_filesystem_step tick action present
  have filesystem := selected_filesystem_action_family action
  have safe := selected_primitive_action_authority journal selected
  have passive : NamespacePassive request := by
    simpa only [NamespacePassive, opening] using flags.symm
  have requestSafe : AuthoritySafeRequest request := by intro setting; rw [opening] at setting; cases setting
  have state := source_unchanged_filesystem_custody accounts objects metadata actual filesystem safe requestSafe
    prior.namespaceState.project (namespaceLaws.operation (tick.before.project engine) tick.after.shared request observed actual passive)
  have names := filesystem_registered_root_names lookup filesystem safe prior.namespaceState.registry prior.names
  have coverage := catalogue_retained_covers (world := tick.after.shared) prior.coverage
  have valid := catalogue_advance_valid prior.valid (fun object allocated =>
    kernel.allocation_monotone (tick.before.project engine) tick.after.shared request observed object actual allocated)
  have owned := opened_filesystem_references_owned targets action present opening prior.consistent
    (unchanged_existing_labels _ _ _) (by intro record member; exact member) prior.references
    (fun object scope target privateObject => relative_open_target_owned targets prior.namespaceState.graph
      (registered_boundaries_exact prior.namespaceState.boundaries prior.names) prior.references present actual
      target opening flags parentLive component publicName privateObject)
  exact ⟨prior.advance descriptors lifetimes references (prior.caps.retain tick.after.shared) prior.catalogue
    state names coverage valid owned .same, rfl, rfl⟩

-- §AR-host-boundary.interfaces: Preserve the original consumer while the current sibling
-- retains its exact next capabilities and catalogue for the joint ownership fold.
theorem relative_read_prefix {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
    (prior : CustodyPrefix runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences processed tick.before) :
    Nonempty (CustodyPrefix runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after) := by
  obtain ⟨next, caps, catalogue⟩ := relative_read_prefix_current namespaceLaws descriptors lifetimes references accounts objects metadata lookup targets
      journal selected action present opening flags parentLive component publicName prior
  exact ⟨next⟩

end LeanCage.Host.Kernel
