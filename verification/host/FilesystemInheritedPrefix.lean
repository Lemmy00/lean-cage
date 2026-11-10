import FilesystemCwdCustody
import FilesystemPassiveOwnership

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: Prefix-only and lost root/CWD opens use the actual native
-- inherited directory context. They do not assume that a future getcwd/ancestry check succeeds.
theorem inherited_directory_ownership_prefix {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
    {request : Request} {observed : Option Reply}
    (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) (opening : request.op = .openAt)
    (flags : request.second = directoryFlags) (base : request.first = cwd)
    (name : request.left = "/".toUTF8 ∨ request.left = ".".toUTF8)
    {processed : List (ActorTick runtime)} {foreignReferences : ForeignReferences}
    (prior : OwnershipPrefix runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences processed tick.before)
    (directoriesPublic : EngineDirectoriesPublic tick.before prior.custody.caps.family) :
    ∃ next : OwnershipPrefix runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after,
      next.custody.caps = prior.custody.caps.retain tick.after.shared ∧ next.custody.catalogue = prior.custody.catalogue := by
  have actual := selected_filesystem_step tick action present
  have filesystem := selected_filesystem_action_family action
  have safe := selected_primitive_action_authority journal selected
  have passive : NamespacePassive request := by simp only [NamespacePassive, opening, flags, or_true]
  have requestSafe : AuthoritySafeRequest request := by intro setting; rw [opening] at setting; cases setting
  have unchanged := namespaceLaws.operation (tick.before.project engine) tick.after.shared request observed actual passive
  have state := source_unchanged_filesystem_custody accounts objects metadata actual filesystem safe requestSafe
    prior.custody.namespaceState.project unchanged
  have names := filesystem_registered_root_names lookup filesystem safe prior.custody.namespaceState.registry prior.custody.names
  have valid := catalogue_advance_valid prior.custody.valid (fun object allocated =>
    kernel.allocation_monotone (tick.before.project engine) tick.after.shared request observed object actual allocated)
  have owned : EngineReferencesOwned runtime ticks tick.after prior.custody.caps.family prior.custody.catalogue := by
    apply opened_filesystem_references_owned targets action present opening prior.custody.consistent
      (unchanged_existing_labels _ _ _) (by intro record member; exact member) prior.custody.references
    intro object scope target privateObject
    have publicObject : prior.custody.caps.family object = none := by
      rcases name with root | inherited
      · exact family_initial_public prior.custody.namespaceState.graph object
          (targets.root _ _ _ _ _ actual target opening flags base root)
      · have same := targets.cwd _ _ _ _ _ actual target opening flags base inherited
        rw [same]
        exact directoriesPublic actor engine present
    rw [privateObject] at publicObject
    cases publicObject
  let next := prior.custody.advance descriptors lifetimes references (prior.custody.caps.retain tick.after.shared)
    prior.custody.catalogue state names (catalogue_retained_covers prior.custody.coverage) valid owned .same
  have ownership : CustodyOwnershipStep next.catalogue tick prior.custody.caps.family next.caps.family :=
    nonremoving_ownership_step next.catalogue (by intro parent name object bound; rw [unchanged]; exact bound)
      (by intro object allocated; rfl)
  exact ⟨prior.advance next (by intro record member; exact member) ownership, rfl, rfl⟩

end LeanCage.Host.Kernel
