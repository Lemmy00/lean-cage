import FilesystemInheritedPrefix
import FilesystemAnchorHistory

namespace LeanCage.Host.Kernel
open Filesystem

-- §AR-host-boundary.primitives: This is one /tmp open under the actual initialized root
-- binding and mount view. It also covers a committed descriptor whose reply was lost.
structure TemporaryTargetContract {kernel : Contract} {semantics : NameSemanticsView}
    {initial : World} {dataObjects : ObjectId → Prop}
    (targets : OpenTargetContract kernel semantics initial.allocated dataObjects)
    (anchor : TemporaryAnchor initial) : Prop where
  resolved : ∀ before after request observed object,
    kernel.step before request observed after → targets.target before request observed after object →
    request.op = .openAt → request.second = directoryFlags → request.first = cwd →
    request.left = "/tmp".toUTF8 → anchor.At before → object = anchor.visible

-- §FS-host-boundary.ownership: The same selected anchor snapshot authorizes a prefix-only
-- temporary-parent open. No later stat/probe success or independent child pathname is used.
theorem temporary_directory_ownership_prefix {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {hostUid : Nat} {semantics : NameSemanticsView}
    {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : PassiveNamespaceContract kernel) (descriptors : DescriptorContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (accounts : AccountContract kernel hostUid) (objects : ObjectLifetimeContract runtime)
    (metadata : LiveMetadataContract runtime child) {native : NativePrimitive kernel}
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} (targets : OpenTargetContract kernel semantics initial.allocated dataObjects)
    (anchor : TemporaryAnchor initial) (temporaryTargets : TemporaryTargetContract targets anchor)
    {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    (anchors : SystemAnchorJournal runtime anchor semantics (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply}
    (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) (opening : request.op = .openAt)
    (flags : request.second = directoryFlags) (base : request.first = cwd)
    (name : request.left = "/tmp".toUTF8)
    {processed : List (ActorTick runtime)} {foreignReferences : ForeignReferences}
    (prior : OwnershipPrefix runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences processed tick.before) :
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
      obtain ⟨anchorState⟩ := system_anchor_selected anchors selected
      have same := temporaryTargets.resolved _ _ _ _ _ actual target opening flags base name anchorState.bound
      rw [same]
      exact family_initial_public prior.custody.namespaceState.graph anchor.visible anchor.visibleInitial
    rw [privateObject] at publicObject
    cases publicObject
  let next := prior.custody.advance descriptors lifetimes references (prior.custody.caps.retain tick.after.shared)
    prior.custody.catalogue state names (catalogue_retained_covers prior.custody.coverage) valid owned .same
  have ownership : CustodyOwnershipStep next.catalogue tick prior.custody.caps.family next.caps.family :=
    nonremoving_ownership_step next.catalogue (by intro parent name object bound; rw [unchanged]; exact bound)
      (by intro object allocated; rfl)
  exact ⟨prior.advance next (by intro record member; exact member) ownership, rfl, rfl⟩

end LeanCage.Host.Kernel
