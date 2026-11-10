import FilesystemDescendantState
import FilesystemOpenTargets
import FilesystemCustodyPrefix
import FilesystemRunCreation

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: The same physical delta shape covers directory and O_EXCL
-- file births. An error or lost acknowledgement may occur in either committed branch.
theorem entry_delta_cases {dataObjects : ObjectId → Prop} {request : Request} {before after : World}
    (change : DataChange dataObjects request before after)
    (operation : request.op = .mkdirAt ∨ (request.op = .openAt ∧ request.second = newFileFlags)) :
    after.entries = before.entries ∨ Nonempty (FreshDirectoryDelta dataObjects request before after) := by
  cases change with
  | unchanged entries => exact .inl entries
  | created parent object operation reference parentLive fresh allocated data absent entries =>
    exact .inr ⟨⟨parent, object, reference, parentLive, fresh, allocated, data, absent, entries⟩⟩
  | removed removing =>
    rcases operation with mkdir | opening
    · rw [mkdir] at removing; cases removing
    · rw [opening.1] at removing; cases removing
  | renamed source target object moving =>
    rcases operation with mkdir | opening
    · rw [mkdir] at moving; cases moving
    · rw [opening.1] at moving; cases moving

-- §FS-host-boundary.ownership: The introduced O_EXCL descriptor and namespace birth name
-- exactly the same new object. No acknowledgement is fabricated to establish this equality.
theorem exclusive_target_is_birth {kernel : Contract} {semantics : NameSemanticsView}
    {initialObjects : ObjectId → Bool} {dataObjects : ObjectId → Prop}
    (targets : OpenTargetContract kernel semantics initialObjects dataObjects)
    {before after : World} {request : Request} {observed : Option Reply} {object : ObjectId}
    (actual : kernel.step before request observed after)
    (delta : FreshDirectoryDelta dataObjects request before after)
    (target : targets.target before request observed after object)
    (opening : request.op = .openAt) (flags : request.second = newFileFlags) : object = delta.object := by
  obtain ⟨fresh, bound⟩ := targets.exclusive _ _ _ _ _ _ actual target opening flags delta.reference
  have installed : after.entries delta.parent.object request.left = some delta.object := delta.bound
  exact Option.some.inj (bound.symm.trans installed)

-- §FS-host-boundary.ownership: This extends the actual global custody prefix for a private
-- descendant creation. The owner comes from its actual retained parent and recorded birth.
theorem descendant_creation_prefix {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {semantics : NameSemanticsView} {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : ByteNamespaceContract kernel semantics dataObjects)
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (accounts : AccountContract kernel hostUid)
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime child)
    (types : CreationTypeContract kernel directories)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} (targets : OpenTargetContract kernel semantics initial.allocated dataObjects)
    {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply} {parent : Handle} {scope : ObjectId}
    (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (operation : request.op = .mkdirAt ∨ (request.op = .openAt ∧ request.second = newFileFlags))
    (mode : request.op = .mkdirAt → request.second = 448)
    (component : Directories.component request.left = true)
    (parentLive : engine.references request.first = some parent)
    (comparison : (semantics.at tick.before.shared parent.object).byteExact)
    {processed : List (ActorTick runtime)} {foreignReferences : ForeignReferences}
    (prior : CustodyPrefix runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences processed tick.before)
    (parentPrivate : prior.caps.family parent.object = some scope) :
    Nonempty (CustodyPrefix runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after) := by
  have actual := selected_filesystem_step tick action present
  have filesystem := selected_filesystem_action_family action
  have safe := selected_primitive_action_authority journal selected
  have requestSafe : AuthoritySafeRequest request := by
    intro setting
    rcases operation with mkdir | opening
    · rw [mkdir] at setting; cases setting
    · rw [opening.1] at setting; cases setting
  have mutation : DataMutation request := operation.elim Or.inl (fun opening => .inr (.inr (.inr opening)))
  have components : ComponentRequest request := by
    rcases operation with mkdir | opening
    · simpa only [ComponentRequest, mkdir] using component
    · simp only [ComponentRequest, opening.1]
      exact fun _ => component
  have operands : DirectoryOperands (tick.before.project engine) request := by
    rcases operation with mkdir | opening
    · simpa only [DirectoryOperands, mkdir] using Exists.intro parent parentLive
    · simp only [DirectoryOperands, opening.1]
      exact fun _ => ⟨parent, parentLive⟩
  have byteOperands : ByteNamespaceOperands semantics (tick.before.project engine) request := by
    intro fd member handle live
    have sameFd : fd = request.first := by
      rcases operation with mkdir | opening
      · simpa only [Lookup.parents, mkdir, List.mem_singleton] using member
      · simp only [Lookup.parents, opening.1] at member
        split at member
        · cases member
        · exact List.mem_singleton.mp member
    subst fd
    have same := Option.some.inj (live.symm.trans parentLive)
    subst handle
    exact comparison
  have change := namespaceLaws.mutation _ _ _ _ actual mutation components operands byteOperands
  have allocation : ∀ object, tick.before.shared.allocated object = true → tick.after.shared.allocated object = true :=
    fun object => kernel.allocation_monotone (tick.before.project engine) tick.after.shared request observed object actual
  rcases entry_delta_cases change operation with unchanged | committed
  · have state := source_unchanged_filesystem_custody accounts objects metadata actual filesystem safe requestSafe
      prior.namespaceState.project unchanged
    have names := filesystem_registered_root_names lookup filesystem safe prior.namespaceState.registry prior.names
    have owned : EngineReferencesOwned runtime ticks tick.after prior.caps.family prior.catalogue := by
      rcases operation with mkdir | opening
      · exact retained_filesystem_references_owned descriptors action (by simp only [mkdir, RetainsDescriptors]; decide)
          prior.consistent (unchanged_existing_labels _ _ _) (by intro record member; exact member) prior.references
      · apply opened_filesystem_references_owned targets action present opening.1 prior.consistent
          (unchanged_existing_labels _ _ _) (by intro record member; exact member) prior.references
        intro object owner target privateObject
        obtain ⟨fresh, bound⟩ := targets.exclusive _ _ _ _ _ _ actual target opening.1 opening.2 parentLive
        rw [unchanged] at bound
        have allocated := (prior.namespaceState.wellFormed _ _ _ bound).2
        change tick.before.shared.allocated object = false at fresh
        rw [fresh] at allocated
        cases allocated
    exact ⟨prior.advance descriptors lifetimes references (prior.caps.retain tick.after.shared) prior.catalogue
      state names (catalogue_retained_covers prior.coverage) (catalogue_advance_valid prior.valid allocation) owned .same⟩
  · obtain ⟨delta⟩ := committed
    have sameParent := Option.some.inj (delta.reference.symm.trans parentLive)
    have privateParent : prior.caps.family delta.parent.object = some scope := by rw [sameParent]; exact parentPrivate
    obtain ⟨leading, trailing, shape⟩ := selected_tick_split selected
    have young := journal_birth_not_initial lifetimes journal shape (show FreshBirth tick delta.object from
      ⟨delta.fresh, delta.allocated⟩)
    have state := source_created_descendant_custody accounts objects metadata types actual filesystem safe operation mode
      prior.namespaceState.project delta young privateParent
    have names : RegisteredRootNames (prior.caps.addDescendant delta.object scope) semantics tick.after.shared := by
      intro root member
      have bound := delta.preserves_binding (prior.namespaceState.registry.1 root member).2.2.1
      have held : GloballyHeld tick.after root.parent := .inr (.inr ⟨root.name, root.object, bound⟩)
      exact byte_exact_after_lookup_bits (prior.names root member)
        (lookup.filesystem root.parent tick.operation filesystem safe
          (prior.namespaceState.registry.1 root member).2.1 held)
    have owned : EngineReferencesOwned runtime ticks tick.after
        (prior.caps.addDescendant delta.object scope).family prior.catalogue := by
      rcases operation with mkdir | opening
      · exact retained_filesystem_references_owned descriptors action (by simp only [mkdir, RetainsDescriptors]; decide)
          prior.consistent (set_family_existing_labels delta.fresh) (by intro record member; exact member) prior.references
      · apply opened_filesystem_references_owned targets action present opening.1 prior.consistent
          (set_family_existing_labels delta.fresh) (by intro record member; exact member) prior.references
        intro object owner target privateObject
        have same := exclusive_target_is_birth targets actual delta target opening.1 opening.2
        subst object
        have equal : scope = owner := Option.some.inj (by
          simpa only [Capabilities.addDescendant, setFamily, ite_eq_left] using privateObject)
        subst owner
        exact prior.references actor engine present request.first parent scope parentLive parentPrivate
    exact ⟨prior.advance descriptors lifetimes references (prior.caps.addDescendant delta.object scope) prior.catalogue
      state names (catalogue_descendant_covers prior.coverage) (catalogue_advance_valid prior.valid allocation)
      owned (.fresh delta.object scope delta.fresh)⟩

end LeanCage.Host.Kernel
