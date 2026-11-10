import FilesystemRegisteredPassive

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: One selected nonallocating/closing filesystem row
-- extends custody from its actual name delta. Setter authority is derived from
-- the maintained source, not supplied as a caller-safe-role hypothesis.
theorem unchanged_filesystem_registered_custody_retained {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    (descriptors : DescriptorContract kernel) (retirement : DescriptorRetirementContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (sdk : RuntimeDescriptorContract runtime) (accounts : AccountContract kernel hostUid)
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply} (selected : all[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (kind : RetainsDescriptors request.op ∨ request.op = .close ∨ request.op = .dirClose)
    (notMkdir : request.op ≠ .mkdirAt) (entries : tick.after.shared.entries = tick.before.shared.entries)
    {foreignReferences : ForeignReferences} {currentNative : NativeProcesses}
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative) :
    ∃ next : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
        foreignReferences (processed ++ [tick]) tick.after currentNative,
      next.current.source.custody.catalogue = prior.current.source.custody.catalogue ∧
      next.current.source.custody.caps.family = prior.current.source.custody.caps.family := by
  have actual := selected_filesystem_step tick action present
  have filesystem := selected_filesystem_action_family action
  have safe := selected_primitive_action_authority journal selected
  have requestSafe := primitive_authority_safe (selected_source_prefix_for journal selected action present)
  have state := source_unchanged_filesystem_custody accounts objects metadata actual filesystem safe requestSafe
    prior.current.source.custody.namespaceState.project entries
  have names := filesystem_registered_root_names lookup filesystem safe
    prior.current.source.custody.namespaceState.registry prior.current.source.custody.names
  have allocation := fun object => kernel.allocation_monotone (tick.before.project engine)
    tick.after.shared request observed object actual
  have owned : EngineReferencesOwned runtime all tick.after prior.current.source.custody.caps.family
      prior.current.source.custody.catalogue := by
    rcases kind with retaining | closing
    · exact retained_filesystem_references_owned descriptors action retaining prior.current.source.custody.consistent
        (unchanged_existing_labels _ _ _) (by intro record member; exact member) prior.current.source.custody.references
    · exact closed_filesystem_references_owned retirement action closing prior.current.source.custody.consistent
        (unchanged_existing_labels _ _ _) (by intro record member; exact member) prior.current.source.custody.references
  let next := prior.current.source.custody.advance descriptors lifetimes references
    (prior.current.source.custody.caps.retain tick.after.shared) prior.current.source.custody.catalogue
    state names (catalogue_retained_covers prior.current.source.custody.coverage)
    (catalogue_advance_valid prior.current.source.custody.valid allocation) owned .same
  have ownership : CustodyOwnershipStep next.catalogue tick prior.current.source.custody.caps.family next.caps.family :=
    nonremoving_ownership_step _ (by intro parent name object bound; rwa [entries])
      (by intro object allocated; rfl)
  let afterSource := prior.current.source.advance next (by intro record member; exact member) ownership
  refine ⟨prior.sourceStep sdk lifetimes afterSource ?_ (unchanged_existing_labels _ _ _) rfl ownership ?_, rfl, rfl⟩
  · intro owner handles closeExec directory impossible
    rw [impossible] at action
    cases action
  · exact no_root_use_of_other_operation action notMkdir

-- §AR-host-boundary.interfaces: Preserve the original source-row result.
theorem unchanged_filesystem_registered_custody {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    (descriptors : DescriptorContract kernel) (retirement : DescriptorRetirementContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (sdk : RuntimeDescriptorContract runtime) (accounts : AccountContract kernel hostUid)
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply} (selected : all[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (kind : RetainsDescriptors request.op ∨ request.op = .close ∨ request.op = .dirClose)
    (notMkdir : request.op ≠ .mkdirAt) (entries : tick.after.shared.entries = tick.before.shared.entries)
    {foreignReferences : ForeignReferences} {currentNative : NativeProcesses}
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative) :
    Nonempty (RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after currentNative) := by
  obtain ⟨next, catalogue, family⟩ := unchanged_filesystem_registered_custody_retained descriptors retirement lifetimes references sdk accounts objects metadata lookup
    journal selected action present kind notMkdir entries prior
  exact ⟨next⟩

-- §FS-host-boundary.publication: A real source marker setter changes only that
-- create-only user attribute. The one-syscall namespace law derives its name frame;
-- error/loss and actual marker/metadata observations remain in the same journal.
theorem attribute_registered_custody {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    (namespaceFrames : NamespaceContract kernel)
    (descriptors : DescriptorContract kernel) (retirement : DescriptorRetirementContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (sdk : RuntimeDescriptorContract runtime) (accounts : AccountContract kernel hostUid)
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply} (selected : all[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) (setting : request.op = .setAttribute)
    {foreignReferences : ForeignReferences} {currentNative : NativeProcesses}
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative) :
    Nonempty (RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after currentNative) := by
  have actual := selected_filesystem_step tick action present
  have entries : tick.after.shared.entries = tick.before.shared.entries := by
    funext parent name
    have retained := namespaceFrames.entry_frame (tick.before.project engine) tick.after.shared request observed
      parent name actual (by simp [ComponentRequest, setting]) (by simp [TouchesEntry, setting])
    exact retained
  exact unchanged_filesystem_registered_custody descriptors retirement lifetimes references sdk accounts objects metadata lookup
    journal selected action present (.inl (by rw [setting]; simp [RetainsDescriptors]))
    (by rw [setting]; decide) entries prior

end LeanCage.Host.Kernel
