import FilesystemUnchangedSource
import FilesystemAllocationReferences

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: The source fold supplies actual one-call allocation
-- origins. Shared namespace and metadata follow their individual primitive laws.
theorem owned_allocation_registered_custody_retained {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    (namespaceLaws : PassiveNamespaceContract kernel) (descriptors : DescriptorContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (sdk : RuntimeDescriptorContract runtime) (accounts : AccountContract kernel hostUid)
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {currentNative : NativeProcesses}
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative)
    {position : Nat} (selected : all[position]? = some tick) {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply}
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) (passive : NamespacePassive request)
    (origins : ∀ fd handle, tick.after.shared.handles fd = some handle →
      engine.references fd = some handle ∨
        ∀ scope, prior.current.source.custody.caps.family handle.object = some scope →
          prior.current.source.custody.catalogue.Owns actor scope) :
    ∃ next : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
        foreignReferences (processed ++ [tick]) tick.after currentNative,
      next.current.source.custody.catalogue = prior.current.source.custody.catalogue ∧
      next.current.source.custody.caps.family = prior.current.source.custody.caps.family := by
  have actual := selected_filesystem_step tick action present
  have filesystem := selected_filesystem_action_family action
  have safe := selected_primitive_action_authority journal selected
  have requestSafe : AuthoritySafeRequest request := by
    intro setting
    simp only [NamespacePassive, setting] at passive
  have entries := namespaceLaws.operation (tick.before.project engine) tick.after.shared request observed actual passive
  have state := source_unchanged_filesystem_custody accounts objects metadata actual filesystem safe requestSafe
    prior.current.source.custody.namespaceState.project entries
  have names := filesystem_registered_root_names lookup filesystem safe
    prior.current.source.custody.namespaceState.registry prior.current.source.custody.names
  have owned := filesystem_references_owned_of_introductions action present prior.current.source.custody.references origins
  have allocation := fun object => kernel.allocation_monotone (tick.before.project engine)
    tick.after.shared request observed object actual
  let next := prior.current.source.custody.advance descriptors lifetimes references
    (prior.current.source.custody.caps.retain tick.after.shared) prior.current.source.custody.catalogue
    state names (catalogue_retained_covers prior.current.source.custody.coverage)
    (catalogue_advance_valid prior.current.source.custody.valid allocation) owned .same
  have ownership : CustodyOwnershipStep next.catalogue tick prior.current.source.custody.caps.family next.caps.family :=
    nonremoving_ownership_step _ (by intro parent name object bound; rwa [entries]) (by intro object allocated; rfl)
  let nextSource := prior.current.source.advance next (by intro record member; exact member) ownership
  refine ⟨prior.sourceStep sdk lifetimes nextSource ?_ (unchanged_existing_labels _ _ _) rfl ownership ?_, rfl, rfl⟩
  · intro owner handles closeExec directory impossible
    rw [impossible] at action
    cases action
  · apply no_root_use_of_other_operation action
    intro made
    simp only [NamespacePassive, made] at passive

-- §AR-host-boundary.interfaces: Preserve the original source-row result.
theorem owned_allocation_registered_custody {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    (namespaceLaws : PassiveNamespaceContract kernel) (descriptors : DescriptorContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (sdk : RuntimeDescriptorContract runtime) (accounts : AccountContract kernel hostUid)
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {currentNative : NativeProcesses}
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative)
    {position : Nat} (selected : all[position]? = some tick) {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply}
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) (passive : NamespacePassive request)
    (origins : ∀ fd handle, tick.after.shared.handles fd = some handle →
      engine.references fd = some handle ∨
        ∀ scope, prior.current.source.custody.caps.family handle.object = some scope →
          prior.current.source.custody.catalogue.Owns actor scope) :
    Nonempty (RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after currentNative) := by
  obtain ⟨next, catalogue, family⟩ := owned_allocation_registered_custody_retained namespaceLaws descriptors lifetimes references sdk accounts objects metadata lookup
    journal prior selected action present passive origins
  exact ⟨next⟩

theorem passive_allocation_registered_custody {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    (namespaceLaws : PassiveNamespaceContract kernel) (descriptors : DescriptorContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (sdk : RuntimeDescriptorContract runtime) (accounts : AccountContract kernel hostUid)
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {currentNative : NativeProcesses}
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative)
    {position : Nat} (selected : all[position]? = some tick) {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply}
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) (passive : NamespacePassive request)
    (origins : ∀ fd handle, tick.after.shared.handles fd = some handle →
      engine.references fd = some handle ∨ prior.current.source.custody.caps.family handle.object = none) :
    Nonempty (RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after currentNative) := by
  apply owned_allocation_registered_custody namespaceLaws descriptors lifetimes references sdk accounts objects metadata
    lookup journal prior selected action present passive
  intro fd handle live
  rcases origins fd handle live with old | publicObject
  · exact .inl old
  · right
    intro scope label
    rw [publicObject] at label
    cases label

-- §AR-host-boundary.primitives: socket(AF_UNIX, STREAM|CLOEXEC|NONBLOCK, 0)
-- allocates a fresh endpoint lifetime. Error/loss may retain that real allocation;
-- reused descriptor numbers do not equate their old and new endpoint objects.
structure SocketBirthContract (kernel : Contract) : Prop where
  introduced : ∀ before after request observed fd handle,
    kernel.step before request observed after → request.op = .socket → after.handles fd = some handle →
    before.handles fd = some handle ∨ before.allocated handle.object = false

theorem socket_registered_custody {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    (sockets : SocketBirthContract kernel)
    (namespaceLaws : PassiveNamespaceContract kernel) (descriptors : DescriptorContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (sdk : RuntimeDescriptorContract runtime) (accounts : AccountContract kernel hostUid)
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {currentNative : NativeProcesses}
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative)
    {position : Nat} (selected : all[position]? = some tick) {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply}
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) (socket : request.op = .socket) :
    Nonempty (RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after currentNative) := by
  apply passive_allocation_registered_custody namespaceLaws descriptors lifetimes references sdk accounts objects
    metadata lookup journal prior selected action present (by simp only [NamespacePassive, socket])
  intro fd handle live
  have actual := selected_filesystem_step tick action present
  rcases sockets.introduced _ _ _ _ _ _ actual socket live with old | fresh
  · exact .inl old
  · right
    change tick.before.shared.allocated handle.object = false at fresh
    cases label : prior.current.source.custody.caps.family handle.object with
    | none => rfl
    | some scope =>
      have born := prior.current.source.custody.namespaceState.graph.live handle.object scope label
      rw [fresh] at born
      cases born

end LeanCage.Host.Kernel
