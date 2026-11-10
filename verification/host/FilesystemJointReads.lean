import FilesystemPublicationReads
import FilesystemOwnershipRetention

namespace LeanCage.Host.Kernel
open Filesystem

theorem owned_allocation_registered_publication_joint {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
    (prior : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative)
    (joint : JointPublicationPrefix prior)
    {position : Nat} (selected : all[position]? = some tick) {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply}
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) (passive : NamespacePassive request)
    (origins : ∀ fd handle, tick.after.shared.handles fd = some handle → engine.references fd = some handle ∨
      ∀ scope, prior.custody.current.source.custody.caps.family handle.object = some scope →
        prior.custody.current.source.custody.catalogue.Owns actor scope) :
    ∃ next : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after currentNative, JointPublicationPrefix next := by
  obtain ⟨next, catalogue, family⟩ := owned_allocation_registered_custody_retained namespaceLaws descriptors lifetimes
    references sdk accounts objects metadata lookup journal prior.custody selected action present passive origins
  let result := prior.preserved next catalogue (by intro object allocated; exact congrFun family object)
  refine ⟨result, joint.preserved next catalogue (by intro object allocated; exact congrFun family object) ?_⟩
  rw [catalogue, family]
  have entries := namespaceLaws.operation (tick.before.project engine) tick.after.shared request observed
    (selected_filesystem_step tick action present) passive
  exact nonremoving_ownership_step _ (by intro parent name object bound; rwa [entries])
    (by intro object allocated; rfl)

-- §FS-host-boundary.snapshot: The actual retained-CWD/root/component source forms
-- also preserve cumulative publication history. Unknown/closed dirfds cannot
-- introduce a target; committed opens on error/loss retain their real ownership.
theorem read_form_registered_publication_joint {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
    (prior : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative)
    (joint : JointPublicationPrefix prior)
    {position : Nat} (selected : all[position]? = some tick) {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply}
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) (opening : request.op = .openAt)
    (source : SourceReadForms.ReadForm request) :
    ∃ next : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after currentNative, JointPublicationPrefix next := by
  have actual := selected_filesystem_step tick action present
  have passive : NamespacePassive request := by
    rcases source opening with root | current | ⟨bounded, flags, component, publicName⟩
    · rw [root]; exact .inr rfl
    · rw [current]; exact .inr rfl
    · simpa only [NamespacePassive, opening] using flags.symm
  apply owned_allocation_registered_publication_joint namespaceLaws descriptors lifetimes references sdk accounts objects metadata
    lookup journal prior joint selected action present passive
  intro fd handle live
  rcases targets.introduced _ _ _ _ _ _ actual opening live with old | introduced
  · exact .inl old
  · right
    intro scope label
    rcases source opening with root | current | ⟨bounded, flags, component, publicName⟩
    · have initialized := targets.root _ _ _ _ _ actual introduced.2 opening
        (congrArg Request.second root) (congrArg Request.first root) (congrArg Request.left root)
      have publicObject := family_initial_public prior.custody.current.source.custody.namespaceState.graph _ initialized
      rw [publicObject] at label
      cases label
    · have same := targets.cwd _ _ _ _ _ actual introduced.2 opening
        (congrArg Request.second current) (congrArg Request.first current) (congrArg Request.left current)
      have publicObject := prior.custody.current.directoriesPublic actor engine present
      change handle.object = engine.workingDirectory at same
      rw [same, publicObject] at label
      cases label
    · obtain ⟨parent, parentLive⟩ := parents.resolved _ _ _ _ _ actual opening flags component
        (SourceReadForms.descriptor_not_cwd bounded) introduced.2
      exact relative_open_target_owned targets prior.custody.current.source.custody.namespaceState.graph
        (registered_boundaries_exact prior.custody.current.source.custody.namespaceState.boundaries
          prior.custody.current.source.custody.names)
        prior.custody.current.source.custody.references present actual introduced.2 opening flags parentLive
        component publicName label

-- §FS-host-boundary.caller: The selected protected manifest path gives its actual
-- introduced descriptor initialized authority. It can differ from the engine's
-- installed image root and does not make arbitrary packet roots public.
theorem bootstrap_read_registered_publication_joint {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    (namespaceLaws : PassiveNamespaceContract kernel) (descriptors : DescriptorContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (sdk : RuntimeDescriptorContract runtime) (accounts : AccountContract kernel hostUid)
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} (targets : OpenTargetContract kernel semantics initial.allocated dataObjects)
    (catalogue : BootstrapCatalogue initial) (resolution : BootstrapLookupContract kernel catalogue targets)
    {final : Population} {all processed : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {currentNative : NativeProcesses}
    (prior : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative)
    (joint : JointPublicationPrefix prior)
    {position : Nat} (selected : all[position]? = some tick) {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply} {input : GatewayWire.Request}
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) (source : BootstrapReadSource catalogue input request) :
    ∃ next : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after currentNative, JointPublicationPrefix next := by
  have actual := selected_filesystem_step tick action present
  have opening : request.op = .openAt := congrArg Request.op source.exactCall
  apply owned_allocation_registered_publication_joint namespaceLaws descriptors lifetimes references sdk accounts objects metadata
    lookup journal prior joint selected action present (by rw [source.exactCall]; exact .inl rfl)
  intro fd handle live
  rcases targets.introduced _ _ _ _ _ _ actual opening live with old | introduced
  · exact .inl old
  · right
    intro scope label
    have identified := resolution.resolved (tick.before.project engine) tick.after.shared observed source.selection.root
      source.name handle.object source.selection.authorized source.canonical (source.exactCall ▸ actual)
      (source.exactCall ▸ introduced.2)
    have publicObject := family_initial_public prior.custody.current.source.custody.namespaceState.graph _
      (catalogue.initialized source.selection.root source.name handle.object identified)
    rw [publicObject] at label
    cases label

end LeanCage.Host.Kernel
