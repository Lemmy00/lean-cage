import ControllerPrimitiveSource
import FilesystemChildCustody

namespace LeanCage.Application.ControllerFilesystem
open LeanCageM3
open LeanCage.Host LeanCage.Host.Filesystem LeanCage.Host.Kernel

-- §AR-metadata.primitives: These are the three actual single-operation ABI
-- effects of the controller reader. They contain no successful-reader or
-- descendant-lifetime premise, and say nothing about unsupported write flags.
structure MetadataNamespaceContract (kernel : Contract) : Prop where
  readonly : ∀ before after request observed,
    kernel.step before request observed after →
    (request.op = .read ∨ request.op = .close ∨
      (request.op = .openAt ∧ request.second = 524288)) → after.entries = before.entries

theorem metadata_namespace_contract {kernel : Contract} (legacy : NamespaceContract kernel) :
    MetadataNamespaceContract kernel := by
  constructor
  intro before after request observed actual kind
  have different : (524288 : UInt64) ≠ newFileFlags := by decide
  funext parent name
  apply legacy.entry_frame _ _ _ _ parent name actual
  · rcases kind with reading | closing | opening
    · simp [ComponentRequest, reading]
    · simp [ComponentRequest, closing]
    · simp [ComponentRequest, opening.1, opening.2, different]
  · rcases kind with reading | closing | opening
    · simp [TouchesEntry, reading]
    · simp [TouchesEntry, closing]
    · simp [TouchesEntry, opening.1, opening.2, different]

theorem metadata_namespace_readonly {kernel : Contract} (namespaceLaws : MetadataNamespaceContract kernel)
    {before after : World} (request : Metadata.Request) {reply : Option Reply}
    (actual : kernel.step before (metadataRequest request) reply after) : after.entries = before.entries := by
  apply namespaceLaws.readonly _ _ _ _ actual
  cases operation : request.op <;> simp [metadataRequest, operation]

-- §AR-metadata.primitives: The source reader's exact open flags are read-only;
-- its read and close cannot change names. This conclusion comes from each
-- actual ABI request, including a lost reply, not a whole-reader footprint input.
theorem metadata_namespace {kernel : Contract} (namespaceLaws : NamespaceContract kernel)
    {before after : World} (request : Metadata.Request) {reply : Option Reply}
    (actual : kernel.step before (metadataRequest request) reply after) : after.entries = before.entries := by
  exact metadata_namespace_readonly (metadata_namespace_contract namespaceLaws) request actual

-- §FS-host-boundary.ownership: The actual metadata case extends the SAME global
-- child/source publication state. The real child's complete FD/CWD table stays
-- on its operation; no future source or child return is introduced.
theorem actual_metadata_registered_publication_readonly {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {semantics : NameSemanticsView} {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : MetadataNamespaceContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (objects : ObjectLifetimeContract runtime)
    (metadata : LiveMetadataContract runtime child) (heldMetadata : GlobalAuthorityContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {all processed : List (ActorTick runtime)} {tick : ActorTick runtime}
    {before after : Processes} (recorded : process.step tick before after)
    (call : ChildCallAt child tick before after) (request : Metadata.Request)
    (operation : call.operation = .adapted (metadataRequest request))
    {foreignReferences : ForeignReferences} {callers : NativeProcesses}
    (prior : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before callers) :
    Nonempty (RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after callers) := by
  have raw := call.native
  rw [operation] at raw
  have actual := child.interpreted _ _ _ _ _ _ raw
  have entries := metadata_namespace_readonly namespaceLaws request actual
  exact child_unchanged_registered_publication sdk descriptors lifetimes references objects metadata heldMetadata lookup
    recorded call (by rw [operation]; exact metadata_authority_safe request) entries prior

-- §AR-host-boundary.interfaces: Preserve the stronger logical predecessor's
-- exact input interface; the final raw reader uses the narrow ABI sibling.
theorem actual_metadata_registered_publication {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {semantics : NameSemanticsView} {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : NamespaceContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (objects : ObjectLifetimeContract runtime)
    (metadata : LiveMetadataContract runtime child) (heldMetadata : GlobalAuthorityContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {all processed : List (ActorTick runtime)} {tick : ActorTick runtime}
    {before after : Processes} (recorded : process.step tick before after)
    (call : ChildCallAt child tick before after) (request : Metadata.Request)
    (operation : call.operation = .adapted (metadataRequest request))
    {foreignReferences : ForeignReferences} {callers : NativeProcesses}
    (prior : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before callers) :
    Nonempty (RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after callers) :=
  actual_metadata_registered_publication_readonly (metadata_namespace_contract namespaceLaws)
    sdk descriptors lifetimes references objects metadata heldMetadata lookup recorded call request operation prior

end LeanCage.Application.ControllerFilesystem
