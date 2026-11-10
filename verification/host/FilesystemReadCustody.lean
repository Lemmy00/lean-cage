import FilesystemSnapshotReadForms
import FilesystemRelativeAllocation
import FilesystemInitialDirectoryCustody

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: The real parser/traversal has already built this
-- read form. Invalid relative dirfds cannot introduce a target; existing aliases
-- and committed descriptors on error/loss keep their actual lifetime identities.
theorem read_form_registered_custody {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative)
    {position : Nat} (selected : all[position]? = some tick) {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply}
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) (opening : request.op = .openAt)
    (source : SourceReadForms.ReadForm request) :
    Nonempty (RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after currentNative) := by
  rcases source opening with root | current | ⟨bounded, flags, component, publicName⟩
  · exact initial_directory_open_custody namespaceLaws descriptors lifetimes references sdk accounts objects metadata
      lookup targets journal prior selected action present opening (congrArg Request.second root)
      (congrArg Request.first root) (.inl (congrArg Request.left root))
  · exact initial_directory_open_custody namespaceLaws descriptors lifetimes references sdk accounts objects metadata
      lookup targets journal prior selected action present opening (congrArg Request.second current)
      (congrArg Request.first current) (.inr (congrArg Request.left current))
  · exact relative_read_resolved_custody namespaceLaws descriptors lifetimes references sdk accounts objects metadata
      lookup targets parents journal prior selected action present opening flags component publicName
      (SourceReadForms.descriptor_not_cwd bounded)

-- §FS-host-boundary.snapshot: These are executable source profiles consumed by
-- read_form_registered_custody. They cover the full freeze prefix, not just success.
theorem selected_snapshot_read_form (workspace : Option ByteArray) (stdin : Snapshot.Stdin) (limits : Snapshot.Limits)
    {before : List Program.Event} {request : Request} {observed : Option Reply}
    (source : Program.Prefix (Program.liftFilesystem (Snapshot.freeze workspace stdin limits))
      (before ++ [Program.filesystemPrefixEvent (request, observed)])) : SourceReadForms.ReadForm request :=
  selected_filesystem_profile (SourceReadForms.freeze_requests workspace stdin limits) source

theorem selected_caller_path_read_form (path : ByteArray) (directory : Bool)
    {before : List Program.Event} {request : Request} {observed : Option Reply}
    (source : Program.Prefix (Program.liftFilesystem (SourcePaths.open path directory))
      (before ++ [Program.filesystemPrefixEvent (request, observed)])) : SourceReadForms.ReadForm request :=
  selected_filesystem_profile (SourceReadForms.open_requests path directory) source

theorem policy_load_read_forms (request : GatewayWire.Request) :
    RequestProgram SourceReadForms.ReadForm (Validation.loadPolicy request) := by
  unfold Validation.loadPolicy
  dsimp only
  split
  · split <;> exact .pure _
  · split
    · exact request_bind (SourceReadForms.copy_file_requests _ _) (fun _ => .pure _)
    · exact .pure _

theorem selected_policy_read_form (caller : GatewayWire.Request)
    {before : List Program.Event} {request : Request} {observed : Option Reply}
    (source : Program.Prefix (Program.liftFilesystem (Validation.loadPolicy caller))
      (before ++ [Program.filesystemPrefixEvent (request, observed)])) : SourceReadForms.ReadForm request :=
  selected_filesystem_profile (policy_load_read_forms caller) source

end LeanCage.Host.Kernel
