import FilesystemParentComparison
import FilesystemPrimitiveSelection

namespace LeanCage.Host.Kernel
open Filesystem

def DataMutation (request : Request) : Prop :=
  request.op = .mkdirAt ∨ request.op = .unlinkAt ∨ request.op = .renameNew ∨
    (request.op = .openAt ∧ request.second = newFileFlags)

def ByteNamespaceOperands (semantics : NameSemanticsView) (world : World) (request : Request) : Prop :=
  ∀ fd ∈ Lookup.parents request, ∀ handle, world.handles fd = some handle →
    (semantics.at world handle.object).byteExact

-- §AR-host-boundary.primitives: This is one stored-data mutation on CURRENTLY supported
-- operands. Public native mutations with other comparison rules remain outside this condition.
structure ByteNamespaceContract (kernel : Contract) (semantics : NameSemanticsView)
    (dataObjects : ObjectId → Prop) : Prop where
  mutation : ∀ before after request observed,
    kernel.step before request observed after → DataMutation request → ComponentRequest request →
    DirectoryOperands before request → ByteNamespaceOperands semantics before request →
    DataChange dataObjects request before after

-- §FS-host-boundary.ownership: The concrete run/validator source, raw guard and same global
-- callback history establish every namespace operand premise before the actual mkdir delta.
theorem primitive_run_mkdir_delta {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat} {semantics : NameSemanticsView}
    {dataObjects : ObjectId → Prop}
    (namespaceLaws : ByteNamespaceContract kernel semantics dataObjects)
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (raw : RawReferenceLifetimeContract kernel)
    (sdk : RuntimeDescriptorContract runtime) (accounts : AccountContract kernel hostUid)
    (metadata : GlobalAuthorityContract runtime child) (nativeMetadata : NativeMetadataContract native)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    (probes : LookupPrimitiveContract kernel.step kernel.interference semantics)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    (authorityProfile : NativeAuthorityProfile native ticks hostUid) (lookupProfile : NativeLookupProfile native ticks hostUid)
    {prior last : Processes} {callers next : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid prior callers ticks last next)
    {backend : NativeAuthorityJournal recording}
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState} {request : Request}
    {observed : Option Reply} (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (source : PrimitiveRunParent runtime initial ticks tick actor engine request) :
    DataChange dataObjects request (tick.before.project engine) tick.after.shared := by
  obtain ⟨parent, information, reference, rawParent, current, trusted, exactNames,
    mkdir, mode, component, reserved⟩ := primitive_run_mkdir_safe_parent (backend := backend) descriptors lifetimes references raw sdk accounts
      metadata nativeMetadata lookup probes journal authorityProfile lookupProfile recording selected present source
  have actual := selected_filesystem_step tick action present
  apply namespaceLaws.mutation _ _ _ _ actual (.inl mkdir)
  · simpa only [ComponentRequest, mkdir] using component
  · simpa only [DirectoryOperands, mkdir] using Exists.intro parent reference
  · intro fd member handle live
    have sameFd : fd = request.first := by simpa only [Lookup.parents, mkdir, List.mem_singleton] using member
    subst fd
    have same : handle = parent := Option.some.inj (live.symm.trans reference)
    subst handle
    simpa only [NameSemanticsView.at, Population.project] using exactNames

end LeanCage.Host.Kernel
