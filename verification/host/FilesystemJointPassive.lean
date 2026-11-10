import FilesystemUnchangedSource
import FilesystemByteNamespaceFrames
import FilesystemOwnershipRetention

namespace LeanCage.Host.Kernel
open Filesystem

def NonallocatingNamespaceRequest (request : Request) : Prop :=
  ¬ AllocatesDescriptor request.op ∧ request.op ≠ .mkdirAt ∧ request.op ≠ .unlinkAt ∧
    request.op ≠ .renameNew ∧ request.op ≠ .temporary

-- §AR-host-boundary.primitives: Nonallocating raw calls have no pathname
-- target. Their single-call name frame is conditional on their actual
-- opcode, with metadata setters still checked by source authority separately.
theorem nonallocating_request_entries {kernel : Contract} {semantics : NameSemanticsView}
    (passive : PassiveNamespaceContract kernel) (frames : ByteNamespaceFrameContract kernel semantics) {before after : World}
    {request : Request} {observed : Option Reply} (actual : kernel.step before request observed after)
    (kind : NonallocatingNamespaceRequest request) : after.entries = before.entries := by
  by_cases directory : request.op = .dirOpen
  · exact passive.operation _ _ _ _ actual (by simp only [NamespacePassive, directory])
  have component : ComponentRequest request := by
    cases operation : request.op <;> simp_all [NonallocatingNamespaceRequest, AllocatesDescriptor, ComponentRequest]
  have noParents : Lookup.parents request = [] := by
    cases operation : request.op <;> simp_all [NonallocatingNamespaceRequest, AllocatesDescriptor, Lookup.parents]
  have operands : ByteNamespaceOperands semantics before request := by
    intro fd member handle live
    rw [noParents] at member
    cases member
  have untouched : ∀ parent name, ¬ TouchesEntry before request parent name := by
    cases operation : request.op <;> simp_all [NonallocatingNamespaceRequest, AllocatesDescriptor, TouchesEntry]
  funext parent name
  exact frames.entry _ _ _ _ parent name actual component operands (untouched parent name)

-- §FS-host-boundary.ownership: Actual read/write/probe/marker/close rows
-- extend the same joint prefix. Their source-derived setter restriction,
-- raw close retirement and error/loss are retained on the selected call.
theorem nonallocating_filesystem_publication_joint {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    (passive : PassiveNamespaceContract kernel) (frames : ByteNamespaceFrameContract kernel semantics)
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
    (present : tick.before.actors actor = some engine) (kind : NonallocatingNamespaceRequest request)
    {foreignReferences : ForeignReferences} {currentNative : NativeProcesses}
    (prior : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative) (joint : JointPublicationPrefix prior) :
    ∃ next : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after currentNative, JointPublicationPrefix next := by
  have entries := nonallocating_request_entries passive frames (selected_filesystem_step tick action present) kind
  have referenceKind : RetainsDescriptors request.op ∨ request.op = .close ∨ request.op = .dirClose := by
    cases operation : request.op <;> simp_all [NonallocatingNamespaceRequest, AllocatesDescriptor, RetainsDescriptors]
  obtain ⟨next, catalogue, family⟩ := unchanged_filesystem_registered_custody_retained descriptors retirement lifetimes
    references sdk accounts objects metadata lookup journal selected action present referenceKind kind.2.1 entries prior.custody
  refine ⟨prior.preserved next catalogue (by intro object allocated; exact congrFun family object),
    joint.preserved next catalogue (by intro object allocated; exact congrFun family object) ?_⟩
  rw [catalogue, family]
  exact nonremoving_ownership_step _ (by intro parent name object bound; rwa [entries])
    (by intro object allocated; rfl)

end LeanCage.Host.Kernel
