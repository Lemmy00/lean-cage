import FilesystemByteNamespaces
import FilesystemPrimitivePublication

namespace LeanCage.Host.Kernel
open Filesystem

-- §AR-host-boundary.primitives: One syscall frames only CURRENTLY byte-exact
-- resolved directory operands. Unsupported public lookup changes stay in the
-- raw relation and cannot be erased by an unconditional exact-name axiom.
structure ByteNamespaceFrameContract (kernel : Contract) (semantics : NameSemanticsView) : Prop where
  entry : ∀ before after request observed parent name,
    kernel.step before request observed after → ComponentRequest request →
    ByteNamespaceOperands semantics before request → ¬ TouchesEntry before request parent name →
    after.entries parent name = before.entries parent name
  nonremoving : ∀ before after request observed parent name object,
    kernel.step before request observed after → ComponentRequest request →
    ByteNamespaceOperands semantics before request → request.op ≠ .unlinkAt → request.op ≠ .renameNew →
    before.entries parent name = some object → after.entries parent name = some object
  renameOtherSource : ∀ before after request observed parent name object,
    kernel.step before request observed after → request.op = .renameNew → ComponentRequest request →
    ByteNamespaceOperands semantics before request → before.entries parent name = some object →
    ¬ NamesEntry before request.first request.left parent name → after.entries parent name = some object

-- §AR-host-boundary.interfaces: Logical predecessors keep their stronger input
-- unchanged. The raw consumer uses only the conditional contract above.
theorem NamespaceContract.byteFrames {kernel : Contract} (legacy : NamespaceContract kernel) (semantics : NameSemanticsView) :
    ByteNamespaceFrameContract kernel semantics := {
  entry := fun before after request observed parent name actual component _ untouched =>
    legacy.entry_frame before after request observed parent name actual component untouched
  nonremoving := fun before after request observed parent name object actual component _ removing moving bound =>
    legacy.nonremoving_entry before after request observed parent name object actual component removing moving bound
  renameOtherSource := fun before after request observed parent name object actual moving component _ bound outside =>
    legacy.rename_other_source before after request observed parent name object actual moving component bound outside }

theorem byte_unlink_operands {semantics : NameSemanticsView} {world : World} {request : Request} {parent : Handle}
    (removing : request.op = .unlinkAt) (live : world.handles request.first = some parent)
    (comparison : (semantics.at world parent.object).byteExact) : ByteNamespaceOperands semantics world request := by
  intro fd member handle found
  have sameFd : fd = request.first := by simpa only [Lookup.parents, removing, List.mem_singleton] using member
  subst fd
  have same : handle = parent := Option.some.inj (found.symm.trans live)
  subst handle
  exact comparison

theorem PrimitiveCommitAuthority.byte_operands {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {hostUid : Nat} {semantics : NameSemanticsView} {initial : World} {all : List (ActorTick runtime)}
    {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (authority : PrimitiveCommitAuthority runtime initial all tick actor engine request observed hostUid semantics) :
    ByteNamespaceOperands semantics (tick.before.project engine) request := by
  let source := authority.resources.source.source.commit
  intro fd member handle live
  have parents : Lookup.parents request = [source.stage.container.fd, source.parent.directory.fd] :=
    (congrArg Lookup.parents source.operation).trans rfl
  rw [parents] at member
  rcases List.mem_cons.mp member with rfl | later
  · have same := Option.some.inj (live.symm.trans authority.resources.stage.container.live)
    subst handle
    simpa only [NameSemanticsView.at, Population.project, authority.resources.stage.sameParent] using authority.names
  · have sameFd := List.mem_singleton.mp later
    subst fd
    have same := Option.some.inj (live.symm.trans authority.resources.stage.parentLive)
    subst handle
    exact authority.names

end LeanCage.Host.Kernel
