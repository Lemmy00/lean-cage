import FilesystemCommitDelta
import FilesystemCommitGuarantee

namespace LeanCage.Host.Kernel
open Filesystem

-- §AR-host-boundary.primitives: One actual renameat2(RENAME_NOREPLACE) success
-- binds its previously resolved source object at the actual target. Error or loss
-- carries no converse assertion and may still have committed the same move.
structure RenameAcknowledgementContract (kernel : Contract) : Prop where
  committed : ∀ before after request reply sourceParent targetParent object,
    kernel.step before request (some reply) after → request.op = .renameNew → ComponentRequest request →
    before.handles request.first = some sourceParent → before.handles request.second = some targetParent →
    before.entries sourceParent.object request.left = some object → reply.1 = 0 → reply.2 = .empty →
    after.entries targetParent.object request.right = some object

-- §FS-host-boundary.publication: A stored-success observation cannot select the
-- unchanged namespace alternative. Its real delta still refers to this exact
-- source-created stage, retained parents and selected kernel operation.
theorem CommitRootAt.acknowledged_delta {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (acknowledgements : RenameAcknowledgementContract kernel)
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {reply : Reply}
    {resources : PrimitiveCommitResources runtime initial all tick actor engine request (some reply)}
    {family : Family} {catalogue : Catalogue runtime all}
    (root : CommitRootAt runtime resources family catalogue)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, some reply)))
    (present : tick.before.actors actor = some engine)
    {dataObjects : ObjectId → Prop}
    (change : DataChange dataObjects request (tick.before.project engine) tick.after.shared)
    (moving : request.op = .renameNew) (components : ComponentRequest request)
    (zero : reply.1 = 0) (empty : reply.2 = .empty) : Nonempty (CommitDelta resources root.root.object) := by
  have actual := selected_filesystem_step tick action present
  have sourceFd := congrArg Request.first resources.source.source.commit.operation
  have targetFd := congrArg Request.second resources.source.source.commit.operation
  have sourceName := congrArg Request.left resources.source.source.commit.operation
  have targetName := congrArg Request.right resources.source.source.commit.operation
  have sourceLive : (tick.before.project engine).handles request.first = some resources.stage.container.handle := by
    rw [sourceFd]
    exact resources.stage.container.live
  have targetLive : (tick.before.project engine).handles request.second = some resources.parent.directory.handle := by
    rw [targetFd]
    exact resources.stage.parentLive
  have sourceBound : (tick.before.project engine).entries resources.stage.container.handle.object request.left =
      some root.root.object := by rw [sourceName]; exact root.bound
  have targetBound := acknowledgements.committed _ _ _ _ _ _ _ actual moving components sourceLive targetLive
    sourceBound zero empty
  rcases root.delta_cases change moving with unchanged | committed
  · have oldTarget : tick.before.shared.entries resources.parent.directory.handle.object request.right =
        some root.root.object := by rwa [unchanged] at targetBound
    have failure := kernel.rename_existing_error _ _ _ _ _ _ _ actual moving sourceLive targetLive oldTarget
    exact False.elim (failure zero)
  · exact committed

theorem AuthenticatedCommitResult.acknowledged_exposure {kernel : Contract}
    {runtime : PrimitiveActorRuntime kernel} (acknowledgements : RenameAcknowledgementContract kernel)
    {initial : World} {all processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {currentNative : NativeProcesses}
    {prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative}
    {actor : ActorId} {engine : EngineState} {request : Request} {reply : Reply}
    {hmac : ByteArray → ByteArray → ByteArray}
    (result : AuthenticatedCommitResult runtime prior actor engine request (some reply) hmac)
    (namespaceLaws : ByteNamespaceContract kernel semantics dataObjects)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, some reply)))
    (present : tick.before.actors actor = some engine) (moving : request.op = .renameNew)
    (zero : reply.1 = 0) (empty : reply.2 = .empty) :
    ∃ _delta : CommitDelta result.authority.resources result.root.root.object,
      ∃ marker : CommitMarkerAt (position := processed.length) runtime result.root hmac,
        Nonempty (ExposedSourceQuery runtime initial all hmac marker.receipt.key marker.receipt.message
          (processed.length + 1)) ∧
        result.updated.current.source.custody.caps =
          prior.current.source.custody.caps.published tick.after.shared result.root.root.object := by
  have actual := selected_filesystem_step tick action present
  have change := result.authority.namespace_delta namespaceLaws actual moving
  let source := result.authority.resources.source.source.commit
  have target := selected_parent_component result.authority.resources.source.source.target true source.selected
  have stage := selected_fresh_component source.parent source.created
  have components : ComponentRequest request :=
    (congrArg ComponentRequest source.operation).mpr ⟨stage.1, target.1⟩
  obtain ⟨delta⟩ := result.root.acknowledged_delta acknowledgements action present change moving components zero empty
  rcases result.effect with unchanged | committed
  · have bound := delta.bound
    rw [unchanged.1, delta.absent] at bound
    cases bound
  · exact committed

end LeanCage.Host.Kernel
