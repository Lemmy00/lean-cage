import FilesystemCommitRoles

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.publication: The actual namespace commit is independent of its
-- acknowledgement. All fields name this invocation's source and target objects/names.
structure CommitDelta {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (resources : PrimitiveCommitResources runtime initial all tick actor engine request observed) (root : ObjectId) : Prop where
  absent : tick.before.shared.entries resources.parent.directory.handle.object resources.source.source.commit.parent.name = none
  gone : tick.after.shared.entries resources.stage.container.handle.object resources.source.source.commit.stage.name = none
  bound : tick.after.shared.entries resources.parent.directory.handle.object resources.source.source.commit.parent.name = some root
  entries : ∀ parent name object, tick.after.shared.entries parent name = some object →
    (parent = resources.parent.directory.handle.object ∧ name = resources.source.source.commit.parent.name ∧ object = root) ∨
      tick.before.shared.entries parent name = some object

-- §FS-host-boundary.publication: The broad actual one-syscall relation retains either
-- no namespace change or this exact own-root move, including committed error and loss.
theorem CommitRootAt.delta_cases {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    {resources : PrimitiveCommitResources runtime initial all tick actor engine request observed}
    {family : Family} {catalogue : Catalogue runtime all}
    (source : CommitRootAt runtime resources family catalogue) {dataObjects : ObjectId → Prop}
    (change : DataChange dataObjects request (tick.before.project engine) tick.after.shared)
    (moving : request.op = .renameNew) :
    tick.after.shared.entries = tick.before.shared.entries ∨ Nonempty (CommitDelta resources source.root.object) := by
  cases change with
  | unchanged entries => exact .inl entries
  | created parent object operation reference parentLive fresh allocated data absent entries =>
    rcases operation with mkdir | ⟨opening, flags⟩
    · rw [moving] at mkdir; cases mkdir
    · rw [moving] at opening; cases opening
  | removed operation entries => rw [moving] at operation; cases operation
  | renamed first target object operation firstReference targetReference targetLive
      firstBinding targetAbsent sourceGone targetBinding entries =>
    have firstFd : request.first = resources.source.source.commit.stage.container.fd :=
      congrArg Request.first resources.source.source.commit.operation
    have targetFd : request.second = resources.source.source.commit.parent.directory.fd :=
      congrArg Request.second resources.source.source.commit.operation
    have firstName : request.left = resources.source.source.commit.stage.name :=
      congrArg Request.left resources.source.source.commit.operation
    have targetName : request.right = resources.source.source.commit.parent.name :=
      congrArg Request.right resources.source.source.commit.operation
    have firstSame : first = resources.stage.container.handle :=
      Option.some.inj ((firstFd ▸ firstReference).symm.trans resources.stage.container.live)
    have targetSame : target = resources.parent.directory.handle :=
      Option.some.inj ((targetFd ▸ targetReference).symm.trans resources.stage.parentLive)
    have firstBinding : tick.before.shared.entries resources.stage.container.handle.object
        resources.source.source.commit.stage.name = some object := by
      simpa only [firstSame, firstName, Population.project] using firstBinding
    have sameObject : object = source.root.object := Option.some.inj (firstBinding.symm.trans source.bound)
    exact .inr ⟨{
      absent := by simpa only [targetSame, targetName, Population.project] using targetAbsent
      gone := by simpa only [firstSame, firstName] using sourceGone
      bound := by simpa only [targetSame, targetName, sameObject] using targetBinding
      entries := by
        intro parent name object bound
        rcases entries parent name object bound with inserted | old
        · exact .inl ⟨inserted.1.trans (congrArg Handle.object targetSame), inserted.2.1.trans targetName,
            inserted.2.2.trans sameObject⟩
        · exact .inr old }⟩

end LeanCage.Host.Kernel
