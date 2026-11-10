import FilesystemPreparingStage
import FilesystemCheckedParents

namespace LeanCage.Host.Kernel
open Filesystem

structure PreparingStagePoint {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {before : List Program.Event} {request : Request}
    {call : PublicationPreparing.Call before request} {limit : Nat} {current : World}
    (source : PreparingStageContinuation runtime initial all call limit current) where
  inspectionRaw : List Program.Event
  inspectionExact : inspectionRaw = source.opening.after.map Program.filesystemEvent
  followingRaw : List Program.Event
  chunks : PrimitiveFilesystem.Chunks
    (call.inside.map Program.filesystemPrefixEvent)
    followingRaw
  trace : source.earlier.remaining = inspectionRaw ++ followingRaw
  world : World
  history : ActorHistoryWith runtime source.earlier.source.inputActor
    (SourceReturnAt runtime all source.earlier.source.inputActor)
    (source.earlier.source.input.events.length + 1 +
      (source.earlier.post.map Program.filesystemEvent).length + inspectionRaw.length)
    world (followingRaw ++ source.earlier.guards) current
  directory : world.handles call.context.stage.directory.fd = some source.earlier.source.opening.handle
  container : world.handles call.context.stage.container.fd = some source.root.use.parent
  directoryRaw : source.earlier.source.opening.handle.rawOwned = true
  containerRaw : source.root.use.parent.rawOwned = true
  distinct : call.context.stage.directory.fd ≠ call.context.stage.container.fd
  observation : ObservedDirectory kernel (fun ordinal request reply =>
    SourceReturnAt runtime all source.earlier.source.inputActor ordinal Reply (.filesystem request) reply)
    (source.earlier.source.input.events.length + 1 +
      (source.earlier.post.map Program.filesystemEvent).length + inspectionRaw.length)
    world call.context.parent.uid call.context.stage.directory
  sameObserved : observation.handle = source.earlier.source.opening.handle

-- §FS-host-boundary.publication: The real stage open/stat supplies the
-- references and actual metadata observation before interrupted preparation.
-- The same raw history contains every later returned call and current guard.
theorem PreparingStageContinuation.allocation {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel)
    {initial : World} {all : List (ActorTick runtime)} {before : List Program.Event} {request : Request}
    {call : PublicationPreparing.Call before request} {limit : Nat} {current : World}
    (source : PreparingStageContinuation runtime initial all call limit current) : Nonempty (PreparingStagePoint source) := by
  have chunks : PrimitiveFilesystem.Chunks (source.opening.after.map Program.filesystemEvent ++
      (call.inside.map Program.filesystemPrefixEvent))
      source.earlier.remaining := by simpa only [List.append_assoc] using source.earlier.chunks
  obtain ⟨inspectionRaw, followingRaw, inspectionChunks, followingChunks, trace⟩ :=
    PrimitiveFilesystem.chunks_split (source.opening.after.map Program.filesystemEvent) _ chunks
  have history : ActorHistoryWith runtime source.earlier.source.inputActor
      (SourceReturnAt runtime all source.earlier.source.inputActor) (source.earlier.source.input.events.length + 1)
      source.earlier.source.opening.after
      (source.earlier.post.map Program.filesystemEvent ++ (inspectionRaw ++ (followingRaw ++ source.earlier.guards))) current := by
    exact Eq.mp (congrArg (fun events => ActorHistoryWith runtime source.earlier.source.inputActor
      (SourceReturnAt runtime all source.earlier.source.inputActor) (source.earlier.source.input.events.length + 1)
      source.earlier.source.opening.after events current) (by simp only [trace, List.append_assoc])) source.earlier.tail
  obtain ⟨afterPost, postHistory, remaining⟩ := actor_with_split (source.earlier.post.map Program.filesystemEvent) _ history
  obtain ⟨afterInspection, inspectionHistory, followingHistory⟩ := actor_with_split inspectionRaw _ remaining
  have inspectionExact : inspectionRaw = source.opening.after.map Program.filesystemEvent :=
    PrimitiveFilesystem.chunks_identity inspectionChunks (by
      intro event member
      have same : event = .returned (.filesystem {
          op := .stat, first := call.context.stage.directory.fd}) source.informationReply := by
        simpa only [source.inspection, List.map_cons, List.map_nil, List.mem_singleton, Program.filesystemEvent] using member
      subst event
      rfl)
  have postFrame := actor_retaining_event_handles descriptors postHistory (by
    intro event member
    obtain ⟨⟨query, reply⟩, occurs, rfl⟩ := List.mem_map.mp member
    exact source.earlier.retaining (query, reply) occurs)
  have inspectionFrame := actor_retaining_event_handles descriptors inspectionHistory (by
    intro event member
    have same : event = .returned (.filesystem {
        op := .stat, first := call.context.stage.directory.fd}) source.informationReply := by
      simpa only [inspectionExact, source.inspection, List.map_cons, List.map_nil, List.mem_singleton,
        Program.filesystemEvent] using member
    subst event
    simp [RetainingEvent, RetainsDescriptors])
  have containerBefore : source.earlier.source.opening.before.handles call.context.stage.container.fd =
      some source.root.use.parent := by
    rw [source.earlier.source.before]
    change source.earlier.source.input.references call.context.stage.container.fd = some source.root.use.parent
    have sameFd : source.opening.request.first = call.context.stage.container.fd :=
      congrArg Request.first source.opening.operation
    rw [← sameFd]
    exact source.root.reference
  have containerOpened := descriptors.allocate_existing _ _ _ _ _ _ source.earlier.source.opening.actual
    (.inl source.opening.opening) containerBefore
  have fresh := (descriptors.allocated_fresh _ _ _ _ _ source.earlier.source.opening.actual
    (.inl source.opening.opening) source.earlier.source.opening.recognized).1
  have distinct : call.context.stage.directory.fd ≠ call.context.stage.container.fd := by
    intro same
    have sameSlot := congrArg source.earlier.source.opening.before.handles same
    have impossible := fresh.symm.trans (sameSlot.trans containerBefore)
    cases impossible
  have inspectedHistory : ActorHistoryWith runtime source.earlier.source.inputActor
      (SourceReturnAt runtime all source.earlier.source.inputActor)
      (source.earlier.source.input.events.length + 1 + (source.earlier.post.map Program.filesystemEvent).length)
      afterPost [.returned (.filesystem {
        op := .stat, first := call.context.stage.directory.fd}) source.informationReply] afterInspection := by
    exact Eq.mp (congrArg (fun events => ActorHistoryWith runtime source.earlier.source.inputActor
      (SourceReturnAt runtime all source.earlier.source.inputActor)
      (source.earlier.source.input.events.length + 1 + (source.earlier.post.map Program.filesystemEvent).length)
      afterPost events afterInspection) (inspectionExact.trans (by rw [source.inspection]; rfl))) inspectionHistory
  obtain ⟨observing, inspected, leading, statActual, statSample, afterStat⟩ := actor_with_head inspectedHistory
  change kernel.step observing {op := .stat, first := call.context.stage.directory.fd}
    (some source.informationReply) inspected at statActual
  have observingLive : observing.handles call.context.stage.directory.fd =
      some source.earlier.source.opening.handle := by
    rw [actor_retaining_event_handles descriptors leading (by intro event impossible; cases impossible), postFrame]
    exact source.earlier.source.opening.live
  let observation : ObservedDirectory kernel (fun ordinal request reply =>
      SourceReturnAt runtime all source.earlier.source.inputActor ordinal Reply (.filesystem request) reply)
      (source.earlier.source.input.events.length + 1 +
        (source.earlier.post.map Program.filesystemEvent).length + inspectionRaw.length)
      afterInspection call.context.parent.uid call.context.stage.directory := {
    handle := source.earlier.source.opening.handle
    live := by rw [inspectionFrame, postFrame]; exact source.earlier.source.opening.live
    raw := descriptors.after_raw _ _ _ _ source.earlier.source.opening.actual _ _ source.earlier.source.opening.live
    sample := {
      ordinal := source.earlier.source.input.events.length + 1 + (source.earlier.post.map Program.filesystemEvent).length
      before := observing
      after := inspected
      reply := source.informationReply
      actual := statActual
      sampled := statSample
      live := observingLive
      parsed := source.parsed }
    earlier := by
      have count : inspectionRaw.length = 1 := (congrArg List.length inspectionExact).trans (by
        simp only [source.inspection, List.length_map, List.length_singleton])
      dsimp only
      omega
    trusted := source.trusted }
  exact ⟨{
    inspectionRaw
    inspectionExact
    followingRaw
    chunks := followingChunks
    trace
    world := afterInspection
    history := followingHistory
    directory := by rw [inspectionFrame, postFrame]; exact source.earlier.source.opening.live
    container := by rw [inspectionFrame, postFrame]; exact containerOpened
    directoryRaw := descriptors.after_raw _ _ _ _ source.earlier.source.opening.actual _ _ source.earlier.source.opening.live
    containerRaw := descriptors.after_raw _ _ _ _ source.earlier.source.opening.actual _ _ containerOpened
    distinct
    observation
    sameObserved := rfl }⟩

end LeanCage.Host.Kernel
