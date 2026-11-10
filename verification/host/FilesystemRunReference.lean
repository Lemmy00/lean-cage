import FilesystemCreatedRun
import FilesystemOutputBorrowing
import FilesystemDirectoryObservations

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: This is the same point after the actual run
-- creation, before its later image/validator/cleanup continuation. Both raw
-- references denote the original source-opened descriptions, not integer roles.
structure RunAllocationPoint {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {outside : List Program.Event}
    {created : List (Request × Reply)} {run : RunDirectory.Owned} {following : List Program.Event}
    {limit : Nat} {current : World}
    (source : CreatedRunContinuation runtime initial all outside created run following limit current) where
  createdAfter : List Program.Event
  createdExact : createdAfter = source.opening.after.map Program.filesystemEvent
  followingRaw : List Program.Event
  chunks : PrimitiveFilesystem.Chunks following followingRaw
  trace : source.earlier.remaining = createdAfter ++ followingRaw
  world : World
  history : ActorHistoryWith runtime source.earlier.source.inputActor
    (SourceReturnAt runtime all source.earlier.source.inputActor)
    (source.earlier.source.input.events.length + 1 +
      (source.earlier.post.map Program.filesystemEvent).length + createdAfter.length)
    world (followingRaw ++ source.earlier.guards) current
  directory : world.handles run.directory.fd = some source.earlier.source.opening.handle
  container : world.handles run.container.fd = some source.root.use.parent
  directoryRaw : source.earlier.source.opening.handle.rawOwned = true
  containerRaw : source.root.use.parent.rawOwned = true
  distinct : run.directory.fd ≠ run.container.fd
  observation : ObservedDirectory kernel (fun ordinal request reply =>
    SourceReturnAt runtime all source.earlier.source.inputActor ordinal Reply (.filesystem request) reply)
    (source.earlier.source.input.events.length + 1 +
      (source.earlier.post.map Program.filesystemEvent).length + createdAfter.length)
    world source.opening.uid run.directory
  sameObserved : observation.handle = source.earlier.source.opening.handle

theorem CreatedRunContinuation.allocation {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel)
    {initial : World} {all : List (ActorTick runtime)} {outside : List Program.Event}
    {created : List (Request × Reply)} {run : RunDirectory.Owned} {following : List Program.Event}
    {limit : Nat} {current : World}
    (source : CreatedRunContinuation runtime initial all outside created run following limit current) :
    Nonempty (RunAllocationPoint source) := by
  obtain ⟨createdAfter, followingRaw, firstChunks, followingChunks, trace⟩ :=
    PrimitiveFilesystem.chunks_split (source.opening.after.map Program.filesystemEvent) following source.earlier.chunks
  have history : ActorHistoryWith runtime source.earlier.source.inputActor
      (SourceReturnAt runtime all source.earlier.source.inputActor)
      (source.earlier.source.input.events.length + 1) source.earlier.source.opening.after
      (source.earlier.post.map Program.filesystemEvent ++ (createdAfter ++ (followingRaw ++ source.earlier.guards))) current := by
    exact Eq.mp (congrArg (fun events => ActorHistoryWith runtime source.earlier.source.inputActor
      (SourceReturnAt runtime all source.earlier.source.inputActor)
      (source.earlier.source.input.events.length + 1) source.earlier.source.opening.after events current)
      (by simp only [trace, List.append_assoc])) source.earlier.tail
  obtain ⟨afterPost, postHistory, remaining⟩ :=
    actor_with_split (source.earlier.post.map Program.filesystemEvent) _ history
  obtain ⟨afterCreate, creatingHistory, followingHistory⟩ := actor_with_split createdAfter _ remaining
  have createdTrace : createdAfter = source.opening.after.map Program.filesystemEvent :=
    PrimitiveFilesystem.chunks_identity firstChunks source.opening.identity
  have postFrame := actor_retaining_event_handles descriptors postHistory (by
    intro event member
    obtain ⟨⟨request, reply⟩, occurs, rfl⟩ := List.mem_map.mp member
    exact source.earlier.retaining (request, reply) occurs)
  have createdFrame := actor_retaining_event_handles descriptors creatingHistory (by
    intro event member
    rw [createdTrace] at member
    obtain ⟨⟨request, reply⟩, occurs, rfl⟩ := List.mem_map.mp member
    exact source.opening.retaining (request, reply) occurs)
  have containerBefore : source.earlier.source.opening.before.handles run.container.fd =
      some source.root.use.parent := by
    rw [source.earlier.source.before]
    change source.earlier.source.input.references run.container.fd = some source.root.use.parent
    have sameFD : source.opening.request.first = run.container.fd := congrArg Request.first source.opening.operation
    rw [← sameFD]
    exact source.root.reference
  have containerOpened := descriptors.allocate_existing _ _ _ _ _ _ source.earlier.source.opening.actual
    (.inl source.opening.opening) containerBefore
  have fresh := (descriptors.allocated_fresh _ _ _ _ _ source.earlier.source.opening.actual
    (.inl source.opening.opening) source.earlier.source.opening.recognized).1
  have distinct : run.directory.fd ≠ run.container.fd := by
    intro same
    have sameSlot := congrArg source.earlier.source.opening.before.handles same
    have impossible := fresh.symm.trans (sameSlot.trans containerBefore)
    cases impossible
  have inspectedHistory : ActorHistoryWith runtime source.earlier.source.inputActor
      (SourceReturnAt runtime all source.earlier.source.inputActor)
      (source.earlier.source.input.events.length + 1 + (source.earlier.post.map Program.filesystemEvent).length)
      afterPost (source.opening.after.map Program.filesystemEvent) afterCreate := createdTrace ▸ creatingHistory
  have inspection : source.opening.after.map Program.filesystemEvent =
      [.returned (.filesystem {op := .stat, first := run.directory.fd}) source.opening.informationReply,
        .returned (.filesystem {
          op := .setAttribute
          first := run.directory.fd
          left := PrivateNames.attributeName
          right := PrivateNames.attributeValue }) source.opening.markerReply] := by
    exact (congrArg (List.map Program.filesystemEvent) source.opening.afterShape).trans rfl
  have actualInspection := Eq.mp (congrArg (fun events => ActorHistoryWith runtime source.earlier.source.inputActor
    (SourceReturnAt runtime all source.earlier.source.inputActor)
    (source.earlier.source.input.events.length + 1 + (source.earlier.post.map Program.filesystemEvent).length)
    afterPost events afterCreate) inspection) inspectedHistory
  obtain ⟨observing, inspected, leading, statActual, statSample, afterStat⟩ := actor_with_head actualInspection
  have observingLive : observing.handles run.directory.fd = some source.earlier.source.opening.handle := by
    rw [actor_retaining_event_handles descriptors leading (by intro event impossible; cases impossible), postFrame]
    exact source.earlier.source.opening.live
  let observation : ObservedDirectory kernel (fun ordinal request reply =>
      SourceReturnAt runtime all source.earlier.source.inputActor ordinal Reply (.filesystem request) reply)
      (source.earlier.source.input.events.length + 1 +
        (source.earlier.post.map Program.filesystemEvent).length + createdAfter.length)
      afterCreate source.opening.uid run.directory := {
    handle := source.earlier.source.opening.handle
    live := by rw [createdFrame, postFrame]; exact source.earlier.source.opening.live
    raw := descriptors.after_raw _ _ _ _ source.earlier.source.opening.actual _ _ source.earlier.source.opening.live
    sample := {
      ordinal := source.earlier.source.input.events.length + 1 + (source.earlier.post.map Program.filesystemEvent).length
      before := observing
      after := inspected
      reply := source.opening.informationReply
      actual := statActual
      sampled := statSample
      live := observingLive
      parsed := source.opening.parsed }
    earlier := by
      dsimp only
      have count := congrArg List.length (createdTrace.trans inspection)
      simp only [List.length_cons, List.length_nil] at count
      omega
    trusted := source.opening.trusted }
  exact ⟨{
    createdAfter
    createdExact := createdTrace
    followingRaw
    chunks := followingChunks
    trace
    world := afterCreate
    history := followingHistory
    directory := by rw [createdFrame, postFrame]; exact source.earlier.source.opening.live
    container := by rw [createdFrame, postFrame]; exact containerOpened
    directoryRaw := descriptors.after_raw _ _ _ _ source.earlier.source.opening.actual _ _ source.earlier.source.opening.live
    containerRaw := descriptors.after_raw _ _ _ _ source.earlier.source.opening.actual _ _ containerOpened
    distinct
    observation
    sameObserved := rfl }⟩

-- §FS-host-boundary.ownership: The actual euid before this run's mkdir is
-- selected from the original source chunk, independently of later success.
theorem CreatedRunContinuation.uid_sample {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {outside : List Program.Event}
    {created : List (Request × Reply)} {run : RunDirectory.Owned} {following : List Program.Event}
    {limit : Nat} {current : World}
    (source : CreatedRunContinuation runtime initial all outside created run following limit current) :
    Nonempty (UidSample kernel (fun ordinal request reply =>
      SourceReturnAt runtime all source.earlier.source.inputActor ordinal Reply (.filesystem request) reply) source.opening.uid) := by
  have trace : source.earlier.source.adapter.occurrence.logicalBefore = outside ++
      .returned (.filesystem {op := .euid}) source.opening.uidReply ::
        source.opening.uidFollowing.map Program.filesystemEvent := by
    exact source.earlier.source.logicalBefore.trans
      ((congrArg (fun events : List (Request × Reply) => outside ++ events.map Program.filesystemEvent)
        source.opening.beforeUid).trans rfl)
  obtain ⟨observation⟩ := primitive_observation source.earlier.source.adapter trace PrimitiveFilesystem.euid_identity
  exact ⟨⟨observation.rawBefore.length, observation.before, observation.after, source.opening.uidReply,
    observation.actual, observation.sampled, source.opening.uidSuccess, source.opening.uidEmpty, source.opening.uidValue⟩⟩

-- §FS-host-boundary.ownership: Completed source calls retain the SAME actual
-- borrowed reference. Runtime results and filesystem replies are taken from
-- this exact history, including interleaved foreign/native operations.
theorem actor_borrow_recorded_returns {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {actor : ActorId} {held : UInt64} {handle : Handle}
    {α : Type} {program : Program α} {post : α → Prop}
    (source : ActorBorrowPost runtime actor held handle post program)
    {origin : OperationOrigin} {ordinal : Nat} {before after : World} {events : List Program.Event} {value : α}
    (history : ActorHistoryWith runtime actor origin ordinal before events after)
    (returned : Program.Returns program events value) (live : before.handles held = some handle) :
    after.handles held = some handle ∧ post value := by
  induction history generalizing program with
  | nil =>
    cases returned
    cases source with
    | pure property => exact ⟨live, property⟩
  | returned actual sampled tail ih =>
    cases returned with
    | call effect next reply rest value continued =>
      cases source with
      | call preserve following => exact ih (following _ _ _ actual live) continued (preserve _ _ _ actual live)
  | environment actual tail ih =>
    apply ih source returned
    rw [kernel.interference_handles _ _ actual]
    exact live

theorem RunAllocationPoint.after_kept_returns {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {outside : List Program.Event}
    {created : List (Request × Reply)} {run : RunDirectory.Owned} {following : List Program.Event}
    {limit : Nat} {current : World}
    {source : CreatedRunContinuation runtime initial all outside created run following limit current}
    (point : RunAllocationPoint source)
    (descriptors : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (live : point.world.handles held = some handle)
    {α : Type} {program : Program α} {value : α}
    (returned : Program.Returns program following value)
    (borrowed : ActorBorrowPost runtime source.earlier.source.inputActor held
      handle (fun _ => True) (PrimitiveFilesystem.lower program))
    (guards : ∀ event ∈ source.earlier.guards, RetainingEvent event) :
    current.handles held = some handle := by
  obtain ⟨afterProgram, history, guarded⟩ := actor_with_split point.followingRaw _ point.history
  have actual := PrimitiveFilesystem.chunks_returns returned point.chunks
  have retained := (actor_borrow_recorded_returns borrowed history actual live).1
  rw [actor_retaining_event_handles descriptors guarded guards]
  exact retained

theorem RunAllocationPoint.after_returns {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {outside : List Program.Event}
    {created : List (Request × Reply)} {run : RunDirectory.Owned} {following : List Program.Event}
    {limit : Nat} {current : World}
    {source : CreatedRunContinuation runtime initial all outside created run following limit current}
    (point : RunAllocationPoint source) (descriptors : DescriptorContract kernel)
    {α : Type} {program : Program α} {value : α}
    (returned : Program.Returns program following value)
    (borrowed : ActorBorrowPost runtime source.earlier.source.inputActor run.directory.fd
      source.earlier.source.opening.handle (fun _ => True) (PrimitiveFilesystem.lower program))
    (guards : ∀ event ∈ source.earlier.guards, RetainingEvent event) :
    current.handles run.directory.fd = some source.earlier.source.opening.handle :=
  point.after_kept_returns descriptors _ _ point.directory returned borrowed guards

end LeanCage.Host.Kernel
