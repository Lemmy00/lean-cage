import FilesystemCreatedStage
import FilesystemPrimitivePublication
import FilesystemSourceNondestructive
import FilesystemPublicationContentProfile

namespace LeanCage.Host.Kernel
open Filesystem
universe u

-- §FS-host-boundary.publication: The exact actual open handle survives its own returned
-- probes, inspection, complete preparation and current commit probes. Each frame comes
-- from those source operations and individual descriptor laws, not a whole-stage premise.
theorem CreatedStageContinuation.current_kept_reference {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel)
    {initial : World} {all : List (ActorTick runtime)} {before : List Program.Event} {request : Request} {observed : Option Reply}
    {call : HostCommitCall before request observed} {limit : Nat} {current : World}
    (source : CreatedStageContinuation runtime initial all call limit current)
    (guarded : ∀ event ∈ source.earlier.guards, RetainingEvent event)
    (held : UInt64) (handle : Handle)
    (live : source.earlier.source.opening.after.handles held = some handle) :
    current.handles held = some handle := by
  obtain ⟨inspectionRaw, preparingRaw, inspectionChunks, preparingChunks, rawTrace⟩ :=
    PrimitiveFilesystem.chunks_split (source.opening.after.map Program.filesystemEvent)
      (call.source.commit.preparing.map Program.filesystemEvent) source.earlier.chunks
  have changed := Eq.mp (congrArg (fun events => ActorHistoryWith runtime source.earlier.source.inputActor
    (SourceReturnAt runtime all source.earlier.source.inputActor) (source.earlier.source.input.events.length + 1)
    source.earlier.source.opening.after events current)
    (congrArg (fun inside : List Program.Event => source.earlier.post.map Program.filesystemEvent ++ inside ++ source.earlier.guards)
      rawTrace)) source.earlier.tail
  have history : ActorHistoryWith runtime source.earlier.source.inputActor
      (SourceReturnAt runtime all source.earlier.source.inputActor) (source.earlier.source.input.events.length + 1)
      source.earlier.source.opening.after
      (source.earlier.post.map Program.filesystemEvent ++ (inspectionRaw ++ (preparingRaw ++ source.earlier.guards))) current := by
    simpa only [List.append_assoc] using changed
  obtain ⟨afterPost, postHistory, rest⟩ := actor_with_split (source.earlier.post.map Program.filesystemEvent) _ history
  obtain ⟨afterInspection, inspectionHistory, rest⟩ := actor_with_split inspectionRaw _ rest
  obtain ⟨afterPreparation, preparationHistory, guards⟩ := actor_with_split preparingRaw source.earlier.guards rest
  have postLive : afterPost.handles held = some handle := by
    rw [actor_retaining_event_handles descriptors postHistory (by
      intro event member
      obtain ⟨⟨operation, reply⟩, occurs, same⟩ := List.mem_map.mp member
      subst event
      exact source.earlier.retaining (operation, reply) occurs)]
    exact live
  obtain ⟨information, inspection⟩ := source.opening.inspection
  have inspectionTrace : inspectionRaw = source.opening.after.map Program.filesystemEvent :=
    PrimitiveFilesystem.chunks_identity inspectionChunks (by
      intro event member
      rw [inspection] at member
      have same : event = .returned (.filesystem {op := .stat, first := call.source.commit.stage.directory.fd}) information := by
        simpa only [List.map_cons, List.map_nil, List.mem_singleton, Program.filesystemEvent] using member
      subst event
      exact PrimitiveFilesystem.stat_identity _)
  have inspectedLive : afterInspection.handles held = some handle := by
    rw [actor_retaining_event_handles descriptors inspectionHistory (by
      intro event member
      rw [inspectionTrace, inspection] at member
      have same : event = .returned (.filesystem {op := .stat, first := call.source.commit.stage.directory.fd}) information := by
        simpa only [List.map_cons, List.map_nil, List.mem_singleton, Program.filesystemEvent] using member
      subst event
      simp [RetainingEvent, RetainsDescriptors])]
    exact postLive
  obtain ⟨preparing, prepared, preparationTrace⟩ :=
    PrimitiveFilesystem.chunks_filesystem_returns call.source.commit.prepared preparingChunks
  have preparation : RecordedRun kernel (fun ordinal request reply =>
      SourceReturnAt runtime all source.earlier.source.inputActor ordinal Reply (.filesystem request) reply)
      (source.earlier.source.input.events.length + 1 + (source.earlier.post.map Program.filesystemEvent).length + inspectionRaw.length)
      (Publication.prepare call.invocation.authenticated.bundle call.source.effective call.source.commit.display
        call.source.stdoutHash call.source.stderrHash call.source.commit.parent call.source.commit.stage).lower
      afterInspection preparing afterPreparation (.ok call.source.commit.candidate) :=
    ⟨prepared, actor_recorded_filesystem (preparationTrace ▸ preparationHistory)⟩
  have preparedLive := (Lowered.history_borrow _ _
    (Lowered.publication_prepare_borrow descriptors held
      handle _ _ _ _ _ _ _) preparation inspectedLive).1
  rw [actor_retaining_event_handles descriptors guards guarded]
  exact preparedLive

-- §AR-host-boundary.interfaces: Preserve the existing actual opener-reference projection.
theorem CreatedStageContinuation.current_reference {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel)
    {initial : World} {all : List (ActorTick runtime)} {before : List Program.Event} {request : Request} {observed : Option Reply}
    {call : HostCommitCall before request observed} {limit : Nat} {current : World}
    (source : CreatedStageContinuation runtime initial all call limit current)
    (guarded : ∀ event ∈ source.earlier.guards, RetainingEvent event) :
    current.handles call.source.commit.stage.directory.fd = some source.earlier.source.opening.handle :=
  source.current_kept_reference descriptors guarded _ _ source.earlier.source.opening.live

theorem CreatedStageContinuation.remaining_nondestructive {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {before : List Program.Event} {request : Request} {observed : Option Reply}
    {call : HostCommitCall before request observed} {limit : Nat} {current : World}
    (source : CreatedStageContinuation runtime initial all call limit current) :
    ∀ event ∈ source.earlier.remaining, NondestructiveEvent event := by
  obtain ⟨inspectionRaw, preparingRaw, inspectionChunks, preparingChunks, rawTrace⟩ :=
    PrimitiveFilesystem.chunks_split (source.opening.after.map Program.filesystemEvent)
      (call.source.commit.preparing.map Program.filesystemEvent) source.earlier.chunks
  obtain ⟨information, inspection⟩ := source.opening.inspection
  have inspectionTrace : inspectionRaw = source.opening.after.map Program.filesystemEvent :=
    PrimitiveFilesystem.chunks_identity inspectionChunks (by
      intro event member
      rw [inspection] at member
      have same : event = .returned (.filesystem {op := .stat, first := call.source.commit.stage.directory.fd}) information := by
        simpa only [List.map_cons, List.map_nil, List.mem_singleton, Program.filesystemEvent] using member
      subst event
      exact PrimitiveFilesystem.stat_identity _)
  obtain ⟨preparing, prepared, preparationTrace⟩ :=
    PrimitiveFilesystem.chunks_filesystem_returns call.source.commit.prepared preparingChunks
  have profile := requests_returned (lower_nondestructive (publication_prepare_nondestructive
    call.invocation.authenticated.bundle call.source.effective call.source.commit.display
    call.source.stdoutHash call.source.stderrHash call.source.commit.parent call.source.commit.stage)) prepared
  intro event member
  have occurs : event ∈ inspectionRaw ++ preparingRaw := rawTrace ▸ member
  rcases List.mem_append.mp occurs with inspected | prepared
  · rw [inspectionTrace, inspection] at inspected
    have same : event = .returned (.filesystem {op := .stat, first := call.source.commit.stage.directory.fd}) information := by
      simpa only [List.map_cons, List.map_nil, List.mem_singleton, Program.filesystemEvent] using inspected
    subst event
    simp [NondestructiveEvent, DestructiveRequest]
  · rw [preparationTrace] at prepared
    obtain ⟨⟨operation, reply⟩, actualMember, same⟩ := List.mem_map.mp prepared
    subst event
    exact profile (operation, reply) actualMember

private theorem drop_append_allowed {α : Type u} {first last : List α} (count : Nat) (allowed : α → Prop)
    (leading : ∀ event ∈ first.drop count, allowed event) (trailing : ∀ event ∈ last, allowed event) :
    ∀ event ∈ (first ++ last).drop count, allowed event := by
  intro event member
  rw [List.drop_append] at member
  rcases List.mem_append.mp member with member | member
  · exact leading event member
  · exact trailing event (List.mem_of_mem_drop member)

-- §FS-host-boundary.ownership: From the actual mkdir through this selected commit,
-- the owner's source has no earlier unlink or rename. Other actors remain unrestricted
-- until their individual ownership transitions establish the constructed journal.
theorem CreatedStageContinuation.source_nondestructive {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {before : List Program.Event} {request : Request} {observed : Option Reply}
    {call : HostCommitCall before request observed} {limit : Nat} {current : World}
    (source : CreatedStageContinuation runtime initial all call limit current) (events : List Program.Event)
    (trace : events = source.earlier.source.input.events ++ .returned (.filesystem source.opening.request) source.opening.reply ::
      (source.earlier.post.map Program.filesystemEvent ++ source.earlier.remaining ++ source.earlier.guards))
    (guarded : ∀ event ∈ source.earlier.guards, NondestructiveEvent event) :
    ∀ event ∈ events.drop (source.root.use.engine.events.length + 1), NondestructiveEvent event := by
  apply trace.symm ▸ drop_append_allowed _ NondestructiveEvent ?_ ?_
  · intro event member
    exact passive_event_nondestructive (source.root.probes event member)
  · intro event member
    rcases List.mem_cons.mp member with rfl | member
    · simp only [NondestructiveEvent, DestructiveRequest, source.opening.opening]
      decide
    · rcases List.mem_append.mp member with member | member
      · rcases List.mem_append.mp member with member | member
        · obtain ⟨⟨operation, reply⟩, occurs, same⟩ := List.mem_map.mp member
          subst event
          exact namespace_passive_not_destructive (source.earlier.passive (operation, reply) occurs)
        · exact source.remaining_nondestructive event member
      · exact guarded event member

end LeanCage.Host.Kernel
