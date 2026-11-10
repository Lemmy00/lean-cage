import FilesystemWriteSources.Refined
import FilesystemPendingWrites
import FilesystemPendingProgramPhases
import FilesystemDescriptionOrigins
import FilesystemChannelVM

namespace LeanCage.Host.EntrypointWriterPrefix
open Filesystem Kernel

private theorem inherited_allocated {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    (history : SelectedActorHistory runtime initial all tick actor engine)
    {fd : UInt64} {handle : Handle} (reference : history.launch.references fd = some handle) :
    let world := history.launch.tick.after.project (.initialFrom (PrimitiveFilesystem.lower Entrypoint.run)
      history.launch.references history.launch.closeExec history.launch.workingDirectory)
    world.allocated handle.object = true ∧ world.descriptionAllocated handle.description = true := by
  have consistent := (actor_journal_consistent descriptors lifetimes references journal
    (empty_population_consistent initial)).2 history.launch.tick history.launchedHere |>.2
  have present := handoff_engine_present history.launch
  have valid := consistent actor _ present fd handle reference
  exact ⟨valid.1, valid.2.1⟩

private theorem descriptions_allocated {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} (references : ReferenceContract runtime)
    {actor : ActorId} {origin : OperationOrigin} {ordinal : Nat} {before after : World}
    {events : List Program.Event} (history : ActorHistoryWith runtime actor origin ordinal before events after)
    {description : DescriptionId} (allocated : before.descriptionAllocated description = true) :
    after.descriptionAllocated description = true := by
  induction history with
  | nil => exact allocated
  | environment actual tail ih => exact ih (kernel.interference_description_allocation _ _ _ actual allocated)
  | returned actual sampled tail ih => exact ih (operation_description_allocated references actual _ allocated)

private theorem phase_raw {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {α : Type} {program : Filesystem.Program α}
    (phase : PendingPrefixPhase runtime initial all tick actor engine request program) :
    RawPrefixHistory kernel.step kernel.interference (SourceRawAt runtime all actor) phase.rawBefore.length
      phase.before (Publication.completed phase.earlier) (tick.before.project engine) := by
  have history := raw_history_then_prefix phase.sampled
    (RawPrefixHistory.stop (step := kernel.step) (interference := kernel.interference)
      (origin := SourceRawAt runtime all actor) _ (tick.before.project engine))
  simpa only [Publication.completed, List.append_nil] using history

private theorem fresh_reference_conflict {before current : World} {fd : UInt64} {handle : Handle} {object : ObjectId}
    (fresh : ∃ candidate, current.handles fd = some candidate ∧ before.allocated candidate.object = false)
    (live : current.handles fd = some handle) (sameObject : handle.object = object)
    (allocated : before.allocated object = true) : False := by
  obtain ⟨candidate, present, fresh⟩ := fresh
  have same := Option.some.inj (present.symm.trans live)
  have old : before.allocated candidate.object = true :=
    (congrArg Handle.object same).trans sameObject ▸ allocated
  rw [old] at fresh
  cases fresh

-- §FS-host-boundary.caller: Actual application file and VM-control writes cannot target
-- the SAME inherited endpoint/OFD. A pending write on it is the real encoded response writer.
theorem inherited_response {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (introductions : DescriptionIntroductionContract kernel)
    (retirement : DescriptorRetirementContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState} {request : Request}
    (present : tick.before.actors actor = some engine)
    (history : SelectedActorHistory runtime initial all tick actor engine)
    (pending : PendingCut engine request) (writing : request.op = .write)
    {inheritedFd : UInt64} {inheritedHandle handle : Handle}
    (inherited : history.launch.references inheritedFd = some inheritedHandle)
    (live : engine.references request.first = some handle)
    (sameObject : handle.object = inheritedHandle.object) (sameDescription : handle.description = inheritedHandle.description) :
    Nonempty (ResponseFrontier pending.occurrence.logicalBefore request none) := by
  have inheritedFacts := inherited_allocated descriptors lifetimes references journal history inherited
  cases origin : pending.origin with
  | response frontier => exact ⟨frontier⟩
  | application context input packet inside active trace =>
    obtain ⟨call⟩ := WriteSources.command_call input active writing
    obtain ⟨refined⟩ := (call.outer context.events trace).refine writing
    cases refined with
    | file parent name bytes mode source =>
      obtain ⟨phase, sameSource, samePending⟩ := pending_filesystem_prefix_phase_exact history pending
        (writeNew parent name bytes mode) source.active source.trace
      have initial := Eq.mpr (congrArg (fun actual : SelectedActorHistory runtime initial all tick actor engine =>
        (actual.launch.tick.after.project (.initialFrom (PrimitiveFilesystem.lower Entrypoint.run)
          actual.launch.references actual.launch.closeExec actual.launch.workingDirectory)).allocated inheritedHandle.object = true)
        sameSource) inheritedFacts.1
      have allocated := actor_history_allocated lifetimes phase.leading initial
      exact False.elim (fresh_reference_conflict
        (pending_new_file_reference descriptors parent name bytes mode phase.active (phase_raw phase) writing)
        live sameObject allocated)
    | image runFd bundle overlay source =>
      obtain ⟨phase, sameSource, samePending⟩ := pending_filesystem_prefix_phase_exact history pending
        (Image.create runFd bundle overlay) source.active source.trace
      have initial := Eq.mpr (congrArg (fun actual : SelectedActorHistory runtime initial all tick actor engine =>
        (actual.launch.tick.after.project (.initialFrom (PrimitiveFilesystem.lower Entrypoint.run)
          actual.launch.references actual.launch.closeExec actual.launch.workingDirectory)).allocated inheritedHandle.object = true)
        sameSource) inheritedFacts.1
      have allocated := actor_history_allocated lifetimes phase.leading initial
      exact False.elim (fresh_reference_conflict
        (pending_image_reference descriptors runFd bundle overlay phase.active (phase_raw phase) writing)
        live sameObject allocated)
    | machine bundle directory duration transport source =>
      obtain ⟨phase, sameSource, samePending⟩ := pending_program_prefix_phase_exact history pending
        (VirtualMachine.run bundle directory duration transport) source.active source.trace
      have initialDescription := Eq.mpr (congrArg (fun actual : SelectedActorHistory runtime initial all tick actor engine =>
        (actual.launch.tick.after.project (.initialFrom (PrimitiveFilesystem.lower Entrypoint.run)
          actual.launch.references actual.launch.closeExec actual.launch.workingDirectory)).descriptionAllocated
          inheritedHandle.description = true) sameSource) inheritedFacts.2
      have old : phase.before.descriptionAllocated handle.description = true :=
        descriptions_allocated references phase.leading (by simpa only [sameDescription] using initialDescription)
      have previous := actor_history_old_description_backward descriptors introductions retirement sdk references
        phase.actual (fun _ _ _ _ _ _ sample => source_return_closed_effect journal sample) old live
      have member : tick ∈ all := Eq.mpr (congrArg (fun ticks => tick ∈ ticks) history.shape) (by simp)
      have raw := (actual_journal_raw descriptors sdk journal).2 tick member |>.1
      have certificate := VirtualMachine.channel_run (runtime := runtime) descriptors sdk actor request.first handle
        (raw actor engine present _ handle live) bundle directory duration transport
      have excluded := channel_pending_avoids (channel_lower certificate) phase.actual phase.active previous writing
      exact False.elim (excluded rfl)

-- §FS-host-boundary.acceptance: Handoff and pending source are produced from the SAME
-- global journal. The stream adapter supplies only its actual endpoint/OFD identity binding.
theorem actual_pending_inherited_response {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (introductions : DescriptionIntroductionContract kernel)
    (retirement : DescriptorRetirementContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (environment : InterferenceContract kernel)
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {position : Nat} {tick : ActorTick runtime} (selected : all[position]? = some tick)
    {actor : ActorId} {engine : EngineState} (present : tick.before.actors actor = some engine)
    (running : engine.running = true) {request : Request} {next : Reply → Program UInt32}
    (head : engine.current = .call (.filesystem request) next) (writing : request.op = .write) :
    ∃ (history : SelectedActorHistory runtime initial all tick actor engine) (pending : PendingCut engine request),
      ∀ inheritedFd inheritedHandle handle, history.launch.references inheritedFd = some inheritedHandle →
        engine.references request.first = some handle → handle.object = inheritedHandle.object →
        handle.description = inheritedHandle.description →
        Nonempty (ResponseFrontier pending.occurrence.logicalBefore request none) := by
  obtain ⟨history⟩ := actual_running_actor_history descriptors lifetimes references environment journal selected present running
  obtain ⟨pending⟩ := pending_write_at journal selected present running head writing
  exact ⟨history, pending, fun _ _ _ inherited live sameObject sameDescription =>
    inherited_response descriptors introductions retirement sdk lifetimes references journal present history pending writing
      inherited live sameObject sameDescription⟩

end LeanCage.Host.EntrypointWriterPrefix
