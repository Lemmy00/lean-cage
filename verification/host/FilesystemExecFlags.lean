import FilesystemInitial
import FilesystemDirectorySources
import FilesystemSpawnSources

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

def ClosedOpenRequest (request : Request) : Prop :=
  request.op = .openAt →
    request.second = readFlags ∨ request.second = directoryFlags ∨ request.second = newFileFlags

-- §AR-host-boundary.primitives: A lost allocation may still install its actual fresh raw FD.
structure CloseExecContract (kernel : Contract) : Prop where
  reference_origin : ∀ before after request observed fd handle,
    kernel.step before request observed after → after.handles fd = some handle →
    before.handles fd = some handle ∨ (AllocatesDescriptor request.op ∧ before.handles fd = none)
  allocated_closed : ∀ before after request observed fd handle,
    kernel.step before request observed after → AllocatesDescriptor request.op →
    before.handles fd = none → after.handles fd = some handle →
    (request.op = .openAt → request.second.toNat &&& 524288 = 524288) → after.closeOnExec fd = true
  retained_closed : ∀ before after request observed fd handle,
    kernel.step before request observed after → before.handles fd = some handle →
    after.handles fd = some handle → before.closeOnExec fd = true → after.closeOnExec fd = true

-- §AR-host-boundary.primitives: SDK calls keep each live raw lease; child tables are separate.
structure RuntimeCloseExecContract {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram) : Prop where
  other : ∀ {β : Type} actor (effect : Effect β) reply before after fd handle,
    runtime.other actor effect reply before after → before.handles fd = some handle →
    handle.rawOwned = true → after.handles fd = some handle →
    before.closeOnExec fd = true → after.closeOnExec fd = true

def FlagsCovered (world : World) (pending : List UInt64) : Prop :=
  ∀ fd handle, world.handles fd = some handle → world.closeOnExec fd = true ∨ fd ∈ pending

def RawClosedOnExec (world : World) : Prop := FlagsCovered world []

theorem closed_open_bit {request : Request} (source : ClosedOpenRequest request) (opening : request.op = .openAt) :
    request.second.toNat &&& 524288 = 524288 := by
  rcases source opening with read | directory | fresh
  · rw [read]; decide
  · rw [directory]; decide
  · rw [fresh]; decide

theorem step_flags_covered {kernel : Contract} (laws : CloseExecContract kernel)
    {before after : World} {request : Request} {observed : Option Reply} {pending : List UInt64}
    (actual : kernel.step before request observed after) (source : ClosedOpenRequest request)
    (covered : FlagsCovered before pending) : FlagsCovered after pending := by
  intro fd handle live
  rcases laws.reference_origin _ _ _ _ _ _ actual live with old | ⟨allocating, vacant⟩
  · rcases covered fd handle old with closed | waiting
    · exact .inl (laws.retained_closed _ _ _ _ _ _ actual old live closed)
    · exact .inr waiting
  · exact .inl (laws.allocated_closed _ _ _ _ _ _ actual allocating vacant live (closed_open_bit source))

theorem step_seal_flags_covered {kernel : Contract} (laws : CloseExecContract kernel)
    {before after : World} {fd : UInt64} {reply : Reply} {pending : List UInt64}
    (actual : kernel.step before {op := .closeOnExec, first := fd} (some reply) after)
    (covered : FlagsCovered before (fd :: pending)) (zero : reply.1 = 0) (empty : reply.2.isEmpty = true) :
    FlagsCovered after pending := by
  intro query handle live
  rcases laws.reference_origin _ _ _ _ _ _ actual live with old | ⟨allocating, vacant⟩
  · rcases covered query handle old with closed | waiting
    · exact .inl (laws.retained_closed _ _ _ _ _ _ actual old live closed)
    · rcases List.mem_cons.mp waiting with same | later
      · subst query
        exact .inl (kernel.close_exec _ _ _ _ actual rfl zero empty)
      · exact .inr later
  · simp [AllocatesDescriptor] at allocating

theorem runtime_flags_covered {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (references : RuntimeDescriptorContract runtime) (laws : RuntimeCloseExecContract runtime)
    {β : Type} {actor : ActorId} {effect : Effect β} {reply : Option β} {before after : World}
    {pending : List UInt64} (actual : runtime.other actor effect reply before after)
    (raw : RawReferences before.handles) (covered : FlagsCovered before pending) : FlagsCovered after pending := by
  intro fd handle live
  have old := references.new_reference _ _ _ _ _ _ _ actual live
  rcases covered fd handle old with closed | waiting
  · exact .inl (laws.other _ _ _ _ _ _ _ actual old (raw fd handle old) live closed)
  · exact .inr waiting

theorem initial_channels_covered {ipc : ObjectId → Prop} {world : World}
    (binding : InitialEngineBinding ipc world.handles world.closeOnExec) : FlagsCovered world [0, 1, 3] := by
  intro fd handle live
  rcases (initial_reference_ipc binding live).2 with zero | one | three
  · have same : fd = 0 := UInt64.toNat_inj.mp zero
    right; simp [same]
  · have same : fd = 1 := UInt64.toNat_inj.mp one
    right; simp [same]
  · have same : fd = 3 := UInt64.toNat_inj.mp three
    right; simp [same]

theorem passive_closed_open {request : Request} (source : NamespacePassive request) : ClosedOpenRequest request := by
  intro opening
  unfold NamespacePassive at source
  rw [opening] at source
  rcases source with read | directory
  · exact .inl read
  · exact .inr (.inl directory)

theorem safe_closed_open {request : Request} (source : Publication.SafeRequest request) :
    ClosedOpenRequest request := by
  intro opening
  unfold Publication.SafeRequest at source
  rw [opening] at source
  exact source

theorem safe_closed_program {α : Type} {program : Filesystem.Program α} (source : Publication.SafeProgram program) :
    RequestProgram ClosedOpenRequest program := by
  induction source with
  | pure => exact .pure _
  | call permitted following ih => exact .call (safe_closed_open permitted) ih

theorem run_creation_closed_program : RequestProgram ClosedOpenRequest RunDirectory.create := by
  apply request_weaken RunDirectory.create_requests
  intro request source opening
  unfold RunDirectory.DirectoryRequest at source
  rw [opening] at source
  exact .inr (.inl source)

theorem run_cleanup_closed_program (run : RunDirectory.Owned) :
    RequestProgram ClosedOpenRequest (RunDirectory.cleanup run) := by
  apply request_weaken (RunDirectory.cleanup_requests run)
  intro request source opening
  unfold RunDirectory.CleanupRequest at source
  rw [opening] at source
  exact False.elim source

theorem image_closed_program (run : UInt64) (bundle : Validation.Bundle) (overlay : List Image.Entry) :
    RequestProgram ClosedOpenRequest (Image.create run bundle overlay) := by
  unfold Image.create
  split
  · exact .pure _
  · apply request_bind (request_weaken
      (read_only_namespace_passive (Image.copyIdentified_readOnly _ _ _)) (fun _ => passive_closed_open))
    intro copied
    cases copied with
    | error => exact .pure _
    | ok base =>
      apply RequestProgram.call (by intro opening; exact .inr (.inr rfl))
      intro reply
      dsimp only [Filesystem.Program.bind]
      split
      · exact .pure _
      · apply request_weaken (Image.contentClose_requests _ _ _)
        intro request source opening
        rcases source with writing | closing
        · rw [writing.1] at opening; cases opening
        · rw [closing] at opening; cases opening

theorem publisher_closed_program {α : Type} {program : Filesystem.Program α}
    (source : Publication.PublisherProgram program) : RequestProgram ClosedOpenRequest program := by
  induction source with
  | pure => exact .pure _
  | call permitted following ih =>
    apply RequestProgram.call _ ih
    rcases permitted with rename | safe
    · intro opening
      rw [rename] at opening
      cases opening
    · exact safe_closed_open safe

theorem cleanup_closed_open (run : RunDirectory.Owned) (input : Publication.Input)
    {before : List Program.Event} {request : Request} {observed : Option Reply}
    (source : Program.Prefix (cleanupRun run input)
      (before ++ [Program.filesystemPrefixEvent (request, observed)])) : ClosedOpenRequest request := by
  have same : cleanupRun run input =
      if input.outcome.vmCleanup == "unknown" then Program.liftFilesystem (Validation.releaseDirectory run)
      else Program.liftFilesystem (RunDirectory.cleanup run) := rfl
  rw [same] at source
  split at source
  · exact passive_closed_open (selected_filesystem_profile (validator_release_passive run) source)
  · exact selected_filesystem_profile (run_cleanup_closed_program run) source

theorem validator_mutation_closed_open {bundle : Validation.Bundle} {raw : ByteArray}
    {before : List Program.Event} {request : Request} {observed : Option Reply}
    (source : ValidatorMutation bundle raw before (Program.filesystemPrefixEvent (request, observed))) :
    ClosedOpenRequest request := by
  cases source with
  | allocating active => exact selected_filesystem_profile run_creation_closed_program active
  | writing context inside active trace =>
    exact selected_filesystem_profile (safe_closed_program (Publication.writeNew_safe _ _ _ _)) active
  | cleaningFailedWrite context writing error written inside active trace =>
    exact selected_filesystem_profile (run_cleanup_closed_program _) active
  | cleaningObserved context inside reaped active trace =>
    exact selected_filesystem_profile (run_cleanup_closed_program _) active
  | releasingUnknown context inside unknown active trace =>
    exact passive_closed_open (selected_filesystem_profile (validator_release_passive _) active)

theorem run_mutation_closed_open {request : GatewayWire.Request} {bundle : Validation.Bundle}
    {duration : Option Nat} {before : List Program.Event} {operation : Request} {observed : Option Reply}
    (source : RunMutation request bundle duration before (Program.filesystemPrefixEvent (operation, observed))) :
    ClosedOpenRequest operation := by
  cases source with
  | preparing source =>
    cases source with
    | validating context inside source trace => exact validator_mutation_closed_open source
    | revalidating context inside source trace => exact validator_mutation_closed_open source
  | allocating context inside active trace => exact selected_filesystem_profile run_creation_closed_program active
  | imaging context inside active trace => exact selected_filesystem_profile (image_closed_program _ _ _) active
  | dispatching context inside active trace =>
    exact passive_closed_open (dispatch_namespace_passive _ _ _ _ _ _ _ _ active)
  | cleaning context inside active trace => exact cleanup_closed_open _ _ active
  | publishing context inside active trace =>
    exact selected_filesystem_profile
      (publisher_closed_program (Publication.publish_prefix_program _ _ _)) active

-- §FS-host-boundary.ownership: The actual source fixes every open mode, including all failures.
theorem entrypoint_closed_open {before : List Program.Event} {request : Request} {observed : Option Reply}
    (source : Program.Prefix Entrypoint.run (before ++ [Program.filesystemPrefixEvent (request, observed)])) :
    ClosedOpenRequest request := by
  by_cases passive : NamespacePassive request
  · exact passive_closed_open passive
  · obtain ⟨entry⟩ := entrypoint_mutation_origin source passive
    cases entry.source with
    | validating context raw loading loaded inside active trace =>
      obtain ⟨validator⟩ := validator_mutation_origin _ _ active
      exact validator_mutation_closed_open validator
    | executing context inside command active trace =>
      obtain ⟨run⟩ := run_mutation_origin _ _ _ active passive
      exact run_mutation_closed_open run

theorem selected_actor_closed_open {kernel : Contract} {runtime : ActorRuntime kernel}
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply} (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) : ClosedOpenRequest request :=
  entrypoint_closed_open (selected_source_prefix journal selected action present)

private theorem empty_history_flags {kernel : Contract} {before after : World}
    (history : History kernel before [] after) : after.closeOnExec = before.closeOnExec := by
  generalize shape : ([] : List (Request × Reply)) = events at history
  induction history with
  | nil => rfl
  | cons actual tail ih => cases shape
  | environment actual tail ih => exact (ih shape).trans (kernel.interference_close_exec _ _ actual)

private theorem empty_history_covered {kernel : Contract} {before after : World} {pending : List UInt64}
    (history : History kernel before [] after) (covered : FlagsCovered before pending) : FlagsCovered after pending := by
  intro fd handle live
  have sameHandles := random_history_handles history (by intro event member; cases member)
  rw [sameHandles] at live
  rw [empty_history_flags history]
  exact covered fd handle live

-- §FS-host-boundary.ownership: Each actual successful fcntl removes exactly its pending FD.
theorem seal_descriptors_covered {kernel : Contract} (laws : CloseExecContract kernel)
    (pending : List UInt64) {before after : World} {events : List (Request × Reply)}
    (source : ConcurrentRun kernel (Startup.sealDescriptors pending) before events after (.ok ()))
    (covered : FlagsCovered before pending) : RawClosedOnExec after := by
  induction pending generalizing before after events with
  | nil =>
    obtain ⟨rfl, _⟩ := Snapshot.returns_pure_eq source.1
    exact empty_history_covered source.2 covered
  | cons fd pending ih =>
    have program := source.1
    unfold Startup.sealDescriptors at program
    obtain ⟨reply, tail, shape, following⟩ := Snapshot.returns_call_split program
    split at following
    · cases following
    · rename_i accepted
      have successful : reply.1 = 0 ∧ reply.2.isEmpty = true := by
        simpa [Bool.or_eq_true] using accepted
      have history := source.2
      rw [shape] at history
      obtain ⟨actualBefore, actualAfter, leading, actual, rest⟩ := history_head history
      exact ih ⟨following, rest⟩ (step_seal_flags_covered laws actual
        (empty_history_covered leading covered) successful.1 successful.2)

theorem actual_startup_raw_closed {kernel : Contract} (laws : CloseExecContract kernel)
    {ipc : ObjectId → Prop} {before after : World} {events : List (Request × Reply)}
    (binding : InitialEngineBinding ipc before.handles before.closeOnExec)
    (source : ConcurrentRun kernel Startup.descriptors before events after (.ok ())) : RawClosedOnExec after :=
  seal_descriptors_covered laws [0, 1, 3] source (initial_channels_covered binding)

def ClosedEffect : {β : Type} → Effect β → Prop
  | _, .filesystem request => ClosedOpenRequest request
  | _, _ => True

theorem operation_flags_covered {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (laws : CloseExecContract kernel) (references : RuntimeDescriptorContract runtime)
    (runtimeLaws : RuntimeCloseExecContract runtime)
    {β : Type} {actor : ActorId} {effect : Effect β} {reply : Option β} {before after : World}
    {pending : List UInt64} (actual : ActorOperation runtime actor effect reply before after)
    (source : ClosedEffect effect) (raw : RawReferences before.handles) (covered : FlagsCovered before pending) :
    FlagsCovered after pending := by
  cases effect with
  | filesystem request => exact step_flags_covered laws actual source covered
  | spawn arguments => exact runtime_flags_covered references runtimeLaws actual raw covered
  | read handle amount => exact runtime_flags_covered references runtimeLaws actual raw covered
  | wait child => exact runtime_flags_covered references runtimeLaws actual raw covered
  | terminate child => exact runtime_flags_covered references runtimeLaws actual raw covered
  | tryWait child => exact runtime_flags_covered references runtimeLaws actual raw covered
  | descriptor handle => exact runtime_flags_covered references runtimeLaws actual raw covered

theorem recorded_closed_effect {kernel : Contract} {runtime : ActorRuntime kernel}
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {actor : ActorId} {ordinal : Nat} {β : Type} {effect : Effect β} {reply : β} {before after : World}
    (recorded : SourceReturnAt runtime ticks actor ordinal β effect reply before after) : ClosedEffect effect := by
  cases effect with
  | filesystem request =>
    obtain ⟨earlier, length, source⟩ := recorded_return_entry_prefix journal recorded
    exact entrypoint_closed_open (observed := some reply) source
  | spawn => trivial
  | read => trivial
  | wait => trivial
  | terminate => trivial
  | tryWait => trivial
  | descriptor => trivial

-- §FS-host-boundary.ownership: Same-journal source calls preserve sealing across all peer steps.
theorem recorded_raw_closed {kernel : Contract} {runtime : ActorRuntime kernel}
    (laws : CloseExecContract kernel) (descriptors : DescriptorContract kernel)
    (references : RuntimeDescriptorContract runtime) (runtimeLaws : RuntimeCloseExecContract runtime)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {actor : ActorId} {ordinal : Nat} {before after : World} {events : List Program.Event}
    (history : ActorHistoryWith runtime actor (SourceReturnAt runtime ticks actor) ordinal before events after)
    (raw : RawReferences before.handles) (closed : RawClosedOnExec before) : RawClosedOnExec after := by
  induction history with
  | nil => exact closed
  | returned actual recorded tail ih =>
    exact ih (actor_operation_after_raw descriptors references actual raw)
      (operation_flags_covered laws references runtimeLaws actual (recorded_closed_effect journal recorded) raw closed)
  | environment actual tail ih =>
    apply ih
    · rw [kernel.interference_handles _ _ actual]
      exact raw
    · intro fd handle live
      rw [kernel.interference_handles _ _ actual] at live
      rw [kernel.interference_close_exec _ _ actual]
      exact closed fd handle live

theorem actor_history_raw {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (descriptors : DescriptorContract kernel) (references : RuntimeDescriptorContract runtime)
    {actor : ActorId} {origin : OperationOrigin} {ordinal : Nat} {before after : World}
    {events : List Program.Event} (history : ActorHistoryWith runtime actor origin ordinal before events after)
    (raw : RawReferences before.handles) : RawReferences after.handles := by
  induction history with
  | nil => exact raw
  | returned actual recorded tail ih => exact ih (actor_operation_after_raw descriptors references actual raw)
  | environment actual tail ih =>
    apply ih
    rw [kernel.interference_handles _ _ actual]
    exact raw

-- §FS-host-boundary.ownership: No supplied sealing receipt replaces the actual startup prefix.
theorem actual_selected_spawn_raw_closed {kernel : Contract} {runtime : ActorRuntime kernel}
    (laws : CloseExecContract kernel) (descriptors : DescriptorContract kernel)
    (references : RuntimeDescriptorContract runtime) (runtimeLaws : RuntimeCloseExecContract runtime)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {arguments : IO.Process.SpawnArgs} {event : Program.Event}
    (selected : ticks[position]? = some tick) (action : tick.action.eventFor actor = some event)
    (present : tick.before.actors actor = some engine) (spawn : SpawnUse arguments event)
    {ipc : ObjectId → Prop} {handedOff : World}
    (binding : InitialEngineBinding ipc handedOff.handles handedOff.closeOnExec)
    (raw : RawReferences handedOff.handles)
    (history : ActorHistoryWith runtime actor (SourceReturnAt runtime ticks actor) 0
      handedOff engine.events (tick.before.project engine)) : RawClosedOnExec (tick.before.project engine) := by
  obtain ⟨entry⟩ := selected_spawn_source journal selected action present spawn
  let remaining := entry.packet.reading.map Program.filesystemEvent ++ entry.inside
  have shape : engine.events = entry.packet.ready.starting.map Program.filesystemEvent ++ remaining := by
    simpa only [EntrypointPrefixCuts.Read.events, EntrypointPrefixCuts.Ready.events, remaining,
      List.append_assoc] using entry.trace
  have indexed : ActorHistoryWith runtime actor (SourceReturnAt runtime ticks actor) 0 handedOff
      (entry.packet.ready.starting.map Program.filesystemEvent ++ remaining) (tick.before.project engine) := by
    rw [← shape]
    exact history
  obtain ⟨sealedWorld, starting, rest⟩ := actor_with_split
    (entry.packet.ready.starting.map Program.filesystemEvent) remaining indexed
  have filesystem := actor_recorded_filesystem starting
  have closed := actual_startup_raw_closed laws binding
    ⟨entry.packet.ready.startup, recorded_history_erase filesystem⟩
  exact recorded_raw_closed laws descriptors references runtimeLaws journal rest
    (actor_history_raw descriptors references starting raw) closed

end LeanCage.Host.Kernel
