import FilesystemPrimitiveSources
import FilesystemAccessJournal
import FilesystemHandoff

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

-- §FS-host-boundary.acceptance: Both lost and returned raw syscalls retain the same global tick.
def SourceRawAt {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram)
    (ticks : List (ActorTick runtime)) (actor : ActorId) : RawOrigin :=
  fun ordinal request observed before after =>
    ∃ (position : Nat) (tick : ActorTick runtime) (initial final : EngineState),
      ticks[position]? = some tick ∧
      tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)) ∧
      tick.before.actors actor = some initial ∧ tick.after.actors actor = some final ∧
      initial.events.length = ordinal ∧ before = tick.before.project initial ∧ after = tick.after.project final

theorem returned_source_raw {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {ticks : List (ActorTick runtime)} {actor : ActorId} {ordinal : Nat}
    {request : Request} {reply : Reply} {before after : World}
    (source : SourceReturnAt runtime ticks actor ordinal Reply (.filesystem request) reply before after) :
    SourceRawAt runtime ticks actor ordinal request (some reply) before after := by
  obtain ⟨position, tick, initial, final, selected, action, input, output, count, first, last⟩ := source
  exact ⟨position, tick, initial, final, selected,
    by simp only [action, ActorAction.eventFor, ↓reduceIte, Program.filesystemPrefixEvent],
    input, output, count, first, last⟩

theorem actor_raw_filesystem {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {ticks : List (ActorTick runtime)} {actor : ActorId} {ordinal : Nat}
    {before after : World} {events : List (Request × Option Reply)}
    (history : ActorHistoryWith runtime actor (SourceReturnAt runtime ticks actor) ordinal before
      (events.map Program.filesystemPrefixEvent) after) :
    ∃ completed, events = completed.map (fun item => (item.1, some item.2)) ∧
      RawHistory kernel.step kernel.interference (SourceRawAt runtime ticks actor) ordinal before completed after := by
  generalize shape : events.map Program.filesystemPrefixEvent = all at history
  induction history generalizing events with
  | nil =>
    cases events <;> cases shape
    exact ⟨[], rfl, .nil _ _⟩
  | returned actual recorded tail ih =>
    cases events with
    | nil => cases shape
    | cons event rest =>
      rcases event with ⟨request, observed⟩
      cases observed with
      | none => cases shape
      | some reply =>
        cases shape
        obtain ⟨completed, trace, actualTail⟩ := ih rfl
        exact ⟨(request, reply) :: completed, by simp only [List.map_cons, trace],
          .call actual (returned_source_raw recorded) actualTail⟩
  | environment actual tail ih =>
    obtain ⟨completed, trace, rest⟩ := ih shape
    exact ⟨completed, trace, .environment actual rest⟩

theorem raw_history_then_prefix {step : RawStep} {interference : RawInterference} {origin : RawOrigin}
    {ordinal : Nat} {before middle after : World} {first : List (Request × Reply)}
    {last : List (Request × Option Reply)} (initial : RawHistory step interference origin ordinal before first middle)
    (final : RawPrefixHistory step interference origin (ordinal + first.length) middle last after) :
    RawPrefixHistory step interference origin ordinal before
      (first.map (fun item => (item.1, some item.2)) ++ last) after := by
  induction initial with
  | nil => exact final
  | call actual sampled tail ih =>
    apply RawPrefixHistory.returned actual sampled
    apply ih
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using final
  | environment actual tail ih => exact .environment actual (ih final)

-- §AR-host-boundary.primitives: The selected row's post-table is the actual table after that call.
theorem selected_raw_kernel_step {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {ticks : List (ActorTick runtime)} {position : Nat} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) :
    ∃ final, tick.after.actors actor = some final ∧
      kernel.step (tick.before.project engine) request observed (tick.after.project final) ∧
      SourceRawAt runtime ticks actor engine.events.length request observed
        (tick.before.project engine) (tick.after.project final) := by
  rcases tick with ⟨kind, before, after, actual⟩
  cases actual with
  | launch => cases action
  | @returned β population owner current effect next reply world found alive head operation =>
    dsimp only [ActorAction.eventFor] at action
    split at action
    · rename_i same
      subst owner
      cases observed with
      | none => cases action
      | some observed =>
        cases action
        have sameEngine := Option.some.inj (present.symm.trans found)
        subst engine
        let final := current.returned (.filesystem request) observed next world
        refine ⟨final, ?_, operation, ?_⟩
        · simp only [Population.advance, Population.install, ↓reduceIte, final]
        · refine ⟨position, _, current, final, selected,
          by simp only [ActorAction.eventFor, ↓reduceIte, Program.filesystemPrefixEvent],
          found, ?_, rfl, rfl, rfl⟩
          simp only [Population.advance, Population.install, ↓reduceIte, final]
    · cases action
  | @lost β population owner current effect next world found alive head operation =>
    dsimp only [ActorAction.eventFor] at action
    split at action
    · rename_i same
      subst owner
      cases observed with
      | some observed => cases action
      | none =>
        cases action
        have sameEngine := Option.some.inj (present.symm.trans found)
        subst engine
        let final := current.lost (.filesystem request) world
        refine ⟨final, ?_, operation, ?_⟩
        · simp only [Population.advance, Population.install, ↓reduceIte, final]
        · refine ⟨position, _, current, final, selected,
          by simp only [ActorAction.eventFor, ↓reduceIte, Program.filesystemPrefixEvent],
          found, ?_, rfl, rfl, rfl⟩
          simp only [Population.advance, Population.install, ↓reduceIte, final]
    · cases action
  | foreign | retire | nativeRetire => cases action

structure PrimitiveAdapterAt {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    (initial : World) (ticks : List (ActorTick runtime)) (tick : ActorTick runtime)
    (actor : ActorId) (engine : EngineState) (request : Request) (observed : Option Reply) where
  occurrence : PrimitiveFilesystem.FilesystemOccurrence Entrypoint.run engine.events request observed
  source : SelectedActorHistory runtime initial ticks tick actor engine
  before : World
  afterEngine : EngineState
  afterPresent : tick.after.actors actor = some afterEngine
  leading : ActorHistoryWith runtime actor (SourceReturnAt runtime ticks actor) 0
    (source.launch.tick.after.project (.initialFrom (PrimitiveFilesystem.lower Entrypoint.run)
      source.launch.references source.launch.closeExec
      source.launch.workingDirectory)) occurrence.rawBefore before
  completed : List (Request × Reply)
  completedTrace : occurrence.inside = completed.map (fun item => (item.1, some item.2))
  preceding : RawHistory kernel.step kernel.interference (SourceRawAt runtime ticks actor)
    occurrence.rawBefore.length before completed (tick.before.project engine)
  raw : RawPrefixHistory kernel.step kernel.interference (SourceRawAt runtime ticks actor)
    occurrence.rawBefore.length before (occurrence.inside ++ [(request, observed)]) (tick.after.project afterEngine)

-- §FS-host-boundary.lookup: All guard snapshots and the selected primary/lost call come from
-- the same actual actor journal and source residual, including the actual native handoff.
theorem actual_primitive_adapter_from_source {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (environment : InterferenceContract kernel)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply} (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (occurrence : PrimitiveFilesystem.FilesystemOccurrence Entrypoint.run engine.events request observed) :
    ∃ adapter : PrimitiveAdapterAt runtime initial ticks tick actor engine request observed,
      adapter.occurrence = occurrence := by
  obtain ⟨source⟩ := actual_selected_actor_history descriptors lifetimes references environment
    journal selected action present
  have arranged := source.history
  rw [occurrence.trace] at arranged
  obtain ⟨before, leading, active⟩ := actor_with_split occurrence.rawBefore
    (occurrence.inside.map Program.filesystemPrefixEvent) arranged
  obtain ⟨completed, completedTrace, recorded⟩ := actor_raw_filesystem active
  have recorded : RawHistory kernel.step kernel.interference (SourceRawAt runtime ticks actor)
      occurrence.rawBefore.length before completed (tick.before.project engine) := by
    simpa only [Nat.zero_add] using recorded
  obtain ⟨afterEngine, afterPresent, actual, sampled⟩ := selected_raw_kernel_step selected action present
  have count : occurrence.rawBefore.length + completed.length = engine.events.length := by
    have lengths := congrArg List.length occurrence.trace
    simp only [List.length_append, List.length_map] at lengths
    have completedLengths := congrArg List.length completedTrace
    simp only [List.length_map] at completedLengths
    omega
  have last : RawPrefixHistory kernel.step kernel.interference (SourceRawAt runtime ticks actor)
      (occurrence.rawBefore.length + completed.length) (tick.before.project engine)
      [(request, observed)] (tick.after.project afterEngine) := by
    rw [count]
    cases observed with
    | none => exact .lost actual sampled
    | some reply => exact .returned actual sampled (.stop _ _)
  have joined := raw_history_then_prefix recorded last
  refine ⟨⟨occurrence, source, before, afterEngine, afterPresent, leading,
    completed, completedTrace, recorded, ?_⟩, rfl⟩
  simpa only [Nat.zero_add, ← completedTrace] using joined

-- §AR-host-boundary.interfaces: Preserve the existing automatically selected raw adapter.
theorem actual_primitive_adapter {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (environment : InterferenceContract kernel)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply} (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) :
    Nonempty (PrimitiveAdapterAt runtime initial ticks tick actor engine request observed) := by
  obtain ⟨occurrence⟩ := selected_primitive_filesystem journal selected action present
  obtain ⟨adapter, same⟩ := actual_primitive_adapter_from_source descriptors lifetimes references environment
    journal selected action present occurrence
  exact ⟨adapter⟩

end LeanCage.Host.Kernel
