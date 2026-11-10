import FilesystemPrimitivePhases

namespace LeanCage.Host.PrimitiveFilesystem

-- §AR-host-boundary.primitives: A finite pending prefix determines the actual source call,
-- including all earlier returned values. It does not predict this call's result.
theorem pending_residual {α β : Type} {program : Program α} {before : List Program.Event}
    (effect : Effect β) (source : Program.Prefix program (before ++ [.lost effect])) :
    ∃ next, Kernel.Residual program before (.call effect next) := by
  generalize trace : before ++ [.lost effect] = events at source
  induction source generalizing before with
  | empty =>
    have length := congrArg List.length trace
    simp only [List.length_append, List.length_singleton, List.length_nil] at length
    omega
  | lost actual next =>
    cases before with
    | nil => cases trace; exact ⟨next, .refl _⟩
    | cons head tail =>
      have length := congrArg List.length trace
      simp only [List.length_cons, List.length_append] at length
      omega
  | returned actual next reply tail rest ih =>
    cases before with
    | nil => cases trace
    | cons head earlier =>
      have same := List.cons.inj trace
      obtain ⟨final, reached⟩ := ih same.2
      exact ⟨final, same.1 ▸ Kernel.Residual.call reached⟩

theorem reached_of_chunks {α : Type} {program after : Program α}
    {logical raw : List Program.Event} (source : Kernel.Residual program logical after)
    (chunks : Chunks logical raw) : Reached program logical raw after := by
  induction source generalizing raw with
  | refl => cases chunks; exact .refl _
  | @call β effect next reply events after tail ih =>
    cases chunks with
    | cons effect reply inside logical raw adapter remaining =>
      exact .call effect next reply inside _ _ _ adapter (ih remaining)

private theorem prefix_bind_left {α β : Type} {program : Program α} (next : α → Program β)
    {events : List Program.Event} (source : Program.Prefix program events) :
    Program.Prefix (program.bind next) events := by
  induction source with
  | empty => exact .empty _
  | lost effect next => exact .lost _ _
  | returned effect next reply tail continued ih => exact .returned effect _ reply tail ih

theorem reached_prefix {α : Type} {program after : Program α} {logical raw tail : List Program.Event}
    (source : Reached program logical raw after) (active : Program.Prefix (lower after) tail) :
    Program.Prefix (lower program) (raw ++ tail) := by
  induction source with
  | refl => exact active
  | call effect next reply inside logical raw after adapter source ih =>
    have joined : Program.Prefix (lower (.call effect next)) (inside ++ (raw ++ tail)) :=
      VirtualMachine.prefix_of_return_bind adapter (ih active)
    simpa only [List.append_assoc] using joined

-- §FS-host-boundary.acceptance: The exact actual raw chunk suffix reproduces an interrupted
-- helper, including its probes and the same final primitive occurrence.
theorem pending_chunks_prefix {α β : Type} {program : Program α} {logical raw inside : List Program.Event}
    (effect : Effect β) (source : Program.Prefix program (logical ++ [.lost effect]))
    (chunks : Chunks logical raw) (active : Program.Prefix (lowerEffect effect) inside) :
    Program.Prefix (lower program) (raw ++ inside) := by
  obtain ⟨next, pending⟩ := pending_residual effect source
  apply reached_prefix (reached_of_chunks pending chunks)
  exact prefix_bind_left (fun reply => lower (next reply)) active

end LeanCage.Host.PrimitiveFilesystem

namespace LeanCage.Host.Kernel
open Filesystem

private theorem physical_prefix_of_raw {kernel : Contract} {origin : RawOrigin} {ordinal : Nat}
    {α : Type} {program : Filesystem.Program α} {before after : World} {events : List (Request × Option Reply)}
    (source : Prefix program events)
    (history : RawPrefixHistory kernel.step kernel.interference origin ordinal before events after) :
    PhysicalPrefix kernel program before events after := by
  induction history generalizing program with
  | stop => exact .stop _ _
  | environment actual tail ih => exact .environment actual (ih source)
  | lost actual sampled => cases source with | lost => exact .lost actual
  | returned actual sampled tail ih =>
    cases source with
    | returned request next reply rest continued => exact .returned actual (ih continued)

-- §FS-host-boundary.ownership: This actual interrupted helper carries its raw initial world,
-- exact original prefix and per-operation global origins, rather than a completed-helper frame.
structure PrimitivePrefixPhase {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    {α : Type} (program : Filesystem.Program α) where
  rawBefore : List Program.Event
  before : World
  earlier : List (Request × Reply)
  trace : engine.events = rawBefore ++ earlier.map Program.filesystemEvent
  leading : ActorHistoryWith runtime actor (SourceReturnAt runtime all actor) 0
    (adapter.source.launch.tick.after.project (.initialFrom (PrimitiveFilesystem.lower Entrypoint.run)
      adapter.source.launch.references adapter.source.launch.closeExec adapter.source.launch.workingDirectory))
    rawBefore before
  sampled : RawPrefixHistory kernel.step kernel.interference (SourceRawAt runtime all actor) rawBefore.length
    before (Publication.completed earlier ++ [(request, observed)]) (tick.after.project adapter.afterEngine)
  actual : PhysicalPrefix kernel program.lower before (Publication.completed earlier ++ [(request, observed)])
    (tick.after.project adapter.afterEngine)

-- §AR-host-boundary.primitives: A real source slice reconstructs the SAME raw helper prefix,
-- keeping its exact initial world, probe chunks, selected call and hostile lost effects.
theorem primitive_filesystem_prefix_phase {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) (primary : request = adapter.occurrence.primary)
    {α : Type} (program : Filesystem.Program α) {context inside : List Program.Event}
    (source : Program.Prefix (Program.liftFilesystem program)
      (inside ++ [Program.filesystemPrefixEvent (request, none)]))
    (trace : adapter.occurrence.logicalBefore = context ++ inside) :
    Nonempty (PrimitivePrefixPhase adapter program) := by
  have chunks := PrimitiveFilesystem.reached_chunks adapter.occurrence.reached
  rw [trace] at chunks
  obtain ⟨rawBefore, rawInside, leadingChunks, insideChunks, rawTrace⟩ :=
    PrimitiveFilesystem.chunks_split context inside chunks
  have rawAdapter : Program.Prefix (PrimitiveFilesystem.lowerEffect (.filesystem request))
      (adapter.occurrence.inside.map Program.filesystemPrefixEvent ++
        [Program.filesystemPrefixEvent (request, observed)]) := by
    have active := Program.lift_filesystem_prefix adapter.occurrence.adapter
    rw [← primary] at active
    simpa only [PrimitiveFilesystem.lowerEffect, List.map_append, List.map_singleton] using active
  have lowered := PrimitiveFilesystem.pending_chunks_prefix (.filesystem request) source insideChunks rawAdapter
  rw [PrimitiveFilesystem.lower_lift_filesystem] at lowered
  have lowered : Program.Prefix (Program.liftFilesystem program.lower)
      ((rawInside ++ adapter.occurrence.inside.map Program.filesystemPrefixEvent) ++
        [Program.filesystemPrefixEvent (request, observed)]) := by
    simpa only [List.append_assoc] using lowered
  obtain ⟨earlier, active, earlierTrace⟩ := selected_filesystem_source lowered
  have engineTrace : engine.events = rawBefore ++ earlier.map Program.filesystemPrefixEvent := by
    rw [adapter.occurrence.trace, rawTrace, List.append_assoc, earlierTrace]
  have history := adapter.source.history
  rw [engineTrace] at history
  obtain ⟨before, leading, tail⟩ := actor_with_split rawBefore _ history
  obtain ⟨completed, completedTrace, recorded⟩ := actor_raw_filesystem tail
  have recorded : RawHistory kernel.step kernel.interference (SourceRawAt runtime all actor)
      rawBefore.length before completed (tick.before.project engine) := by
    simpa only [Nat.zero_add] using recorded
  have exactTrace : engine.events = rawBefore ++ completed.map Program.filesystemEvent := by
    exact engineTrace.trans (congrArg (rawBefore ++ ·) (by rw [completedTrace, List.map_map]; rfl))
  have ordinal : rawBefore.length + completed.length = engine.events.length := by
    have lengths := congrArg List.length exactTrace
    simp only [List.length_append, List.length_map] at lengths
    omega
  have selected : all[adapter.source.preceding.length]? = some tick := by
    have selected : (adapter.source.preceding ++ tick :: adapter.source.following)[adapter.source.preceding.length]? =
        some tick := by
      simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
    exact (congrArg (fun items : List (ActorTick runtime) => items[adapter.source.preceding.length]?)
      adapter.source.shape).trans selected
  obtain ⟨afterEngine, afterPresent, actual, sampled⟩ := selected_raw_kernel_step selected action present
  have sameEngine := Option.some.inj (afterPresent.symm.trans adapter.afterPresent)
  subst afterEngine
  have last : RawPrefixHistory kernel.step kernel.interference (SourceRawAt runtime all actor)
      (rawBefore.length + completed.length) (tick.before.project engine) [(request, observed)]
      (tick.after.project adapter.afterEngine) := by
    rw [ordinal]
    cases observed with
    | none => exact .lost actual sampled
    | some reply => exact .returned actual sampled (.stop _ _)
  have joined := raw_history_then_prefix recorded last
  have original : Prefix program.lower (Publication.completed completed ++ [(request, observed)]) := by
    simpa only [completedTrace, Publication.completed] using active
  refine ⟨⟨rawBefore, before, completed, exactTrace, leading, ?_, ?_⟩⟩
  · exact joined
  · exact physical_prefix_of_raw original joined

end LeanCage.Host.Kernel
