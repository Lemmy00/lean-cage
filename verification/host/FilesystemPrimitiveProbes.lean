import FilesystemPrimitiveRecording
import FilesystemAccessProofs.Last

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.lookup: This source receipt covers the actual guard interval up to the
-- selected namespace syscall, without assuming that foreign-owned flags stay fixed.
theorem primitive_adapter_parent_probes {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {ticks : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial ticks tick actor engine request observed)
    {semantics : NameSemanticsView}
    (laws : LookupPrimitiveContract kernel.step kernel.interference semantics)
    (kind : NamespaceRequest request) :
    ∀ fd ∈ Lookup.parents request, ∀ handle, (tick.before.project engine).handles fd = some handle →
      Nonempty (CheckedDirectory kernel.step (SourceRawAt runtime ticks actor) semantics fd handle) := by
  obtain ⟨checks, checked, same, trace⟩ := guarded_namespace_last adapter.occurrence.adapter kind
  have completed : adapter.completed = checks :=
    completed_injective (adapter.completedTrace.symm.trans trace)
  have history : RawHistory kernel.step kernel.interference (SourceRawAt runtime ticks actor)
      adapter.occurrence.rawBefore.length adapter.before checks (tick.before.project engine) := by
    simpa only [completed] using adapter.preceding
  have parents : Lookup.parents request = Lookup.parents adapter.occurrence.primary := congrArg Lookup.parents same
  intro fd member handle live
  have frame := raw_probe_history_handles laws history (checked_parents_probes checked)
  have initialLive : adapter.before.handles fd = some handle := by rw [← frame]; exact live
  exact (checked_parents_recorded laws checked history fd (parents ▸ member) handle initialLive).1

-- §FS-host-boundary.caller: Parent checks are derived from the same native handoff, entry source
-- and physical journal, with no standalone accepted-guard premise.
theorem actual_selected_parent_probes {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (environment : InterferenceContract kernel)
    {semantics : NameSemanticsView}
    (laws : LookupPrimitiveContract kernel.step kernel.interference semantics)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply} (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) (kind : NamespaceRequest request) :
    ∀ fd ∈ Lookup.parents request, ∀ handle, engine.references fd = some handle →
      Nonempty (CheckedDirectory kernel.step (SourceRawAt runtime ticks actor) semantics fd handle) := by
  obtain ⟨adapter⟩ := actual_primitive_adapter descriptors lifetimes references environment
    journal selected action present
  exact primitive_adapter_parent_probes adapter laws kind

end LeanCage.Host.Kernel
