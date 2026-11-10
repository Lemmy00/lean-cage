import FilesystemPrimitiveProbes

namespace LeanCage.Host.Kernel
open Filesystem

theorem checked_parents_recorded_bounded {step : RawStep} {interference : RawInterference}
    {origin : RawOrigin} {semantics : NameSemanticsView}
    (laws : LookupPrimitiveContract step interference semantics)
    {ordinal : Nat} {before after : World} {fds : List UInt64} {events : List (Request × Reply)}
    (checked : CheckedParents fds events) (history : RawHistory step interference origin ordinal before events after) :
    ∀ fd ∈ fds, ∀ handle, before.handles fd = some handle →
      Nonempty (BoundedCheckedDirectory step origin semantics fd handle ordinal (ordinal + events.length)) ∧
        after.handles fd = some handle := by
  induction checked generalizing ordinal before with
  | nil => simp
  | cons fd rest first last accepted following ih =>
    obtain ⟨middle, initial, ending⟩ := raw_history_split first last history
    have all := CheckedParents.cons fd rest first last accepted following
    have frame := raw_probe_history_handles laws history (checked_parents_probes all)
    intro query member handle live
    refine ⟨?_, by rw [frame]; exact live⟩
    rcases List.mem_cons.mp member with rfl | later
    · obtain ⟨⟨bounded⟩, kept⟩ := lookup_check_raw_sound_bounded laws (lookup_check_complete accepted) initial live
      refine ⟨⟨bounded.checked, bounded.lower, ?_⟩⟩
      have bound := bounded.upper
      simp only [List.length_append]
      omega
    · have firstFrame := raw_probe_history_handles laws initial
        (fun event member => checked_parents_probes (CheckedParents.cons fd [] first [] accepted .nil)
          event (by simpa only [List.append_nil] using member))
      obtain ⟨⟨bounded⟩, kept⟩ := ih ending query later handle (by rw [firstFrame]; exact live)
      refine ⟨⟨bounded.checked, ?_, ?_⟩⟩
      · have bound := bounded.lower
        omega
      · have bound := bounded.upper
        simpa only [List.length_append, Nat.add_assoc] using bound

-- §FS-host-boundary.lookup: Each accepted parent probe's genuine raw ordinal is inside this
-- actual guard chunk and strictly precedes its selected namespace operation.
theorem primitive_adapter_parent_probes_bounded {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {ticks : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial ticks tick actor engine request observed)
    {semantics : NameSemanticsView} (laws : LookupPrimitiveContract kernel.step kernel.interference semantics)
    (kind : NamespaceRequest request) :
    ∀ fd ∈ Lookup.parents request, ∀ handle, engine.references fd = some handle →
      Nonempty (BoundedCheckedDirectory kernel.step (SourceRawAt runtime ticks actor) semantics fd handle
        adapter.occurrence.rawBefore.length engine.events.length) := by
  obtain ⟨checks, checked, same, trace⟩ := guarded_namespace_last adapter.occurrence.adapter kind
  have completed : adapter.completed = checks := completed_injective (adapter.completedTrace.symm.trans trace)
  have history : RawHistory kernel.step kernel.interference (SourceRawAt runtime ticks actor)
      adapter.occurrence.rawBefore.length adapter.before checks (tick.before.project engine) := by
    simpa only [completed] using adapter.preceding
  have parents : Lookup.parents request = Lookup.parents adapter.occurrence.primary := congrArg Lookup.parents same
  have count : adapter.occurrence.rawBefore.length + checks.length = engine.events.length := by
    have whole := congrArg List.length adapter.occurrence.trace
    have inside := congrArg List.length trace
    simp only [List.length_append, List.length_map] at whole inside
    omega
  intro fd member handle live
  have frame := raw_probe_history_handles laws history (checked_parents_probes checked)
  have initialLive : adapter.before.handles fd = some handle := by rw [← frame]; exact live
  obtain ⟨⟨bounded⟩, kept⟩ := checked_parents_recorded_bounded laws checked history fd (parents ▸ member) handle initialLive
  exact ⟨⟨bounded.checked, bounded.lower, by simpa only [count] using bounded.upper⟩⟩

theorem checked_directory_global_sample {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {ticks : List (ActorTick runtime)} {actor : ActorId}
    {semantics : NameSemanticsView} {fd : UInt64} {handle : Handle}
    (checked : CheckedDirectory kernel.step (SourceRawAt runtime ticks actor) semantics fd handle) :
    ∃ (position : Nat) (tick : ActorTick runtime) (engine : EngineState),
      ticks[position]? = some tick ∧ tick.before.actors actor = some engine ∧
      engine.events.length = checked.ordinal ∧ checked.observedAt = tick.before.project engine := by
  cases checked with
  | temporary magic code =>
    obtain ⟨position, tick, initial, final, selected, action, first, last, count, before, after⟩ := magic.sampled
    exact ⟨position, tick, initial, selected, first, count, before⟩
  | ext magic value flags code decoded allowed =>
    obtain ⟨position, tick, initial, final, selected, action, first, last, count, before, after⟩ := flags.sampled
    exact ⟨position, tick, initial, selected, first, count, before⟩

end LeanCage.Host.Kernel
