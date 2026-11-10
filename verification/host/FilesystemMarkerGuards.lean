import FilesystemMarkerLifetime
import FilesystemReadSources

namespace LeanCage.Host.Kernel
open Filesystem

structure SafeExternalCut {kernel : Contract} {runtime : ActorRuntime kernel}
    (contract : ProcessContract runtime) (primitive : ChildPrimitive kernel) (hostUid : Nat)
    (initial final : Processes) (ticks : List (ActorTick runtime)) (position : Nat) (tick : ActorTick runtime)
    extends ExternalCut contract primitive hostUid initial final ticks position tick where
  firstSafe : ExternalAuthorityJournal first
  currentSafe : ExternalAuthoritySafe current
  lastSafe : ExternalAuthorityJournal last

theorem selected_safe_external_cut {kernel : Contract} {runtime : ActorRuntime kernel}
    {contract : ProcessContract runtime} {primitive : ChildPrimitive kernel} {hostUid : Nat}
    {before after : Processes} {ticks : List (ActorTick runtime)}
    (recording : ExternalJournal contract primitive hostUid before ticks after)
    (safe : ExternalAuthorityJournal recording)
    {position : Nat} {tick : ActorTick runtime} (selected : ticks[position]? = some tick) :
    Nonempty (SafeExternalCut contract primitive hostUid before after ticks position tick) := by
  induction recording generalizing position with
  | nil => cases selected
  | @cons before middle after first ticks actual tail ih =>
    cases position with
    | zero =>
      have same := Option.some.inj selected
      subst first
      exact ⟨⟨⟨[], ticks, rfl, rfl, before, middle, .nil _, actual, tail⟩, True.intro, safe.1, safe.2⟩⟩
    | succ position =>
      obtain ⟨cut⟩ := ih safe.2 selected
      exact ⟨{
        leading := first :: cut.leading
        trailing := cut.trailing
        count := by simpa only [List.length_cons] using congrArg Nat.succ cut.count
        shape := by simp only [cut.shape, List.cons_append]
        before := cut.before
        after := cut.after
        first := .cons actual cut.first
        current := cut.current
        last := cut.last
        firstSafe := ⟨safe.1, cut.firstSafe⟩
        currentSafe := cut.currentSafe
        lastSafe := cut.lastSafe }⟩

-- §FS-host-boundary.snapshot: The key marker is derived at the actual guard, never assumed there.
theorem actual_guard_excludes_initial_marker {kernel : Contract} {runtime : ActorRuntime kernel}
    {contract : ProcessContract runtime} {primitive : ChildPrimitive kernel} {hostUid : Nat}
    (lifetimes : LifetimeContract runtime) (objects : ObjectLifetimeContract runtime)
    (metadata : LiveMetadataContract runtime primitive) (attributes : ExistingAttributeContract runtime primitive)
    (foreign : ForeignContract runtime) {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    (backend : BackendAuthorityProducer contract primitive ticks) {after : Processes}
    (recording : ExternalJournal contract primitive hostUid Processes.empty ticks after)
    {object : ObjectId} {value : ByteArray} (old : initial.allocated object = true)
    (markedState : ProtectedMarker initial hostUid object value)
    {actor : ActorId} {fd : UInt64} {handle : Handle}
    (guard : PublicGuard kernel (fun ordinal request reply =>
      SourceReturnAt runtime ticks actor ordinal Reply (.filesystem request) reply) fd handle) :
    handle.object ≠ object := by
  intro sameObject
  obtain ⟨position, tick, engine, nextEngine, selected, action, present, afterPresent,
    count, beforeShape, afterShape⟩ := guard.sampled
  have safe := actual_external_authority_journal journal backend recording
  obtain ⟨cut⟩ := selected_safe_external_cut recording safe selected
  have prior : ActorJournal runtime (Population.empty initial) cut.leading tick.before := by
    have arranged := journal
    rw [cut.shape] at arranged
    obtain ⟨middle, first, last⟩ := actor_journal_split cut.leading _ arranged
    cases last with
    | cons rest => exact first
  have alive : ObjectAlive tick.before.shared object := by
    have actual := objects.reference _ _ _ _ _ _ guard.actual guard.live
    rw [sameObject, beforeShape] at actual
    exact actual
  have state := external_journal_protected_marker lifetimes objects metadata attributes foreign
    prior cut.first cut.firstSafe old alive markedState
  obtain ⟨information, known, owner, mode, marker⟩ := state
  have actualMarker : guard.before.attributes object PrivateNames.attributeName = some value := by
    rw [beforeShape]
    exact marker
  have absent := guard.absent
  rw [sameObject, actualMarker] at absent
  cases absent

-- §FS-host-boundary.snapshot: An actual source-guarded copy cannot include that protected object.
theorem actual_guarded_read_excludes_initial_marker {kernel : Contract} {runtime : ActorRuntime kernel}
    {contract : ProcessContract runtime} {primitive : ChildPrimitive kernel} {hostUid : Nat}
    (lifetimes : LifetimeContract runtime) (objects : ObjectLifetimeContract runtime)
    (metadata : LiveMetadataContract runtime primitive) (attributes : ExistingAttributeContract runtime primitive)
    (foreign : ForeignContract runtime) {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    (backend : BackendAuthorityProducer contract primitive ticks) {after : Processes}
    (recording : ExternalJournal contract primitive hostUid Processes.empty ticks after)
    {object : ObjectId} {value : ByteArray} (old : initial.allocated object = true)
    (markedState : ProtectedMarker initial hostUid object value)
    {actor : ActorId} {position : Nat} {engine : EngineState} {request : Request}
    (read : SelectedGuardedRead runtime ticks actor position engine request) : read.handle.object ≠ object :=
  actual_guard_excludes_initial_marker lifetimes objects metadata attributes foreign journal backend recording
    old markedState read.guard

-- §FS-host-boundary.snapshot: The actual snapshot reads a live object distinct from the key.
theorem actual_snapshot_protected_reference {kernel : Contract} {runtime : ActorRuntime kernel}
    {contract : ProcessContract runtime} {primitive : ChildPrimitive kernel} {hostUid : Nat}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (environment : InterferenceContract kernel)
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime primitive)
    (attributes : ExistingAttributeContract runtime primitive) (foreign : ForeignContract runtime)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    (backend : BackendAuthorityProducer contract primitive ticks) {after : Processes}
    (recording : ExternalJournal contract primitive hostUid Processes.empty ticks after)
    {object : ObjectId} {value : ByteArray} (old : initial.allocated object = true)
    (markedState : ProtectedMarker initial hostUid object value)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply}
    (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (workspace : Option ByteArray) (stdin : Snapshot.Stdin) (limits : Snapshot.Limits)
    {context : List Program.Event} {before : List (Request × Option Reply)}
    (source : Prefix (Snapshot.freeze workspace stdin limits) (before ++ [(request, observed)]))
    (trace : engine.events = context ++ before.map Program.filesystemPrefixEvent) (reading : request.op = .read) :
    ∃ handle, engine.references request.first = some handle ∧ handle.object ≠ object := by
  obtain ⟨guarded⟩ := actual_snapshot_guarded_read descriptors lifetimes references environment journal
    selected action present workspace stdin limits source trace reading
  exact ⟨guarded.handle, guarded.live, actual_guarded_read_excludes_initial_marker lifetimes objects metadata
    attributes foreign journal backend recording old markedState guarded⟩

end LeanCage.Host.Kernel
