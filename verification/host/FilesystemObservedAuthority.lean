import FilesystemDirectoryObservations
import FilesystemIntervals

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: A source fstat and UID observation establish current authority.
-- Every intervening global tick retains the same actual OFD; no path-stability premise is used.
theorem observed_directory_current_authority {kernel : Contract} {runtime : ActorRuntime kernel}
    {process : ProcessContract runtime} {primitive : ChildPrimitive kernel} {hostUid : Nat}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (raw : RawReferenceLifetimeContract kernel)
    (sdk : RuntimeDescriptorContract runtime) (accounts : AccountContract kernel hostUid)
    (metadata : GlobalAuthorityContract runtime primitive)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    (backend : BackendAuthorityProducer process primitive ticks) {afterProcesses : Processes}
    (recording : ExternalJournal process primitive hostUid Processes.empty ticks afterProcesses)
    {actor : ActorId} {position : Nat} {tick : ActorTick runtime} {engine : EngineState}
    (selected : ticks[position]? = some tick) (present : tick.before.actors actor = some engine)
    {limit uid : Nat} {world : World} {directory : Directories.Opened}
    (source : ObservedDirectory kernel
      (fun ordinal request reply => SourceReturnAt runtime ticks actor ordinal Reply (.filesystem request) reply)
      limit world uid directory)
    (identity : UidSample kernel
      (fun ordinal request reply => SourceReturnAt runtime ticks actor ordinal Reply (.filesystem request) reply) uid)
    (now : engine.references directory.fd = some source.handle) (bound : limit ≤ engine.events.length) :
    ∃ information, tick.before.shared.information source.handle.object = some information ∧
      SameAuthority directory.information information ∧ Directories.trusted hostUid information = true := by
  have uidSame := sampled_uid_is_host accounts identity
  have trusted : Directories.trusted hostUid directory.information = true := by
    rw [← uidSame]
    exact source.trusted
  have owners : directory.information.uid = hostUid ∨ directory.information.uid = 0 := by
    have fields : directory.information.directory = true ∧
        (directory.information.uid = hostUid ∨ directory.information.uid = 0) ∧
        (directory.information.mode &&& 18 = 0 ∨
          (directory.information.uid = 0 ∧ directory.information.mode &&& 512 ≠ 0)) := by
      simpa [Directories.trusted, and_assoc] using trusted
    exact fields.2.1
  obtain ⟨sourcePosition, sourceTick, beforeEngine, afterEngine, sourceAt, action, beforePresent,
    afterPresent, count, beforeShape, afterShape⟩ := source.sample.sampled
  have firstLive : beforeEngine.references directory.fd = some source.handle := by
    simpa only [beforeShape, Population.project] using source.sample.live
  have sourceBefore : beforeEngine.events.length < engine.events.length := by
    rw [count]
    exact Nat.lt_of_lt_of_le source.earlier bound
  have ordered := source_ordinal_orders_positions journal sourceAt selected actor beforeEngine engine
    beforePresent present sourceBefore
  obtain ⟨leading, inside, trailing, shape, interval⟩ :=
    journal_between_selected journal sourceAt selected (Nat.le_of_lt ordered)
  obtain ⟨sourceBound, sourceValue⟩ := List.getElem?_eq_some_iff.mp sourceAt
  have member : sourceTick ∈ ticks := List.mem_iff_getElem.mpr ⟨sourcePosition, sourceBound, sourceValue⟩
  have consistent := (actor_journal_consistent descriptors lifetimes references journal
    (empty_population_consistent initial)).2 sourceTick member
  have old : sourceTick.before.shared.descriptionAllocated source.handle.description = true :=
    (consistent.1 actor beforeEngine beforePresent directory.fd source.handle firstLive).2.1
  have held := (actor_journal_reference_continuity raw sdk references interval beforePresent present old now).2
  have safe := actual_external_authority_journal journal backend recording
  have arranged : ∃ recorded : ExternalJournal process primitive hostUid Processes.empty ticks afterProcesses,
      ExternalAuthorityJournal recorded := ⟨recording, safe⟩
  rw [shape, List.append_assoc] at arranged
  obtain ⟨arranged, arrangedSafe⟩ := arranged
  obtain ⟨atStart, first, rest, firstSafe, restSafe⟩ := safe_external_split leading _ arranged arrangedSafe
  obtain ⟨atEnd, recordedInterval, last, intervalSafe, lastSafe⟩ := safe_external_split inside trailing rest restSafe
  have initialKnown : sourceTick.before.shared.information source.handle.object = some directory.information := by
    have known := descriptors.stat_actual _ _ _ _ _ _ source.sample.actual rfl source.sample.live source.sample.parsed
    simpa only [beforeShape, Population.project] using known
  obtain ⟨information, known, same⟩ := external_journal_authority metadata interval recordedInterval intervalSafe
    initialKnown owners (by
      intro current occurs
      obtain ⟨next, nextPresent, nextLive⟩ := (held current occurs).2
      exact .inl ⟨actor, next, directory.fd, source.handle, nextPresent, nextLive, rfl⟩)
  exact ⟨information, known, same, (same_authority_trusted hostUid same).trans trusted⟩

end LeanCage.Host.Kernel
