import FilesystemCleanupOccurrences

namespace LeanCage.Host.Kernel
open Filesystem
universe u

private theorem chunks_request_profile {logical raw : List Program.Event} {allowed : Request → Prop}
    (source : PrimitiveFilesystem.Chunks logical raw)
    (closed : ∀ primary candidate, allowed primary → AdapterRequest primary candidate → allowed candidate)
    (profile : ∀ event ∈ logical, RequestEvent allowed event) :
    ∀ event ∈ raw, RequestEvent allowed event := by
  induction source with
  | nil => intro event impossible; cases impossible
  | cons effect reply inside logical raw adapter remaining ih =>
    intro event member
    rcases List.mem_append.mp member with first | last
    · have head := profile (.returned effect reply) (by simp)
      cases effect with
      | filesystem request =>
        obtain ⟨events, returned, trace⟩ := Program.lift_filesystem_source (guardedCall request) adapter
        rw [trace] at first
        obtain ⟨⟨operation, answer⟩, occurs, rfl⟩ := List.mem_map.mp first
        exact closed request operation head (profile_returns (guarded_call_profile request) returned (operation, answer) occurs)
      | spawn | read | wait | terminate | tryWait | descriptor =>
        have single := PrimitiveFilesystem.effect_returns_singleton _ adapter
        rw [single] at first
        have same := List.mem_singleton.mp first
        subst event
        exact True.intro
    · exact ih (by intro event occurs; exact profile event (List.mem_cons_of_mem _ occurs)) event last

private theorem chunks_quiet {logical raw : List Program.Event}
    (source : PrimitiveFilesystem.Chunks logical raw) (quiet : ∀ event ∈ logical, NondestructiveEvent event) :
    ∀ event ∈ raw, NondestructiveEvent event := by
  apply chunks_request_profile source ?_ quiet
  intro primary candidate safe role
  rcases role with same | magic | flags | close
  · change candidate = primary at same
    rw [same]
    exact safe
  · simp [DestructiveRequest, magic]
  · simp [DestructiveRequest, flags]
  · simp [DestructiveRequest, close]

private theorem drop_append_allowed {α : Type u} {first last : List α} (count : Nat) (allowed : α → Prop)
    (leading : ∀ event ∈ first.drop count, allowed event) (trailing : ∀ event ∈ last, allowed event) :
    ∀ event ∈ (first ++ last).drop count, allowed event := by
  intro event member
  rw [List.drop_append] at member
  rcases List.mem_append.mp member with member | member
  · exact leading event member
  · exact trailing event (List.mem_of_mem_drop member)

theorem CleanupOccurrenceSegment.before_quiet {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {actor : ActorId} {events outside : List Program.Event}
    {created : List (Request × Reply)} {run : RunDirectory.Owned} {work : List Program.Event}
    {inside : List (Request × Option Reply)} {request : Request} {guardOrdinal limit : Nat} {current : World}
    {source : RunCleanupParent runtime initial all actor events outside created run work inside request guardOrdinal limit current}
    (segment : CleanupOccurrenceSegment source) :
    ∀ event ∈ segment.beforeRaw.drop (source.allocation.root.use.engine.events.length + 1), NondestructiveEvent event := by
  apply Eq.mpr (congrArg (fun actualEvents : List Program.Event =>
    ∀ event ∈ actualEvents.drop (source.allocation.root.use.engine.events.length + 1), NondestructiveEvent event)
    segment.beforeTrace)
  apply drop_append_allowed
  · intro event member
    exact passive_event_nondestructive (source.allocation.root.probes event member)
  · intro event member
    rcases List.mem_cons.mp member with rfl | member
    · simp only [NondestructiveEvent, DestructiveRequest, source.allocation.opening.opening]
      decide
    · rcases List.mem_append.mp member with member | workMember
      · rcases List.mem_append.mp member with postMember | createdMember
        · obtain ⟨⟨query, reply⟩, occurs, rfl⟩ := List.mem_map.mp postMember
          exact namespace_passive_not_destructive (source.allocation.earlier.passive (query, reply) occurs)
        · rw [source.point.createdExact] at createdMember
          obtain ⟨⟨query, reply⟩, occurs, rfl⟩ := List.mem_map.mp createdMember
          exact source.allocation.opening.nondestructive (query, reply) occurs
      · exact chunks_quiet segment.workChunks source.workQuiet event workMember

theorem CleanupOccurrenceSegment.inner_unlink {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {actor : ActorId} {events outside : List Program.Event}
    {created : List (Request × Reply)} {run : RunDirectory.Owned} {work : List Program.Event}
    {inside : List (Request × Option Reply)} {request : Request} {guardOrdinal limit : Nat} {current : World}
    {source : RunCleanupParent runtime initial all actor events outside created run work inside request guardOrdinal limit current}
    (segment : CleanupOccurrenceSegment source) (unlink : request.op = .unlinkAt) :
    ∀ pair ∈ segment.cleanupEvents, pair.1.op = .unlinkAt → pair.1.first = run.directory.fd := by
  obtain ⟨frontier⟩ := cleanup_frontier source.cleanupSource
  have chunks : PrimitiveFilesystem.Chunks (frontier.replies.map Program.filesystemEvent)
      (segment.cleanupEvents.map Program.filesystemEvent) :=
    Eq.mp (congrArg (fun logical => PrimitiveFilesystem.Chunks logical (segment.cleanupEvents.map Program.filesystemEvent))
      ((congrArg (List.map Program.filesystemPrefixEvent) frontier.trace).trans (completed_filesystem_events _))) segment.chunks
  have profile : ∀ event ∈ segment.cleanupEvents.map Program.filesystemEvent,
      RequestEvent (fun query => query.op = .unlinkAt → query.first = run.directory.fd) event := by
    apply chunks_request_profile chunks ?_ ?_
    · intro primary candidate allowed role removing
      rcases role with same | magic | flags | close
      · change candidate = primary at same
        exact (congrArg Request.first same).trans (allowed ((congrArg Request.op same).symm.trans removing))
      · rw [magic] at removing; cases removing
      · rw [flags] at removing; cases removing
      · rw [close] at removing; cases removing
    · intro event member
      obtain ⟨pair, occurs, rfl⟩ := List.mem_map.mp member
      exact frontier.earlier_unlinks_inside unlink pair occurs
  intro pair member
  exact profile (Program.filesystemEvent pair) (List.mem_map.mpr ⟨pair, member, rfl⟩)

private theorem child_component {name : ByteArray}
    (member : name ∈ ["request.cpio".toUTF8, "control.sock".toUTF8, "policy.json".toUTF8]) :
    Directories.component name = true := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same
  · rw [same]
    change Directories.component (ByteArray.mk #[114, 101, 113, 117, 101, 115, 116, 46, 99, 112, 105, 111]) = true
    simp [Directories.component, ByteArray.isEmpty, ByteArray.size, Array.contains_eq_mem]
  · rw [same]
    change Directories.component (ByteArray.mk #[99, 111, 110, 116, 114, 111, 108, 46, 115, 111, 99, 107]) = true
    simp [Directories.component, ByteArray.isEmpty, ByteArray.size, Array.contains_eq_mem]
  · rw [same]
    change Directories.component (ByteArray.mk #[112, 111, 108, 105, 99, 121, 46, 106, 115, 111, 110]) = true
    simp [Directories.component, ByteArray.isEmpty, ByteArray.size, Array.contains_eq_mem]

theorem CleanupOccurrenceSegment.unlink_component {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {actor : ActorId} {events outside : List Program.Event}
    {created : List (Request × Reply)} {run : RunDirectory.Owned} {work : List Program.Event}
    {inside : List (Request × Option Reply)} {request : Request} {guardOrdinal limit : Nat} {current : World}
    {source : RunCleanupParent runtime initial all actor events outside created run work inside request guardOrdinal limit current}
    (segment : CleanupOccurrenceSegment source) :
    ∀ pair ∈ segment.cleanupEvents, pair.1.op = .unlinkAt → Directories.component pair.1.left = true := by
  have logical : ∀ event ∈ inside.map Program.filesystemPrefixEvent,
      RequestEvent (fun query => query.op = .unlinkAt → Directories.component query.left = true) event := by
    intro event member
    obtain ⟨pair, occurs, rfl⟩ := List.mem_map.mp member
    have role := RunDirectory.cleanup_request_prefix run source.cleanupSource pair (List.mem_append_left _ occurs)
    have component (removing : pair.1.op = .unlinkAt) : Directories.component pair.1.left = true := by
      unfold RunDirectory.CleanupRequest at role
      rw [removing] at role
      rcases role with child | root
      · exact child_component child.2.2
      · have name : run.name = source.allocation.root.use.request.left :=
          (congrArg Request.left source.allocation.opening.operation).symm.trans source.allocation.root.sameName
        rw [root.2.2, name]
        exact source.allocation.root.use.component
    rcases pair with ⟨query, reply⟩
    cases reply <;> exact component
  have profile := chunks_request_profile segment.chunks (allowed := fun query =>
    query.op = .unlinkAt → Directories.component query.left = true) (by
      intro primary candidate allowed role removing
      rcases role with same | magic | flags | close
      · change candidate = primary at same
        rw [same] at removing ⊢
        exact allowed removing
      · rw [magic] at removing; cases removing
      · rw [flags] at removing; cases removing
      · rw [close] at removing; cases removing) logical
  intro pair member
  exact profile (Program.filesystemEvent pair) (List.mem_map.mpr ⟨pair, member, rfl⟩)

-- §FS-host-boundary.ownership: Captured resources are matched to the SAME
-- actor ordinal/global source operation. An earlier inner unlink cannot be
-- rebound to another equal-shaped call or a reused directory descriptor.
theorem CleanupOccurrenceSegment.captured_unlink {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel)
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {actor : ActorId} {events outside : List Program.Event}
    {created : List (Request × Reply)} {run : RunDirectory.Owned} {work : List Program.Event}
    {inside : List (Request × Option Reply)} {request : Request} {guardOrdinal limit : Nat} {current : World}
    {source : RunCleanupParent runtime initial all actor events outside created run work inside request guardOrdinal limit current}
    (segment : CleanupOccurrenceSegment source) (unlink : request.op = .unlinkAt)
    {ordinal : Nat} {query : Request} {reply : Reply} {before after : World}
    (sample : SourceReturnAt runtime all actor ordinal Reply (.filesystem query) reply before after)
    (atEvent : events[ordinal]? = some (.returned (.filesystem query) reply))
    (sinceBirth : source.allocation.root.use.engine.events.length + 1 ≤ ordinal)
    (removing : query.op = .unlinkAt) :
    query.first = run.directory.fd ∧ Directories.component query.left = true ∧
      before.handles run.directory.fd = some source.allocation.earlier.source.opening.handle := by
  have full : events = segment.beforeRaw ++
      (segment.cleanupEvents.map Program.filesystemEvent ++ source.allocation.earlier.guards) := by
    simpa only [List.append_assoc] using segment.trace
  have afterBefore : segment.beforeRaw.length ≤ ordinal := by
    by_cases earlier : ordinal < segment.beforeRaw.length
    · have selected : segment.beforeRaw[ordinal]? = some (.returned (.filesystem query) reply) := by
        simpa only [full, List.getElem?_append_left earlier] using atEvent
      have selectedDrop : (segment.beforeRaw.drop (source.allocation.root.use.engine.events.length + 1))[ordinal - (source.allocation.root.use.engine.events.length + 1)]? =
          some (.returned (.filesystem query) reply) := by
        rw [List.getElem?_drop]
        simpa only [Nat.add_sub_of_le sinceBirth] using selected
      have quiet := segment.before_quiet _ (List.mem_of_getElem? selectedDrop)
      exact False.elim (quiet (.inl removing))
    · omega
  let offset := ordinal - segment.beforeRaw.length
  have following : (segment.cleanupEvents.map Program.filesystemEvent ++ source.allocation.earlier.guards)[offset]? =
      some (.returned (.filesystem query) reply) := by
    simpa only [full, List.getElem?_append_right afterBefore, offset] using atEvent
  have inCleanup : offset < segment.cleanupEvents.length := by
    by_cases bounded : offset < segment.cleanupEvents.length
    · exact bounded
    · have afterCleanup : (segment.cleanupEvents.map Program.filesystemEvent).length ≤ offset := by
        simp only [List.length_map]
        omega
      have guardEvent : source.allocation.earlier.guards[offset - segment.cleanupEvents.length]? =
          some (.returned (.filesystem query) reply) := by
        simpa only [List.getElem?_append_right afterCleanup, List.length_map] using following
      have quiet := source.guardsQuiet _ (List.mem_of_getElem? guardEvent)
      exact False.elim (quiet (.inl removing))
  have selectedRaw : (segment.cleanupEvents.map Program.filesystemEvent)[offset]? =
      some (.returned (.filesystem query) reply) := by
    have bound : offset < (segment.cleanupEvents.map Program.filesystemEvent).length := by
      simpa only [List.length_map] using inCleanup
    exact (List.getElem?_append_left bound).symm.trans following
  rw [List.getElem?_map] at selectedRaw
  cases selectedPair : segment.cleanupEvents[offset]? with
  | none => simp only [selectedPair, Option.map_none] at selectedRaw; cases selectedRaw
  | some pair =>
    simp only [selectedPair, Option.map_some, Option.some.injEq] at selectedRaw
    have decoded := congrArg PrimitiveFilesystem.filesystemEvent? selectedRaw
    have fields : (pair.1, some pair.2) = (query, some reply) := by
      change some (pair.1, some pair.2) = some (query, some reply) at decoded
      exact Option.some.inj decoded
    have queryField : pair.1 = query := congrArg (fun pair : Request × Option Reply => pair.1) fields
    have replyField : pair.2 = reply := Option.some.inj (congrArg (fun pair : Request × Option Reply => pair.2) fields)
    have samePair : pair = (query, reply) := Prod.ext queryField replyField
    subst pair
    have descriptor := segment.inner_unlink unlink (query, reply) (List.mem_of_getElem? selectedPair) removing
    obtain ⟨capturedBefore, capturedAfter, actual, captured, resource⟩ := borrowed_recorded_use_at
      (Lowered.cleanup_directory_uses descriptors run source.allocation.earlier.source.opening.handle source.point.distinct)
      segment.active segment.history segment.directory selectedPair
    have count : segment.beforeRaw.length + offset = ordinal := Nat.add_sub_of_le afterBefore
    have captured : SourceReturnAt runtime all actor ordinal Reply (.filesystem query) reply capturedBefore capturedAfter := by
      exact Eq.mp (congrArg (fun who => SourceReturnAt runtime all who ordinal Reply (.filesystem query) reply
        capturedBefore capturedAfter) source.sameActor) (count ▸ captured)
    have worlds := same_ordinal_source_returns journal captured sample
    exact ⟨descriptor, segment.unlink_component (query, reply) (List.mem_of_getElem? selectedPair) removing,
      Eq.mp (congrArg (fun world => world.handles run.directory.fd =
      some source.allocation.earlier.source.opening.handle) worlds.2.1) (resource ⟨removing, descriptor⟩)⟩

end LeanCage.Host.Kernel
