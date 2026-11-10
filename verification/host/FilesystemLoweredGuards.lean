import FilesystemGuardedOpens

namespace LeanCage.Host.Kernel.Lowered
open Filesystem

-- §FS-host-boundary.snapshot: The accepted privacy observation is an actual raw getAttribute
-- on the retained descriptor returned by the preceding guarded open.
theorem public_handle_guard_recorded {kernel : Contract} (laws : DescriptorContract kernel)
    (origin : FilesystemOrigin) (ordinal : Nat) (fd : UInt64) (handle : Handle)
    {before after : World} {events : List (Request × Reply)} {result : UInt64}
    (run : RecordedRun kernel origin ordinal (SourcePaths.publicHandle fd).lower before events after (.ok result))
    (live : before.handles fd = some handle) :
    result = fd ∧ Nonempty (GuardedHandle kernel origin (ordinal + events.length) after fd) := by
  have source := run.1
  change Returns (Filesystem.Program.call
    { op := .getAttribute, first := fd, second := 1, left := PrivateNames.attributeName }
    (fun reply => (if nativeError reply && errorNumber reply == 61 then
      Filesystem.Program.pure (.ok fd)
    else closeResult fd (.error "caller path enters private application state")).lower)) events (.ok result) at source
  obtain ⟨reply, last, shape, continued⟩ := Snapshot.returns_call_split source
  split at continued
  · rename_i accepted
    obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq continued
    have sameFd : result = fd := Except.ok.inj same
    have history := run.2
    rw [shape] at history
    obtain ⟨actual, checked, leading, operation, sampled, final⟩ := recorded_history_head history
    have actualLive : actual.handles fd = some handle := by
      rw [empty_recorded_handles leading]
      exact live
    have fields : nativeError reply = true ∧ errorNumber reply = 61 := by
      simpa only [Bool.and_eq_true, beq_iff_eq] using accepted
    have absent := kernel.attribute_absent _ _ _ _ handle operation rfl rfl actualLive fields.1 fields.2
    have retained : after.handles fd = some handle := by
      rw [empty_recorded_handles final, laws.retained _ _ _ _ operation (by simp [RetainsDescriptors])]
      exact actualLive
    refine ⟨sameFd, ⟨⟨handle, retained,
      ⟨ordinal, actual, checked, reply, operation, sampled, actualLive, fields, absent⟩, ?_⟩⟩⟩
    rw [shape]
    simp only [List.length_singleton]
    omega
  · obtain ⟨logical, rejected⟩ := returns_source _ continued
    have impossible := (Snapshot.closeResult_provenance _ _ rejected).1
    cases impossible

theorem source_open_guard_recorded {kernel : Contract} (laws : DescriptorContract kernel)
    (origin : FilesystemOrigin) (ordinal : Nat) (parent : UInt64) (name : ByteArray) (directory : Bool)
    {before after : World} {events : List (Request × Reply)} {fd : UInt64}
    (run : RecordedRun kernel origin ordinal (SourcePaths.openAt parent name directory).lower
      before events after (.ok fd)) :
    Nonempty (GuardedHandle kernel origin (ordinal + events.length) after fd) := by
  let request : Request := {
    op := .openAt, first := parent, second := if directory then directoryFlags else readFlags, left := name }
  let next (reply : Reply) : Filesystem.Program (Result UInt64) :=
    match descriptor reply with
    | none => .pure (.error (failure "caller path openat" reply))
    | some opened => SourcePaths.publicHandle opened
  have stage : RecordedRun kernel origin ordinal
      ((guardedCall request).bind (fun reply => (next reply).lower)) before events after (.ok fd) := run
  obtain ⟨opening, openedReply, following, openedWorld, trace, opened, remaining⟩ :=
    Kernel.recorded_run_bind_split _ _ stage
  unfold next at remaining
  split at remaining
  · cases remaining.1
  · rename_i openedFd recognized
    obtain ⟨handle, live, raw⟩ := guarded_open_live laws opened rfl recognized
    obtain ⟨same, guarded⟩ := public_handle_guard_recorded laws origin (ordinal + opening.length)
      openedFd handle remaining live
    subst openedFd
    obtain ⟨guarded⟩ := guarded
    refine ⟨⟨guarded.handle, guarded.live, guarded.guard, ?_⟩⟩
    simpa only [trace, List.length_append, Nat.add_assoc] using guarded.earlier

end LeanCage.Host.Kernel.Lowered
