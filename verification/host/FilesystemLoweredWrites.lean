import FilesystemLoweredPublicationBorrowing

namespace LeanCage.Host.Kernel.Lowered
open Filesystem

private theorem concurrent_split {kernel : Contract} {α β : Type}
    (program : Filesystem.Program α) (next : α → Filesystem.Program β)
    {before after : World} {events : List (Request × Reply)} {result : β}
    (run : ConcurrentRun kernel (program.bind next) before events after result) :
    ∃ first value last middle, events = first ++ last ∧
      ConcurrentRun kernel program before first middle value ∧ ConcurrentRun kernel (next value) middle last after result := by
  obtain ⟨first, value, last, source, remaining, trace⟩ := Snapshot.returns_bind_split _ _ run.1
  have history := run.2
  rw [trace] at history
  obtain ⟨middle, leading, trailing⟩ := history_split first last history
  exact ⟨first, value, last, middle, trace, ⟨source, leading⟩, remaining, trailing⟩

theorem writeLoop_identity (fuel : Nat) (fd : UInt64) (bytes : ByteArray) (offset : Nat) :
    (writeLoop fuel fd bytes offset).lower = writeLoop fuel fd bytes offset := by
  apply lowering_identity
  induction fuel generalizing offset with
  | zero => exact .pure _
  | succ fuel ih =>
    unfold writeLoop
    split
    · exact .pure _
    · apply RequestProfile.call (allowed := fun request => guardedCall request = Filesystem.Program.effect request) _ _ rfl
      intro reply
      repeat' first | exact .pure _ | exact ih _ | split

theorem writeAndClose_identity (fuel : Nat) (fd : UInt64) (bytes : ByteArray) (offset : Nat) :
    ((writeLoop fuel fd bytes offset).bind (closeResult fd)).lower =
      (writeLoop fuel fd bytes offset).bind (closeResult fd) := by
  rw [Filesystem.Program.lower_bind, writeLoop_identity]
  apply congrArg (Filesystem.Program.bind (writeLoop fuel fd bytes offset))
  funext result
  exact close_result_identity fd result

private theorem adapter_no_write (request : Request) (opening : request.op = .openAt)
    {candidate : Request} (profile : AdapterRequest request candidate) : candidate.op ≠ .write := by
  rcases profile with same | magic | flags | closing
  · subst candidate; rw [opening]; decide
  · rw [magic]; decide
  · rw [flags]; decide
  · rw [closing]; decide

-- §FS-host-boundary.ownership: The acknowledged O_EXCL open inside this actual raw guard
-- establishes freshness relative to the whole invocation, rather than a fabricated logical step.
theorem guarded_exclusive_fresh (kernel : Contract) (parent : UInt64) (name : ByteArray) (mode : UInt64)
    {before after : World} {events : List (Request × Reply)} {reply : Reply} {fd : UInt64}
    (run : ConcurrentRun kernel (guardedCall {
      op := .openAt, first := parent, second := newFileFlags, third := mode, left := name }) before events after reply)
    (recognized : descriptor reply = some fd) :
    ∃ handle, after.handles fd = some handle ∧ before.allocated handle.object = false := by
  have source := run
  unfold guardedCall at source
  obtain ⟨checks, accepted, remaining, checkedWorld, trace, checked, following⟩ := concurrent_split _ _ source
  cases accepted with
  | false =>
    have same := (Snapshot.returns_pure_eq following.1).2
    rw [same] at recognized
    have rejected : descriptor Lookup.unsupported = none := by decide
    rw [rejected] at recognized
    cases recognized
  | true =>
    change ConcurrentRun kernel (Filesystem.Program.effect {
      op := .openAt, first := parent, second := newFileFlags, third := mode, left := name })
      checkedWorld remaining after reply at following
    obtain ⟨actualReply, rest, shape, finish⟩ := Snapshot.returns_call_split following.1
    obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq finish
    cases same
    have history := following.2
    rw [shape] at history
    obtain ⟨actual, opened, leading, operation, trailing⟩ := history_head history
    obtain ⟨object, description, fresh, allocated, descriptionFresh, descriptionAllocated, described, live⟩ :=
      kernel.exclusive_file _ _ _ _ _ operation rfl rfl recognized
    have original : before.allocated object = false := by
      cases earlier : before.allocated object with
      | false => rfl
      | true =>
        have current := history_allocated leading object (history_allocated checked.2 object earlier)
        rw [fresh] at current
        cases current
    refine ⟨⟨object, description, newFileFlags, true⟩, ?_, original⟩
    rw [random_history_handles trailing (by intro event impossible; cases impossible)]
    exact live

-- §FS-host-boundary.ownership: Every raw write, including the last lost call, targets the
-- actual file born by this writer. Probe/rejection/open effects and arbitrary interference stay.
theorem writeNew_prefix_only_fresh (kernel : Contract) (parent : UInt64) (name bytes : ByteArray)
    (mode : UInt64) {before after : World} {events : List (Request × Option Reply)}
    (run : PhysicalPrefix kernel (writeNew parent name bytes mode).lower before events after) :
    PrefixTargets kernel (fun object => before.allocated object = false) before events after := by
  unfold writeNew at run
  split at run
  · apply physical_nonwrite run
    have empty := Snapshot.prefix_pure_empty (physical_prefix_source run)
    rw [empty]
    simp
  · let request : Request := {op := .openAt, first := parent, second := newFileFlags, third := mode, left := name}
    let next (reply : Reply) : Filesystem.Program (Result Unit) :=
      match descriptor reply with
      | none => .pure (.error (failure "exclusive openat" reply))
      | some fd => (writeLoop (bytes.size + 1) fd bytes 0).bind (closeResult fd)
    have stage : PhysicalPrefix kernel ((guardedCall request).bind (fun reply => (next reply).lower))
        before events after := run
    rcases physical_bind_split _ _ stage with checking |
        ⟨middle, opening, reply, remaining, opened, tail, trace⟩
    · apply physical_nonwrite checking
      intro event member
      exact adapter_no_write request rfl
        (profile_prefix (guarded_call_profile request) (physical_prefix_source checking) event member)
    · have initialTargets : WritesWithin kernel (fun object => before.allocated object = false) before opening middle :=
        nonwrite_history opened.2 (by
          intro event member
          exact adapter_no_write request rfl (profile_returns (guarded_call_profile request) opened.1 event member))
      unfold next at tail
      cases recognized : descriptor reply with
      | none =>
        rw [recognized] at tail
        have noWrites : PrefixTargets kernel (fun object => before.allocated object = false) middle remaining after := by
          apply physical_nonwrite tail
          have empty := Snapshot.prefix_pure_empty (physical_prefix_source tail)
          rw [empty]
          simp
        rw [trace]
        exact writes_then_prefix initialTargets noWrites
      | some fd =>
        rw [recognized] at tail
        obtain ⟨handle, live, fresh⟩ := guarded_exclusive_fresh kernel parent name mode opened recognized
        have writing : PhysicalPrefix kernel ((writeLoop (bytes.size + 1) fd bytes 0).bind (closeResult fd))
            middle remaining after := writeAndClose_identity _ _ _ _ ▸ tail
        have targets := writeAndClose_prefix_targets kernel (bytes.size + 1) fd bytes 0 writing live
        rw [trace]
        exact writes_then_prefix initialTargets (prefix_targets_mono targets (by
          intro object same
          simpa only [same] using fresh))

end LeanCage.Host.Kernel.Lowered
