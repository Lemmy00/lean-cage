import FilesystemLoweredHistory
import FilesystemReadSources.Handles

namespace LeanCage.Host.Kernel.Lowered
open Filesystem

structure RecordedOpen (kernel : Contract) (origin : FilesystemOrigin) (request : Request) (fd : UInt64) where
  ordinal : Nat
  before : World
  after : World
  reply : Reply
  handle : Handle
  actual : kernel.step before request (some reply) after
  sampled : origin ordinal request reply before after
  recognized : descriptor reply = some fd
  live : after.handles fd = some handle
  raw : handle.rawOwned = true

-- §FS-host-boundary.lookup: A successful open result follows only accepted post-open probes.
theorem opened_success_source {request : Request} {initial reply : Reply}
    {events : List (Request × Reply)} {fd : UInt64}
    (source : Returns (Lookup.opened request initial) events reply)
    (recognized : descriptor reply = some fd) :
    reply = initial ∧ ∀ event ∈ events, ProbeRequest event.1 := by
  unfold Lookup.opened at source
  split at source
  · split at source
    · obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq source
      exact ⟨same, by simp⟩
    · obtain ⟨checks, accepted, last, checked, following, trace⟩ := adapter_returns_bind_split _ _ source
      cases accepted with
      | true =>
        obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq following
        refine ⟨same, ?_⟩
        rw [trace, List.append_nil]
        exact profile_returns (lookup_check_profile _ _ (.inl rfl) (.inr rfl)) checked
      | false =>
        obtain ⟨_, _, _, returned⟩ := Snapshot.returns_call_split following
        obtain ⟨_, same⟩ := Snapshot.returns_pure_eq returned
        rw [same] at recognized
        have denied : descriptor Lookup.unsupported = none := by decide
        rw [denied] at recognized
        cases recognized
  · obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq source
    exact ⟨same, by simp⟩

theorem recorded_retaining_handles {kernel : Contract} (laws : DescriptorContract kernel)
    {origin : FilesystemOrigin} {ordinal : Nat} {before after : World}
    {events : List (Request × Reply)}
    (history : RecordedHistory kernel origin ordinal before events after)
    (profile : ∀ event ∈ events, RetainsDescriptors event.1.op) : after.handles = before.handles := by
  induction history with
  | nil => rfl
  | @cons ordinal before middle after request reply events actual sampled tail ih =>
    exact (ih (by intro event member; exact profile event (by simp [member]))).trans
      (laws.retained _ _ _ _ actual (profile (request, reply) (by simp)))
  | environment actual tail ih => exact (ih profile).trans (kernel.interference_handles _ _ actual)

-- §FS-host-boundary.ownership: The returned lease is established by the actual open inside the
-- guard. Failed probes and rejection closes cannot produce this successful descriptor result.
theorem guarded_open_recorded {kernel : Contract} (laws : DescriptorContract kernel)
    {origin : FilesystemOrigin} {ordinal : Nat} {request : Request} {before after : World}
    {events : List (Request × Reply)} {reply : Reply} {fd : UInt64}
    (run : RecordedRun kernel origin ordinal (guardedCall request) before events after reply)
    (opening : request.op = .openAt) (recognized : descriptor reply = some fd) :
    ∃ opened : RecordedOpen kernel origin request fd, after.handles fd = some opened.handle := by
  have unfolded := run
  unfold guardedCall at unfolded
  obtain ⟨checks, accepted, following, checkedWorld, trace, checked, remaining⟩ :=
    Kernel.recorded_run_bind_split _ _ unfolded
  cases accepted with
  | false =>
    have same := (Snapshot.returns_pure_eq remaining.1).2
    rw [same] at recognized
    have denied : descriptor Lookup.unsupported = none := by decide
    rw [denied] at recognized
    cases recognized
  | true =>
    obtain ⟨openedReply, openedEvents, shape, post⟩ := Snapshot.returns_call_split remaining.1
    have history := remaining.2
    rw [shape] at history
    obtain ⟨actual, openedWorld, leading, operation, sampled, tail⟩ := recorded_history_head history
    obtain ⟨same, probes⟩ := opened_success_source post recognized
    have original : descriptor openedReply = some fd := by simpa only [same] using recognized
    obtain ⟨fresh, handle, live⟩ := laws.allocated_fresh _ _ _ _ _ operation (.inl opening) original
    have raw := laws.allocated_raw _ _ _ _ _ _ operation (.inl opening) original live
    have frames := recorded_retaining_handles laws tail (by
      intro event member
      rcases probes event member with magic | flags
      · rw [magic]; simp [RetainsDescriptors]
      · rw [flags]; simp [RetainsDescriptors])
    exact ⟨⟨ordinal + checks.length, actual, openedWorld, openedReply, handle, operation, sampled,
      original, live, raw⟩, by rw [frames]; exact live⟩

theorem guarded_open_live {kernel : Contract} (laws : DescriptorContract kernel)
    {origin : FilesystemOrigin} {ordinal : Nat} {request : Request} {before after : World}
    {events : List (Request × Reply)} {reply : Reply} {fd : UInt64}
    (run : RecordedRun kernel origin ordinal (guardedCall request) before events after reply)
    (opening : request.op = .openAt) (recognized : descriptor reply = some fd) :
    ∃ handle, after.handles fd = some handle ∧ handle.rawOwned = true := by
  obtain ⟨opened, live⟩ := guarded_open_recorded laws run opening recognized
  exact ⟨opened.handle, live, opened.raw⟩

-- §FS-host-boundary.ownership: A separate retained parent is sampled at the SAME actual
-- open, after the guard's real pre-open probes and any interleaved permitted operations.
theorem guarded_open_recorded_retained {kernel : Contract} (laws : DescriptorContract kernel)
    {origin : FilesystemOrigin} {ordinal : Nat} {request : Request} {before after : World}
    {events : List (Request × Reply)} {reply : Reply} {fd held : UInt64} {parent : Handle}
    (run : RecordedRun kernel origin ordinal (guardedCall request) before events after reply)
    (opening : request.op = .openAt) (recognized : descriptor reply = some fd)
    (live : before.handles held = some parent) :
    ∃ opened : RecordedOpen kernel origin request fd,
      after.handles fd = some opened.handle ∧ opened.before.handles held = some parent := by
  have unfolded := run
  unfold guardedCall at unfolded
  obtain ⟨checks, accepted, following, checkedWorld, trace, checked, remaining⟩ :=
    Kernel.recorded_run_bind_split _ _ unfolded
  have checkedLive := (borrow_returns (lookup_all_borrow laws held parent _) ⟨checked.1, recorded_history_erase checked.2⟩ live).1
  cases accepted with
  | false =>
    have same := (Snapshot.returns_pure_eq remaining.1).2
    rw [same] at recognized
    have denied : descriptor Lookup.unsupported = none := by decide
    rw [denied] at recognized
    cases recognized
  | true =>
    obtain ⟨openedReply, openedEvents, shape, post⟩ := Snapshot.returns_call_split remaining.1
    have history := remaining.2
    rw [shape] at history
    obtain ⟨actual, openedWorld, leading, operation, sampled, tail⟩ := recorded_history_head history
    obtain ⟨same, probes⟩ := opened_success_source post recognized
    have original : descriptor openedReply = some fd := by simpa only [same] using recognized
    obtain ⟨fresh, handle, openedLive⟩ := laws.allocated_fresh _ _ _ _ _ operation (.inl opening) original
    have raw := laws.allocated_raw _ _ _ _ _ _ operation (.inl opening) original openedLive
    have frames := recorded_retaining_handles laws tail (by
      intro event member
      rcases probes event member with magic | flags
      · rw [magic]; simp [RetainsDescriptors]
      · rw [flags]; simp [RetainsDescriptors])
    refine ⟨⟨ordinal + checks.length, actual, openedWorld, openedReply, handle, operation, sampled,
      original, openedLive, raw⟩, by rw [frames]; exact openedLive, ?_⟩
    rw [empty_recorded_handles leading]
    exact checkedLive

-- §FS-host-boundary.ownership: Opening the inherited CWD samples that actual CWD, even with
-- intervening raw guard probes. The application never selects it by its later spelling.
theorem guarded_open_recorded_directory {kernel : Contract} (laws : DescriptorContract kernel)
    {origin : FilesystemOrigin} {ordinal : Nat} {request : Request} {before after : World}
    {events : List (Request × Reply)} {reply : Reply} {fd : UInt64}
    (run : RecordedRun kernel origin ordinal (guardedCall request) before events after reply)
    (opening : request.op = .openAt) (recognized : descriptor reply = some fd) :
    ∃ opened : RecordedOpen kernel origin request fd,
      after.handles fd = some opened.handle ∧ opened.before.workingDirectory = before.workingDirectory := by
  have unfolded := run
  unfold guardedCall at unfolded
  obtain ⟨checks, accepted, following, checkedWorld, trace, checked, remaining⟩ :=
    Kernel.recorded_run_bind_split _ _ unfolded
  cases accepted with
  | false =>
    have same := (Snapshot.returns_pure_eq remaining.1).2
    rw [same] at recognized
    have denied : descriptor Lookup.unsupported = none := by decide
    rw [denied] at recognized
    cases recognized
  | true =>
    obtain ⟨openedReply, openedEvents, shape, post⟩ := Snapshot.returns_call_split remaining.1
    have history := remaining.2
    rw [shape] at history
    obtain ⟨actual, openedWorld, leading, operation, sampled, tail⟩ := recorded_history_head history
    obtain ⟨same, probes⟩ := opened_success_source post recognized
    have original : descriptor openedReply = some fd := by simpa only [same] using recognized
    obtain ⟨fresh, handle, live⟩ := laws.allocated_fresh _ _ _ _ _ operation (.inl opening) original
    have raw := laws.allocated_raw _ _ _ _ _ _ operation (.inl opening) original live
    have frames := recorded_retaining_handles laws tail (by
      intro event member
      rcases probes event member with magic | flags
      · rw [magic]; simp [RetainsDescriptors]
      · rw [flags]; simp [RetainsDescriptors])
    exact ⟨⟨ordinal + checks.length, actual, openedWorld, openedReply, handle, operation, sampled,
      original, live, raw⟩, by rw [frames]; exact live,
      (history_directory (recorded_history_erase leading)).trans
        (history_directory (recorded_history_erase checked.2))⟩

end LeanCage.Host.Kernel.Lowered
