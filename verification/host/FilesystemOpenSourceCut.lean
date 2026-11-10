import FilesystemRootOpenReceipt
import FilesystemGuardedOpens

namespace LeanCage.Host.PrimitiveFilesystem

-- §AR-host-boundary.primitives: Split the actual expanded execution at one original
-- source call, preserving both its exact adapter chunk and the remaining source run.
theorem reached_selected_filesystem {α : Type} {program after : Program α} {raw : List Program.Event}
    (context following : List Program.Event) (request : Filesystem.Request) (reply : Filesystem.Reply)
    (source : Reached program (context ++ .returned (.filesystem request) reply :: following) raw after) :
    ∃ first inside last next,
      Reached program context first (.call (.filesystem request) next) ∧
      Program.Returns (lowerEffect (.filesystem request)) inside reply ∧
      Reached (next reply) following last after ∧ raw = first ++ inside ++ last := by
  induction context generalizing program raw with
  | nil =>
    cases source with
    | call effect next actual inside logical raw after adapter rest =>
      exact ⟨[], inside, raw, next, .refl _, adapter, rest, by simp only [List.nil_append]⟩
  | cons event context ih =>
    cases source with
    | call effect next actual inside logical raw after adapter rest =>
      obtain ⟨first, middle, last, final, leading, active, remaining, trace⟩ := ih rest
      exact ⟨inside ++ first, middle, last, final,
        .call effect next actual inside _ _ _ adapter leading, active, remaining,
        by simp only [trace, List.append_assoc]⟩

end LeanCage.Host.PrimitiveFilesystem

namespace LeanCage.Host.Kernel.Lowered
open Filesystem

private theorem prefix_bind_return {α β : Type} {program : Filesystem.Program α}
    {next : α → Filesystem.Program β} {events : List (Request × Reply)} {value : α}
    {later : List (Request × Option Reply)} (source : Returns program events value)
    (remaining : Prefix (next value) later) :
    Prefix (program.bind next) (Publication.completed events ++ later) := by
  induction source with
  | pure => exact remaining
  | call request next reply events value rest ih => exact .returned _ _ _ _ (ih remaining)

structure GuardedOpenCut (kernel : Contract) (origin : FilesystemOrigin) (ordinal : Nat)
    (request : Request) (fd : UInt64) (events : List (Request × Reply)) where
  opening : RecordedOpen kernel origin request fd
  checks : List (Request × Reply)
  following : List (Request × Reply)
  trace : events = checks ++ (request, opening.reply) :: following
  count : opening.ordinal = ordinal + checks.length
  active : Prefix (guardedCall request) (Publication.completed checks ++ [(request, some opening.reply)])
  retaining : ∀ event ∈ following, RetainsDescriptors event.1.op
  passive : ∀ event ∈ following, NamespacePassive event.1

-- §FS-host-boundary.ownership: This is the selected actual open inside its real guard,
-- not another equal-looking global row. Prefix probes and post-open checks are kept.
theorem guarded_open_recorded_cut {kernel : Contract} (laws : DescriptorContract kernel)
    {origin : FilesystemOrigin} {ordinal : Nat} {request : Request} {before after : World}
    {events : List (Request × Reply)} {reply : Reply} {fd : UInt64}
    (run : RecordedRun kernel origin ordinal (guardedCall request) before events after reply)
    (opening : request.op = .openAt) (recognized : descriptor reply = some fd) :
    ∃ cut : GuardedOpenCut kernel origin ordinal request fd events,
      after.handles fd = some cut.opening.handle ∧ cut.opening.reply = reply ∧
      RecordedHistory kernel origin (cut.opening.ordinal + 1) cut.opening.after cut.following after := by
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
    refine ⟨{
      opening := ⟨ordinal + checks.length, actual, openedWorld, openedReply, handle, operation, sampled,
        original, live, raw⟩
      checks
      following := openedEvents
      trace := trace.trans (congrArg (checks ++ ·) shape)
      count := rfl
      active := ?_
      retaining := ?_
      passive := ?_ }, (by rw [frames]; exact live), same.symm, tail⟩
    · unfold guardedCall
      apply prefix_bind_return checked.1
      exact .returned request _ openedReply [] (.empty _)
    · intro event member
      rcases probes event member with magic | flags
      · rw [magic]; simp [RetainsDescriptors]
      · rw [flags]; simp [RetainsDescriptors]
    · intro event member
      rcases probes event member with magic | flags
      · simp only [NamespacePassive, magic]
      · simp only [NamespacePassive, flags]

end LeanCage.Host.Kernel.Lowered
