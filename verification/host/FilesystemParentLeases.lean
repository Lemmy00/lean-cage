import FilesystemNativeMetadata
import FilesystemPrimitiveObservations
import FilesystemReferenceLifetime

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

theorem returned_action_events {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {β : Type} {actor : ActorId} {effect : Effect β} {reply : β} {before after : Population}
    (actual : ActorStep runtime (.returned actor effect reply) before after)
    {initial final : EngineState} (first : before.actors actor = some initial)
    (last : after.actors actor = some final) :
    final.events = initial.events ++ [.returned effect reply] := by
  cases actual with
  | @returned β population actor engine effect next reply world present alive head operation =>
    have sameInitial := Option.some.inj (first.symm.trans present)
    subst engine
    have sameFinal : initial.returned effect reply next world = final := by
      apply Option.some.inj
      simpa only [Population.advance, Population.install, ite_eq_left] using last
    subst final
    rfl

-- §FS-host-boundary.ownership: Each global snapshot retains the SAME actual source sample and
-- old OFD, allowing descriptor reuse only when it cannot resurrect that reference.
theorem active_parent_lease_snapshots {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (raw : RawReferenceLifetimeContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (references : ReferenceContract runtime) {all ticks : List (ActorTick runtime)}
    {hostUid object : Nat} {before after : Population}
    (journal : ActorJournal runtime before ticks after)
    (lease : ActiveParentLease runtime all before hostUid object)
    {final : EngineState} (last : after.actors lease.actor = some final)
    (live : final.references lease.descriptor = some lease.handle)
    (old : before.shared.descriptionAllocated lease.handle.description = true) :
    ∀ tick ∈ ticks, Nonempty (ActiveParentLease runtime all tick.before hostUid object) ∧
      Nonempty (ActiveParentLease runtime all tick.after hostUid object) := by
  induction journal with
  | nil => intro tick impossible; cases impossible
  | @cons tick ticks after tail ih =>
    obtain ⟨middle, extra, middlePresent, trace⟩ :=
      actor_step_event_prefix tick.operation lease.actor lease.engine lease.present
    have middleOld := actor_step_description_allocated references tick.operation lease.handle.description old
    have middleLive := (actor_journal_reference_continuity raw sdk references tail middlePresent last middleOld live).1
    have earlier : lease.ordinal < middle.events.length := by
      have original := lease.earlier
      rw [trace, List.length_append]
      omega
    let nextLease : ActiveParentLease runtime all tick.after hostUid object := {
      lease with engine := middle, present := middlePresent, live := middleLive, earlier }
    have remaining := ih nextLease last live middleOld
    intro selected member
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨⟨lease⟩, ⟨nextLease⟩⟩
    · exact remaining selected later

-- §FS-host-boundary.ownership: The actual fstat return starts protection; its successful source
-- guard and real post-stat handle supply the lease, not an independently chosen parent role.
theorem primitive_stat_parent_lease {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) {initial : World} {ticks : List (ActorTick runtime)}
    {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState} {fd : UInt64} {reply : Reply}
    (sample : PrimitiveObservationAt runtime initial ticks tick actor engine (.filesystem {op := .stat, first := fd}) reply)
    {handle : Handle} {hostUid : Nat} {information : Stat}
    (live : sample.before.handles fd = some handle) (parsed : parseStat reply = some information)
    (trusted : Directories.trusted hostUid information = true) :
    ∃ (position : Nat) (actual : ActorTick runtime), ticks[position]? = some actual ∧
      Nonempty (ActiveParentLease runtime ticks actual.after hostUid handle.object) := by
  obtain ⟨position, actual, first, last, selected, action, firstPresent, lastPresent,
    count, beforeShape, afterShape⟩ := sample.sampled
  have operation : ActorStep runtime (.returned actor (.filesystem {op := .stat, first := fd}) reply)
      actual.before actual.after := action ▸ actual.operation
  have events := returned_action_events operation firstPresent lastPresent
  have retained : last.references fd = some handle := by
    have afterLive : sample.after.handles fd = some handle := by
      rw [descriptors.retained _ _ _ _ sample.actual (by simp [RetainsDescriptors])]
      exact live
    simpa only [afterShape, Population.project] using afterLive
  refine ⟨position, actual, selected, ⟨{
    actor, engine := last, descriptor := fd, handle, present := lastPresent, live := retained
    identity := rfl, ordinal := sample.rawBefore.length, before := sample.before, after := sample.after
    reply, information, sampled := sample.sampled, held := live, parsed, trusted, earlier := ?_ }⟩⟩
  rw [events, List.length_append, List.length_singleton, count]
  omega

end LeanCage.Host.Kernel
