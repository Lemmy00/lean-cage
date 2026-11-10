import GatewayChannelOFDReferences
import GatewayChannelDescriptionLifetimes

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

-- §AR-host-boundary.primitives: One actual row records all physical OFD
-- references, including pending kernel loans. An old output reference must
-- copy a prior one; a genuinely fresh OFD remains an allowed alternative.
structure SocketReferenceRuntime {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (process : ProcessContract runtime) (child : ChildPrimitive kernel) (native : NativePrimitive kernel)
    (hostUid : Nat) where
  observed : ∀ {before after : Processes} {callers next : NativeProcesses} {tick : ActorTick runtime},
    NativeExternalStep process child native hostUid before callers tick after next →
      SocketReferenceSnapshot → SocketReferenceSnapshot → Prop
  input : ∀ {before after : Processes} {callers next : NativeProcesses} {tick : ActorTick runtime}
    {row : NativeExternalStep process child native hostUid before callers tick after next} {first last},
    observed row first last → first.population = tick.before ∧ first.native = callers ∧ first.children = before
  output : ∀ {before after : Processes} {callers next : NativeProcesses} {tick : ActorTick runtime}
    {row : NativeExternalStep process child native hostUid before callers tick after next} {first last},
    observed row first last → last.population = tick.after ∧ last.native = next ∧ last.children = after
  input_lifetime : ∀ {before after : Processes} {callers next : NativeProcesses} {tick : ActorTick runtime}
    {row : NativeExternalStep process child native hostUid before callers tick after next} {first last},
    observed row first last → ∀ place handle, first.at place = some handle →
      tick.before.shared.descriptionAllocated handle.description = true
  output_lifetime : ∀ {before after : Processes} {callers next : NativeProcesses} {tick : ActorTick runtime}
    {row : NativeExternalStep process child native hostUid before callers tick after next} {first last},
    observed row first last → ∀ place handle, last.at place = some handle →
      tick.after.shared.descriptionAllocated handle.description = true
  copied : ∀ {before after : Processes} {callers next : NativeProcesses} {tick : ActorTick runtime}
    {row : NativeExternalStep process child native hostUid before callers tick after next} {first last},
    observed row first last → ∀ place handle, last.at place = some handle →
    tick.before.shared.descriptionAllocated handle.description = true →
    ∃ original source, first.at original = some source ∧
      source.object = handle.object ∧ source.description = handle.description

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
  (references : SocketReferenceRuntime process child native hostUid)

-- The annotation is indexed by the supplied stored journal value. There is
-- no second valid witness for an equal tick and no omitted callback row.
inductive SocketReferenceRecording :
    {before after : Processes} → {callers next : NativeProcesses} → {ticks : List (ActorTick runtime)} →
    NativeExternalJournal process child native hostUid before callers ticks after next →
      SocketReferenceSnapshot → SocketReferenceSnapshot → Type 1 where
  | nil (before : Processes) (callers : NativeProcesses) (snapshot : SocketReferenceSnapshot) :
      SocketReferenceRecording (.nil before callers) snapshot snapshot
  | cons {before middle after : Processes} {callers next final : NativeProcesses}
      {tick : ActorTick runtime} {ticks : List (ActorTick runtime)}
      {row : NativeExternalStep process child native hostUid before callers tick middle next}
      {tail : NativeExternalJournal process child native hostUid middle next ticks after final}
      {first between last : SocketReferenceSnapshot}
      (actual : references.observed row first between)
      (rest : SocketReferenceRecording tail between last) :
      SocketReferenceRecording (.cons row tail) first last

noncomputable def SocketReferenceRecording.at
    {before after : Processes} {callers next : NativeProcesses} {ticks : List (ActorTick runtime)}
    {journal : NativeExternalJournal process child native hostUid before callers ticks after next}
    {first last : SocketReferenceSnapshot} (recording : SocketReferenceRecording references journal first last) :
    Nat → Option (SocketReferenceSnapshot × SocketReferenceSnapshot) := by
  induction recording with
  | nil => exact fun _ => none
  | @cons before middle after callers next final tick ticks row tail first between last actual rest ih =>
    exact fun
      | 0 => some (first, between)
      | position + 1 => ih position

theorem SocketReferenceRecording.empty_identity
    {before after : Processes} {callers next : NativeProcesses} {ticks : List (ActorTick runtime)}
    {journal : NativeExternalJournal process child native hostUid before callers ticks after next}
    {first last : SocketReferenceSnapshot} (recording : SocketReferenceRecording references journal first last)
    (empty : ticks = []) : first = last := by
  cases recording with
  | nil => rfl
  | cons => cases empty

theorem SocketReferenceRecording.at_has_tick
    {before after : Processes} {callers next : NativeProcesses} {ticks : List (ActorTick runtime)}
    {journal : NativeExternalJournal process child native hostUid before callers ticks after next}
    {first last : SocketReferenceSnapshot} (recording : SocketReferenceRecording references journal first last)
    {position : Nat} {current following : SocketReferenceSnapshot}
    (sampled : SocketReferenceRecording.at references recording position = some (current, following)) :
    ∃ tick, ticks[position]? = some tick := by
  induction recording generalizing position with
  | nil => cases sampled
  | @cons before middle after callers next final tick ticks row tail first between last actual rest ih =>
    cases position with
    | zero => exact ⟨tick, rfl⟩
    | succ position => exact ih sampled

theorem socket_reference_backward {before after : Processes} {callers next : NativeProcesses} {tick : ActorTick runtime}
    {row : NativeExternalStep process child native hostUid before callers tick after next}
    {first last : SocketReferenceSnapshot} (actual : references.observed row first last)
    (socket : SocketLifetime) (old : tick.before.shared.descriptionAllocated socket.description = true)
    (held : last.held socket) : first.held socket := by
  obtain ⟨place, handle, present, identity⟩ := held
  obtain ⟨original, source, input, object, description⟩ := references.copied actual place handle present
    (by simpa only [identity.2] using old)
  exact ⟨original, source, input, object.trans identity.1, description.trans identity.2⟩

-- §FS-host-boundary.ownership: This is OFD lifetime continuity, not a queue
-- or exclusive-reader assertion. It allows arbitrary changes to unrelated
-- handles and every callback, failed operation, loss and retiring row.
theorem SocketReferenceRecording.backward (lifetimes : ReferenceContract runtime)
    {before after : Processes} {callers next : NativeProcesses} {ticks : List (ActorTick runtime)}
    {journal : NativeExternalJournal process child native hostUid before callers ticks after next}
    {first last : SocketReferenceSnapshot} (recording : SocketReferenceRecording references journal first last)
    (socket : SocketLifetime) (old : first.population.shared.descriptionAllocated socket.description = true)
    (held : last.held socket) : first.held socket := by
  induction recording with
  | nil => exact held
  | @cons before middle after callers next final tick ticks row tail first between last actual rest ih =>
    have input := (references.input actual).1
    have output := (references.output actual).1
    have allocated : tick.before.shared.descriptionAllocated socket.description = true := by
      simpa only [input] using old
    have later := actor_step_description_allocated lifetimes tick.operation socket.description allocated
    have current := ih (by simpa only [output] using later) held
    exact socket_reference_backward references actual socket allocated current

-- A structurally selected actual row exposes its actual input/output sample
-- and the exact prefix/suffix of this same reference recording.
theorem SocketReferenceRecording.selected_cut
    {before after : Processes} {callers next : NativeProcesses} {ticks : List (ActorTick runtime)}
    {journal : NativeExternalJournal process child native hostUid before callers ticks after next}
    {first last : SocketReferenceSnapshot} (recording : SocketReferenceRecording references journal first last)
    {position : Nat} (point : SelectedNativeCut process child native hostUid before after callers next ticks position)
    (selected : selectNativeCut journal position = some point) :
    ∃ current following,
      ∃ _preceding : SocketReferenceRecording references point.cut.first first current,
      ∃ suffix : SocketReferenceRecording references point.cut.last following last,
      SocketReferenceRecording.at references recording position = some (current, following) ∧
      references.observed point.cut.current current following ∧
      ∀ offset, SocketReferenceRecording.at references suffix offset =
        SocketReferenceRecording.at references recording (position + 1 + offset) := by
  induction recording generalizing position with
  | nil => cases selected
  | @cons before middle after callers next final tick ticks row tail first between last actual rest ih =>
    cases position with
    | zero =>
      have identity : point = ⟨tick, ⟨[], ticks, rfl, rfl, before, middle, callers, next, .nil _ _, row, tail⟩⟩ :=
        (Option.some.inj selected).symm
      cases identity
      refine ⟨first, between, .nil _ _ _, rest, rfl, actual, ?_⟩
      intro offset
      simp only [SocketReferenceRecording.at, Nat.zero_add, Nat.add_comm 1 offset]
    | succ position =>
      let extend := fun (chosen : SelectedNativeCut process child native hostUid middle after next final ticks position) =>
        ({ tick := chosen.tick
           cut := { chosen.cut with
             leading := tick :: chosen.cut.leading
             count := by simp only [List.length_cons, chosen.cut.count]
             shape := by simp only [chosen.cut.shape, List.cons_append]
             first := .cons row chosen.cut.first } } :
          SelectedNativeCut process child native hostUid before after callers final (tick :: ticks) (position + 1))
      change (selectNativeCut tail position).map extend = some point at selected
      cases earlier : selectNativeCut tail position with
      | none => simp only [earlier, Option.map_none] at selected; cases selected
      | some chosen =>
        obtain ⟨current, following, preceding, suffix, sampled, operation, suffixAt⟩ := ih chosen earlier
        simp only [earlier, Option.map_some] at selected
        have identity := (Option.some.inj selected).symm
        cases identity
        refine ⟨current, following, .cons actual preceding, suffix, sampled, operation, ?_⟩
        intro offset
        simpa only [SocketReferenceRecording.at, Nat.succ_add] using suffixAt offset

theorem SocketReferenceRecording.description_allocated (lifetimes : ReferenceContract runtime)
    {before after : Processes} {callers next : NativeProcesses} {ticks : List (ActorTick runtime)}
    {journal : NativeExternalJournal process child native hostUid before callers ticks after next}
    {first last : SocketReferenceSnapshot} (recording : SocketReferenceRecording references journal first last)
    (description : DescriptionId) (old : first.population.shared.descriptionAllocated description = true) :
    last.population.shared.descriptionAllocated description = true := by
  induction recording with
  | nil => exact old
  | @cons before middle after callers next final tick ticks row tail first between last actual rest ih =>
    have input := (references.input actual).1
    have output := (references.output actual).1
    have allocated : tick.before.shared.descriptionAllocated description = true := by
      simpa only [input] using old
    have next := actor_step_description_allocated lifetimes tick.operation description allocated
    exact ih (by simpa only [output] using next)

theorem SocketReferenceRecording.selected_input_lifetime
    {before after : Processes} {callers next : NativeProcesses} {ticks : List (ActorTick runtime)}
    {journal : NativeExternalJournal process child native hostUid before callers ticks after next}
    {first last : SocketReferenceSnapshot} (recording : SocketReferenceRecording references journal first last)
    {position : Nat} (point : SelectedNativeCut process child native hostUid before after callers next ticks position)
    (selected : selectNativeCut journal position = some point) (current following : SocketReferenceSnapshot)
    (sampled : SocketReferenceRecording.at references recording position = some (current, following))
    (socket : SocketLifetime) (held : current.held socket) :
    point.tick.before.shared.descriptionAllocated socket.description = true := by
  obtain ⟨actualCurrent, actualFollowing, preceding, suffix, atRow, operation, suffixAt⟩ :=
    SocketReferenceRecording.selected_cut references recording point selected
  have states := Prod.mk.inj (Option.some.inj (atRow.symm.trans sampled))
  have beforeHeld : actualCurrent.held socket := states.1.symm ▸ held
  obtain ⟨place, handle, live, identity⟩ := beforeHeld
  have old := references.input_lifetime operation place handle live
  simpa only [identity.2] using old

-- §FS-host-boundary.ownership: An actual terminal live reference excludes a
-- last-OFD drop at each earlier sampled boundary of this interval. No future
-- SDK reply, engine completion, reaping or queue content is required.
theorem SocketReferenceRecording.selected_held (lifetimes : ReferenceContract runtime)
    {before after : Processes} {callers next : NativeProcesses} {ticks : List (ActorTick runtime)}
    {journal : NativeExternalJournal process child native hostUid before callers ticks after next}
    {first last : SocketReferenceSnapshot} (recording : SocketReferenceRecording references journal first last)
    (socket : SocketLifetime) (old : first.population.shared.descriptionAllocated socket.description = true)
    (held : last.held socket)
    {position : Nat} (point : SelectedNativeCut process child native hostUid before after callers next ticks position)
    (selected : selectNativeCut journal position = some point) :
    ∃ current following,
      SocketReferenceRecording.at references recording position = some (current, following) ∧
      current.held socket ∧ following.held socket := by
  obtain ⟨current, following, preceding, suffix, sampled, operation, suffixAt⟩ := SocketReferenceRecording.selected_cut references recording point selected
  have allocated := SocketReferenceRecording.description_allocated references lifetimes preceding socket.description old
  have input := (references.input operation).1
  have output := (references.output operation).1
  have atInput : point.tick.before.shared.descriptionAllocated socket.description = true := by
    simpa only [input] using allocated
  have atOutput := actor_step_description_allocated lifetimes point.tick.operation socket.description atInput
  have followingHeld := SocketReferenceRecording.backward references lifetimes suffix socket (by simpa only [output] using atOutput) held
  exact ⟨current, following, sampled,
    socket_reference_backward references operation socket atInput followingHeld, followingHeld⟩

end LeanCage.Host.PrivateStreams
