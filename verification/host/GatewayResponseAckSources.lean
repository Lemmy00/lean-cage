import GatewayActorLaunchIdentity
import GatewayWriterCursor
import FilesystemOutputSources

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {ticks : List (ActorTick runtime)} {pair : Pair}

theorem actor_history_returned_origin {actor : ActorId} {origin : OperationOrigin}
    {ordinal : Nat} {before after : World} {events : List Program.Event}
    (history : ActorHistoryWith runtime actor origin ordinal before events after)
    (index : Nat) {β : Type} (effect : Effect β) (reply : β)
    (selected : events[index]? = some (.returned effect reply)) :
    ∃ first last, origin (ordinal + index) β effect reply first last := by
  induction history generalizing index with
  | nil => cases selected
  | returned actual recorded tail ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at selected
      cases selected
      exact ⟨_, _, by simpa only [Nat.add_zero] using recorded⟩
    | succ index =>
      obtain ⟨first, last, source⟩ := ih index selected
      exact ⟨first, last, by simpa only [Nat.add_assoc, Nat.add_comm 1 index] using source⟩
  | environment actual tail ih => exact ih index selected

theorem acknowledged_source_request {fd : UInt64} {bytes : ByteArray} {first last : Nat}
    {events : List (Request × Reply)} (source : EntrypointWriterPrefix.AcknowledgedPrefix fd bytes first events last)
    (index : Nat) (event : Request × Reply) (selected : events[index]? = some event) :
    event.1.op = .write ∧ event.1.first = fd := by
  induction source generalizing index with
  | nil => cases selected
  | more offset reply events last inside native empty positive bounded tail ih =>
    cases index with
    | zero => cases Option.some.inj selected; exact ⟨rfl, rfl⟩
    | succ index => exact ih index selected

theorem acknowledged_source_reply {fd : UInt64} {bytes : ByteArray} {first last : Nat}
    {events : List (Request × Reply)} (source : EntrypointWriterPrefix.AcknowledgedPrefix fd bytes first events last)
    (index : Nat) (event : Request × Reply) (selected : events[index]? = some event) :
    nativeError event.2 = false ∧ 0 < event.2.1.toNat ∧ event.2.1.toNat ≤ event.1.left.size := by
  induction source generalizing index with
  | nil => cases selected
  | more offset reply events last inside native empty positive bounded tail ih =>
    cases index with
    | zero => cases Option.some.inj selected; exact ⟨native, positive, bounded⟩
    | succ index => exact ih index selected

-- §FS-host-boundary.caller: Every earlier source ACK is recovered as an
-- actual global row with the SAME handoff and retained response descriptor.
-- Neither later teardown nor a second equal-transcript execution supplies it.
theorem actual_response_ack_source_indexed
    (descriptors : DescriptorContract kernel) (directories : DirectoryRetirementContract kernel)
    (sdk : RuntimeDescriptorContract runtime) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (environment : InterferenceContract kernel)
    {initial : World} {final : Population}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    (last : EngineWriteEntry ticks pair) (response : EngineResponse last)
    (history : SelectedActorHistory runtime initial ticks last.tick last.actor last.engine)
    (handle : Handle) (inherited : history.launch.references 1 = some handle)
    (endpoint : handle.object = pair.engine)
    (index : Nat) (event : Request × Reply)
    (selected : response.source.writer.acknowledged[index]? = some event) :
    ∃ entry : EngineWriteEntry ticks pair,
      entry.actor = last.actor ∧ entry.request = event.1 ∧ entry.handle = handle ∧ entry.sender = .engine ∧
      EngineWriteObservation entry (some event.2) ∧ entry.position < last.position ∧
      entry.engine.events.length = last.engine.events.length - response.source.writer.acknowledged.length + index := by
  obtain ⟨raw, returned, shape⟩ := pending_response_raw response.pending response.source
  have atEvent : last.engine.events[raw.length + index]? = some (Program.filesystemEvent event) := by
    rw [shape, List.getElem?_append_right (by omega)]
    simpa only [Nat.add_sub_cancel_left, List.getElem?_map, Option.map_some] using
      congrArg (Option.map Program.filesystemEvent) selected
  obtain ⟨before, after, source⟩ := actor_history_returned_origin history.history (raw.length + index)
    (.filesystem event.1) event.2 atEvent
  obtain ⟨position, tick, engine, afterEngine, atTick, action, present, afterPresent, ordinal, beforeWorld, afterWorld⟩ := source
  have observed : tick.action.eventFor last.actor = some (Program.filesystemPrefixEvent (event.1, some event.2)) := by
    simp only [action, ActorAction.eventFor, ite_true, Program.filesystemPrefixEvent]
  obtain ⟨actual, next, actualPresent, running, head⟩ :=
    actual_filesystem_observation_head tick.operation last.actor event.1 (some event.2) observed
  have identity := Option.some.inj (present.symm.trans actualPresent)
  subst actual
  obtain ⟨earlier⟩ := actual_selected_actor_history descriptors lifetimes references environment journal atTick observed present
  have sameLaunch := selected_launch_references_unique journal earlier history
  have inheritedEarlier : earlier.launch.references 1 = some handle := by rw [sameLaunch]; exact inherited
  have live := actual_live_inherited_reference descriptors directories sdk journal earlier present running inheritedEarlier
  obtain ⟨writing, fd⟩ := acknowledged_source_request response.source.writer.progress index event selected
  let entry : EngineWriteEntry ticks pair := {
    position, tick, selected := atTick, actor := last.actor, engine, present, running,
    request := event.1, next, head, writing, sender := .engine, handle,
    input := by simpa only [fd] using live, endpoint }
  refine ⟨entry, rfl, rfl, rfl, rfl, ⟨observed⟩, ?_, ?_⟩
  · have count := (List.getElem?_eq_some_iff.mp selected).1
    have length : last.engine.events.length = raw.length + response.source.writer.acknowledged.length := by
      simp only [shape, List.length_append, List.length_map]
    by_cases ordered : position < last.position
    · exact ordered
    · have backwards := selected_events_prefix journal (by omega) last.selected atTick last.actor last.engine engine
        last.present present
      have bound := List.IsPrefix.length_le backwards
      omega
  · have length : last.engine.events.length = raw.length + response.source.writer.acknowledged.length := by
      simp only [shape, List.length_append, List.length_map]
    change engine.events.length = _
    omega

-- The original source-only interface is retained for consumers that do not
-- need the exact raw ordinal of each acknowledged write.
theorem actual_response_ack_source
    (descriptors : DescriptorContract kernel) (directories : DirectoryRetirementContract kernel)
    (sdk : RuntimeDescriptorContract runtime) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (environment : InterferenceContract kernel)
    {initial : World} {final : Population}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    (last : EngineWriteEntry ticks pair) (response : EngineResponse last)
    (history : SelectedActorHistory runtime initial ticks last.tick last.actor last.engine)
    (handle : Handle) (inherited : history.launch.references 1 = some handle)
    (endpoint : handle.object = pair.engine)
    (index : Nat) (event : Request × Reply)
    (selected : response.source.writer.acknowledged[index]? = some event) :
    ∃ entry : EngineWriteEntry ticks pair,
      entry.actor = last.actor ∧ entry.request = event.1 ∧ entry.handle = handle ∧ entry.sender = .engine ∧
      EngineWriteObservation entry (some event.2) ∧ entry.position < last.position := by
  obtain ⟨entry, actor, request, held, sender, observed, position, _⟩ :=
    actual_response_ack_source_indexed descriptors directories sdk lifetimes references environment
      journal last response history handle inherited endpoint index event selected
  exact ⟨entry, actor, request, held, sender, observed, position⟩

end LeanCage.Host.PrivateStreams
