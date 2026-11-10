import FilesystemReferenceLifetime
import FilesystemRecording
import FilesystemRemovalJournal

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

def NamespacePassiveEvent : Program.Event → Prop
  | .returned (.filesystem request) _ | .lost (.filesystem request) => NamespacePassive request
  | _ => True

def NondestructiveEvent : Program.Event → Prop
  | .returned (.filesystem request) _ | .lost (.filesystem request) => ¬ DestructiveRequest request
  | _ => True

def RequestEvent (allowed : Request → Prop) : Program.Event → Prop
  | .returned (.filesystem request) _ | .lost (.filesystem request) => allowed request
  | _ => True

theorem actor_journal_presence {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {before after : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime before ticks after) {actor : ActorId} {engine : EngineState}
    (present : before.actors actor = some engine) : ∃ final, after.actors actor = some final := by
  induction journal generalizing engine with
  | nil => exact ⟨engine, present⟩
  | @cons tick ticks after tail ih =>
    obtain ⟨middle, middlePresent⟩ := actor_step_presence tick.operation present
    exact ih middlePresent

-- §FS-host-boundary.ownership: The same selected source event appends exactly once to
-- this actor's transcript. Peer and retirement events cannot produce that append.
theorem source_event_after {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (tick : ActorTick runtime) {actor : ActorId} {engine : EngineState} {event : Program.Event}
    (action : tick.action.eventFor actor = some event) (present : tick.before.actors actor = some engine) :
    ∃ final, tick.after.actors actor = some final ∧ final.events = engine.events ++ [event] := by
  rcases tick with ⟨kind, before, after, actual⟩
  cases actual with
  | launch | foreign | retire | nativeRetire => cases action
  | @returned β population owner current effect next reply world currentPresent alive head operation =>
    dsimp only [ActorAction.eventFor] at action
    split at action
    · rename_i same
      subst owner
      cases action
      have identity := Option.some.inj (present.symm.trans currentPresent)
      subst engine
      exact ⟨current.returned effect reply next world, by simp [Population.advance, Population.install], rfl⟩
    · cases action
  | @lost β population owner current effect next world currentPresent alive head operation =>
    dsimp only [ActorAction.eventFor] at action
    split at action
    · rename_i same
      subst owner
      cases action
      have identity := Option.some.inj (present.symm.trans currentPresent)
      subst engine
      exact ⟨current.lost effect world, by simp [Population.advance, Population.install], rfl⟩
    · cases action

theorem OwnershipJournal.actual {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {all : List (ActorTick runtime)} {catalogue : Catalogue runtime all}
    {before after : Population} {first final : Family} {ticks : List (ActorTick runtime)}
    (history : OwnershipJournal runtime catalogue before first ticks after final) :
    ActorJournal runtime before ticks after := by
  induction history with
  | nil => exact .nil _
  | cons step tail ih => exact .cons ih

-- §FS-host-boundary.ownership: A source suffix profile classifies every SAME-actor kernel
-- event in the actual interval. It frames no peer, namespace, contents, or inode lifetime.
theorem actor_interval_request_profile {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (allowed : Request → Prop)
    {before after : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime before ticks after) {actor : ActorId} {initial final : EngineState}
    (initialPresent : before.actors actor = some initial) (finalPresent : after.actors actor = some final)
    (profile : ∀ event ∈ final.events.drop initial.events.length, RequestEvent allowed event) :
    ∀ tick ∈ ticks, ∀ request observed,
      tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)) → allowed request := by
  intro tick member request observed action
  obtain ⟨position, bound, selected⟩ := List.mem_iff_getElem.mp member
  have selectedAt : ticks[position]? = some tick := List.getElem?_eq_some_iff.mpr ⟨bound, selected⟩
  obtain ⟨leading, trailing, shape⟩ := selected_tick_split selectedAt
  rw [shape] at journal
  obtain ⟨middle, first, rest⟩ := actor_journal_split leading _ journal
  cases rest with
  | cons tail =>
    obtain ⟨earlier, earlierPresent⟩ := actor_journal_presence first initialPresent
    obtain ⟨later, laterPresent, appended⟩ := source_event_after tick action earlierPresent
    obtain ⟨priorEvents, beforeTrace⟩ := actor_journal_event_prefix first actor initial earlier initialPresent earlierPresent
    obtain ⟨lastEvents, afterTrace⟩ := actor_journal_event_prefix tail actor later final laterPresent finalPresent
    have suffix : final.events.drop initial.events.length =
        priorEvents ++ Program.filesystemPrefixEvent (request, observed) :: lastEvents := by
      rw [afterTrace, appended, beforeTrace]
      simp only [List.append_assoc, List.singleton_append, List.drop_left]
    have passive := profile (Program.filesystemPrefixEvent (request, observed)) (by rw [suffix]; simp)
    cases observed <;> exact passive

-- §AR-host-boundary.interfaces: Preserve the original exact read/probe source profile.
theorem actor_interval_source_profile {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {before after : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime before ticks after) {actor : ActorId} {initial final : EngineState}
    (initialPresent : before.actors actor = some initial) (finalPresent : after.actors actor = some final)
    (profile : ∀ event ∈ final.events.drop initial.events.length, NamespacePassiveEvent event) :
    ∀ tick ∈ ticks, ∀ request observed,
      tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)) → NamespacePassive request :=
  actor_interval_request_profile NamespacePassive journal initialPresent finalPresent profile

theorem actor_interval_nondestructive_profile {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {before after : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime before ticks after) {actor : ActorId} {initial final : EngineState}
    (initialPresent : before.actors actor = some initial) (finalPresent : after.actors actor = some final)
    (profile : ∀ event ∈ final.events.drop initial.events.length, NondestructiveEvent event) :
    ∀ tick ∈ ticks, ∀ request observed,
      tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)) → ¬ DestructiveRequest request :=
  actor_interval_request_profile (fun request => ¬ DestructiveRequest request) journal initialPresent finalPresent profile

end LeanCage.Host.Kernel
