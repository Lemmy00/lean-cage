import FilesystemApplicationLowering
import FilesystemRecording
import PrefixOrigins

namespace LeanCage.Host.PrimitiveFilesystem

-- §AR-host-boundary.primitives: Each completed source call retains its exact raw adapter chunk.
inductive Reached {α : Type} :
    Program α → List Program.Event → List Program.Event → Program α → Prop where
  | refl (program : Program α) : Reached program [] [] program
  | call {β : Type} (effect : Effect β) (next : β → Program α) (reply : β)
      (inside logical raw : List Program.Event) (after : Program α)
      (adapter : Program.Returns (lowerEffect effect) inside reply)
      (rest : Reached (next reply) logical raw after) :
      Reached (.call effect next) (.returned effect reply :: logical) (inside ++ raw) after

theorem reached_source {α : Type} {program after : Program α}
    {logical raw : List Program.Event} (source : Reached program logical raw after) :
    Kernel.Residual program logical after := by
  induction source with
  | refl => exact .refl _
  | call effect next reply inside logical raw after adapter rest ih => exact .call ih

structure Occurrence {α : Type} (program : Program α) (before : List Program.Event)
    (event : Program.Event) where
  replyType : Type
  effect : Effect replyType
  next : replyType → Program α
  logicalBefore : List Program.Event
  rawBefore : List Program.Event
  inside : List Program.Event
  reached : Reached program logicalBefore rawBefore (.call effect next)
  adapter : Program.Prefix (lowerEffect effect) (inside ++ [event])
  trace : before = rawBefore ++ inside

-- §FS-host-boundary.acceptance: The chosen last event remains at the same raw source position.
theorem lowered_last_source {α : Type} (program : Program α)
    {before : List Program.Event} {event : Program.Event}
    (source : Program.Prefix (lower program) (before ++ [event])) :
    Nonempty (Occurrence program before event) := by
  induction program generalizing before with
  | pure value => exact False.elim (Program.pure_has_no_last value before event source)
  | @call β effect next ih =>
    change Program.Prefix ((lowerEffect effect).bind (fun reply => lower (next reply)))
      (before ++ [event]) at source
    rcases Program.last_bind_split _ _ source with active |
        ⟨initial, reply, inside, completed, active, trace⟩
    · exact ⟨⟨β, effect, next, [], [], before, .refl _, active, rfl⟩⟩
    · obtain ⟨occurrence⟩ := ih reply active
      exact ⟨{
        occurrence with
        logicalBefore := .returned effect reply :: occurrence.logicalBefore
        rawBefore := initial ++ occurrence.rawBefore
        reached := .call effect next reply initial _ _ _ completed occurrence.reached
        trace := trace.trans ((congrArg (initial ++ ·) occurrence.trace).trans
          (List.append_assoc initial occurrence.rawBefore occurrence.inside).symm) }⟩

def filesystemEvent? : Program.Event → Option (Filesystem.Request × Option Filesystem.Reply)
  | .returned (.filesystem request) reply => some (request, some reply)
  | .lost (.filesystem request) => some (request, none)
  | _ => none

theorem filesystem_event_decode (event : Filesystem.Request × Option Filesystem.Reply) :
    filesystemEvent? (Program.filesystemPrefixEvent event) = some event := by
  rcases event with ⟨request, observed⟩
  cases observed <;> rfl

private def filesystemEffect {α : Type} : Effect α → Bool
  | .filesystem _ => true
  | _ => false

private def filesystemEvent : Program.Event → Bool
  | .returned effect _ => filesystemEffect effect
  | .lost effect => filesystemEffect effect

private theorem effect_prefix_profile {α : Type} (effect : Effect α)
    {events : List Program.Event} (source : Program.Prefix (Program.effect effect) events) :
    ∀ event ∈ events, filesystemEvent event = filesystemEffect effect := by
  cases source with
  | empty => simp
  | lost =>
    intro event member
    have same := List.mem_singleton.mp member
    subst event
    rfl
  | returned _ _ reply tail rest =>
    have empty := Program.pure_prefix_empty _ rest
    subst tail
    intro event member
    have same := List.mem_singleton.mp member
    subst event
    rfl

private theorem runtime_no_filesystem {α : Type} (effect : Effect α)
    (runtime : filesystemEffect effect = false) (before : List Program.Event)
    (event : Filesystem.Request × Option Filesystem.Reply) :
    ¬ Program.Prefix (Program.effect effect) (before ++ [Program.filesystemPrefixEvent event]) := by
  intro source
  have profile := effect_prefix_profile effect source (Program.filesystemPrefixEvent event) (by simp)
  rw [runtime] at profile
  rcases event with ⟨request, observed⟩
  cases observed <;> cases profile

structure FilesystemOccurrence {α : Type} (program : Program α)
    (before : List Program.Event) (request : Filesystem.Request) (observed : Option Filesystem.Reply) where
  primary : Filesystem.Request
  next : Filesystem.Reply → Program α
  logicalBefore : List Program.Event
  rawBefore : List Program.Event
  inside : List (Filesystem.Request × Option Filesystem.Reply)
  reached : Reached program logicalBefore rawBefore (.call (.filesystem primary) next)
  adapter : Filesystem.Prefix (Filesystem.guardedCall primary) (inside ++ [(request, observed)])
  trace : before = rawBefore ++ inside.map Program.filesystemPrefixEvent

-- §FS-host-boundary.lookup: The same raw syscall belongs to this actual original caller effect.
theorem lowered_filesystem_source {α : Type} (program : Program α)
    {before : List Program.Event} {request : Filesystem.Request} {observed : Option Filesystem.Reply}
    (source : Program.Prefix (lower program)
      (before ++ [Program.filesystemPrefixEvent (request, observed)])) :
    Nonempty (FilesystemOccurrence program before request observed) := by
  obtain ⟨⟨replyType, effect, next, logicalBefore, rawBefore, inside, reached, adapter, trace⟩⟩ :=
    lowered_last_source program source
  cases effect with
  | filesystem primary =>
    obtain ⟨events, actual, eventsTrace⟩ := Program.lift_filesystem_prefix_source
      (Filesystem.guardedCall primary) adapter
    rcases List.eq_nil_or_concat events with empty | ⟨leading, final, shape⟩
    · subst events
      have lengths := congrArg List.length eventsTrace
      simp only [List.length_append, List.length_singleton, List.map_nil, List.length_nil] at lengths
      omega
    · rw [List.concat_eq_append] at shape
      subst events
      rw [List.map_append, List.map_singleton] at eventsTrace
      have split := List.of_concat_eq_concat (by
        simpa only [List.concat_eq_append] using eventsTrace)
      have same := Option.some.inj (by
        simpa only [filesystem_event_decode] using congrArg filesystemEvent? split.2)
      subst final
      exact ⟨⟨primary, next, logicalBefore, rawBefore, leading, reached, actual,
        by rw [trace, split.1]⟩⟩
  | spawn arguments | read handle amount | wait child | terminate child | tryWait child | descriptor handle =>
    exact False.elim (runtime_no_filesystem _ rfl inside (request, observed) adapter)

-- §FS-host-boundary.ownership: Existing caller phase proofs consume this derived logical cut.
theorem filesystem_occurrence_logical {α : Type} {program : Program α}
    {before : List Program.Event} {request : Filesystem.Request} {observed : Option Filesystem.Reply}
    (occurrence : FilesystemOccurrence program before request observed) :
    Program.Prefix program (occurrence.logicalBefore ++ [.lost (.filesystem occurrence.primary)]) :=
  Kernel.residual_prefix (reached_source occurrence.reached) (.lost _ _)

theorem filesystem_occurrence_request {α : Type} {program : Program α}
    {before : List Program.Event} {request : Filesystem.Request} {observed : Option Filesystem.Reply}
    (occurrence : FilesystemOccurrence program before request observed) :
    Filesystem.AdapterRequest occurrence.primary request :=
  Filesystem.profile_prefix (Filesystem.guarded_call_profile _) occurrence.adapter
    (request, observed) (by simp)

theorem filesystem_occurrence_primary {α : Type} {program : Program α}
    {before : List Program.Event} {request : Filesystem.Request} {observed : Option Filesystem.Reply}
    (occurrence : FilesystemOccurrence program before request observed)
    (magic : request.op ≠ .filesystemType) (flags : request.op ≠ .inodeFlags)
    (close : request.op ≠ .close) : request = occurrence.primary := by
  rcases filesystem_occurrence_request occurrence with same | extra | extra | extra
  · exact same
  · exact False.elim (magic extra)
  · exact False.elim (flags extra)
  · exact False.elim (close extra)

end LeanCage.Host.PrimitiveFilesystem

namespace LeanCage.Host.Kernel
open Filesystem

-- §AR-host-boundary.primitives: This is the source program executed by the raw interpreter.
abbrev PrimitiveActorRuntime (kernel : Contract) :=
  ActorRuntime kernel (PrimitiveFilesystem.lower Entrypoint.run)

theorem selected_primitive_filesystem {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply} (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) :
    Nonempty (PrimitiveFilesystem.FilesystemOccurrence Entrypoint.run engine.events request observed) :=
  PrimitiveFilesystem.lowered_filesystem_source Entrypoint.run
    (selected_source_prefix_for journal selected action present)

end LeanCage.Host.Kernel
