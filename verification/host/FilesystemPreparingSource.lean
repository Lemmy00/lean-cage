import FilesystemPreparingReferences
import FilesystemStageReference

namespace LeanCage.Host.Kernel
open Filesystem
universe u

private theorem chunks_profile {logical raw : List Program.Event} {allowed : Request → Prop}
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

private theorem nondestructive_closed (primary candidate : Request) (safe : ¬ DestructiveRequest primary)
    (role : AdapterRequest primary candidate) : ¬ DestructiveRequest candidate := by
  rcases role with same | magic | flags | close
  · change candidate = primary at same
    rw [same]
    exact safe
  · simp [DestructiveRequest, magic]
  · simp [DestructiveRequest, flags]
  · simp [DestructiveRequest, close]

private theorem chunks_quiet {logical raw : List Program.Event}
    (source : PrimitiveFilesystem.Chunks logical raw) (quiet : ∀ event ∈ logical, NondestructiveEvent event) :
    ∀ event ∈ raw, NondestructiveEvent event :=
  chunks_profile source nondestructive_closed quiet

private theorem drop_append_allowed {α : Type u} {first last : List α} (count : Nat) (allowed : α → Prop)
    (leading : ∀ event ∈ first.drop count, allowed event) (trailing : ∀ event ∈ last, allowed event) :
    ∀ event ∈ (first ++ last).drop count, allowed event := by
  intro event member
  rw [List.drop_append] at member
  rcases List.mem_append.mp member with member | member
  · exact leading event member
  · exact trailing event (List.mem_of_mem_drop member)

-- §FS-host-boundary.ownership: Every actual call before this interrupted
-- preparation is nondestructive. In particular no future prepare result
-- supplies the root lifetime, current binding or ownership.
theorem PreparingStageContinuation.source_nondestructive {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {before : List Program.Event} {request : Request}
    {call : PublicationPreparing.Call before request} {limit : Nat} {current : World}
    (source : PreparingStageContinuation runtime initial all call limit current) (events : List Program.Event)
    (trace : events = source.earlier.source.input.events ++ .returned (.filesystem source.opening.request) source.opening.reply ::
      (source.earlier.post.map Program.filesystemEvent ++ source.earlier.remaining ++ source.earlier.guards))
    (guarded : ∀ event ∈ source.earlier.guards, NondestructiveEvent event) :
    ∀ event ∈ events.drop (source.root.use.engine.events.length + 1), NondestructiveEvent event := by
  apply Eq.mpr (congrArg (fun actualEvents : List Program.Event =>
    ∀ event ∈ actualEvents.drop (source.root.use.engine.events.length + 1), NondestructiveEvent event) trace)
  apply drop_append_allowed
  · intro event member
    exact passive_event_nondestructive (source.root.probes event member)
  · intro event member
    rcases List.mem_cons.mp member with rfl | member
    · simp only [NondestructiveEvent, DestructiveRequest, source.opening.opening]
      decide
    · rcases List.mem_append.mp member with member | guardMember
      · rcases List.mem_append.mp member with postMember | remainingMember
        · obtain ⟨⟨operation, reply⟩, occurs, rfl⟩ := List.mem_map.mp postMember
          exact namespace_passive_not_destructive (source.earlier.passive (operation, reply) occurs)
        · apply chunks_quiet source.earlier.chunks ?_ event remainingMember
          intro candidate occurs
          rcases List.mem_append.mp occurs with inspected | preparing
          · obtain ⟨information, shape⟩ := source.opening.inspection
            have same : candidate = .returned (.filesystem {
                op := .stat, first := call.context.stage.directory.fd}) information := by
              simpa only [shape, List.map_cons, List.map_nil, List.mem_singleton, Program.filesystemEvent] using inspected
            subst candidate
            simp [NondestructiveEvent, DestructiveRequest]
          · obtain ⟨⟨operation, reply⟩, member, rfl⟩ := List.mem_map.mp preparing
            have allowed := request_prefix (publication_prepare_nondestructive _ _ _ _ _ _ _) call.active
              (operation, reply) (List.mem_append_left _ member)
            cases reply <;> exact allowed
      · exact guarded event guardMember

theorem PreparingStageResources.guards_nondestructive {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    {adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed}
    {call : PublicationPreparing.Call adapter.occurrence.logicalBefore request} {position : Nat}
    (resources : PreparingStageResources adapter call position) (primary : request = adapter.occurrence.primary) :
    ∀ event ∈ resources.source.earlier.guards, NondestructiveEvent event := by
  have safe : ¬ DestructiveRequest request :=
    request_prefix (publication_prepare_nondestructive _ _ _ _ _ _ _) call.active (request, none) (by simp)
  rw [resources.guards]
  intro event member
  obtain ⟨⟨operation, reply⟩, occurs, rfl⟩ := List.mem_map.mp member
  have role := profile_prefix (guarded_call_profile adapter.occurrence.primary) adapter.occurrence.adapter
    (operation, reply) (List.mem_append_left _ occurs)
  have quiet := nondestructive_closed request operation safe (primary ▸ role)
  cases reply <;> exact quiet

end LeanCage.Host.Kernel
