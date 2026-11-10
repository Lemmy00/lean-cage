import FilesystemSourceIntervals
import FilesystemAccessProofs.Profiles
import FilesystemPrimitiveFrames

namespace LeanCage.Host.Kernel
open Filesystem

private theorem adapter_nondestructive {primary : Request} (safe : ¬ DestructiveRequest primary)
    {candidate : Request} (role : AdapterRequest primary candidate) : ¬ DestructiveRequest candidate := by
  rcases role with same | magic | flags | close
  · exact same ▸ safe
  · unfold DestructiveRequest
    rw [magic]
    decide
  · unfold DestructiveRequest
    rw [flags]
    decide
  · simp only [DestructiveRequest, close]; decide

private theorem adapter_profile_nondestructive {α : Type} {program : Filesystem.Program α}
    (primary : Request) (safe : ¬ DestructiveRequest primary)
    (source : RequestProfile (AdapterRequest primary) program) :
    RequestProgram (fun request => ¬ DestructiveRequest request) program := by
  induction source with
  | pure => exact .pure _
  | call request next allowed following ih => exact .call (adapter_nondestructive safe allowed) ih

-- §FS-host-boundary.ownership: Actual raw adapter probes/rejection closes add no removal
-- or rename to a source-proved nondestructive program. Full hostile replies remain allowed.
theorem lower_nondestructive {α : Type} {program : Filesystem.Program α}
    (source : RequestProgram (fun request => ¬ DestructiveRequest request) program) :
    RequestProgram (fun request => ¬ DestructiveRequest request) program.lower := by
  induction source with
  | pure => exact .pure _
  | @call request next allowed following ih =>
    exact request_bind (adapter_profile_nondestructive request allowed (guarded_call_profile request)) ih

theorem requests_returned {α : Type} {program : Filesystem.Program α} {allowed : Request → Prop}
    (source : RequestProgram allowed program) {events : List (Request × Reply)} {value : α}
    (returned : Returns program events value) : ∀ event ∈ events, allowed event.1 := by
  induction returned with
  | pure => intro event impossible; cases impossible
  | call request next reply events value rest ih =>
    cases source with
    | call allowed following =>
      intro event member
      rcases List.mem_cons.mp member with rfl | member
      · exact allowed
      · exact ih (following reply) event member

theorem passive_event_nondestructive {event : Program.Event} (passive : NamespacePassiveEvent event) :
    NondestructiveEvent event := by
  cases event with
  | @returned β effect reply =>
    cases effect <;> dsimp only [NondestructiveEvent] <;> first
      | exact namespace_passive_not_destructive passive
      | exact True.intro
  | @lost β effect =>
    cases effect <;> dsimp only [NondestructiveEvent] <;> first
      | exact namespace_passive_not_destructive passive
      | exact True.intro

-- §FS-host-boundary.lookup: These are exactly the earlier raw parent probes of this
-- namespace call, retaining even an interrupted/lost selected primary operation.
theorem adapter_namespace_prefix_nondestructive {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {ticks : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial ticks tick actor engine request observed)
    (kind : NamespaceRequest request) :
    ∀ event ∈ adapter.occurrence.inside.map Program.filesystemPrefixEvent, NondestructiveEvent event := by
  obtain ⟨checks, checked, same, trace⟩ := guarded_namespace_last adapter.occurrence.adapter kind
  intro event member
  rw [trace, List.map_map] at member
  obtain ⟨⟨query, reply⟩, occurs, identity⟩ := List.mem_map.mp member
  subst event
  have operation := checked_parents_probes checked (query, reply) occurs
  change ¬ DestructiveRequest query
  rcases operation with magic | flags
  · unfold DestructiveRequest
    rw [magic]
    decide
  · unfold DestructiveRequest
    rw [flags]
    decide

end LeanCage.Host.Kernel
