import FilesystemMarkerBindings.Invocation

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: The marker's actual run descriptor is produced, not supplied.
theorem selected_private_marker_handle {kernel : Contract} {runtime : ActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (environment : InterferenceContract kernel)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply}
    (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (setting : request.op = .setAttribute) (named : request.left = PrivateNames.attributeName) :
    ∃ handle, engine.references request.first = some handle ∧ handle.rawOwned = true := by
  obtain ⟨invocation⟩ := entrypoint_private_marker_call (selected_source_prefix journal selected action present)
    setting named
  obtain ⟨source⟩ := run_marker_call invocation.active setting
  obtain ⟨actorHistory⟩ := actual_selected_actor_history descriptors lifetimes references environment
    journal selected action present
  have trace : engine.events =
      (invocation.context ++ source.selecting.map Program.filesystemEvent) ++
        source.creating.map Program.filesystemEvent := by
    conv => lhs; rw [invocation.trace, source.trace]
    simp only [Publication.completed, List.map_append, List.map_map, List.append_assoc]
    rfl
  have history := actorHistory.history
  rw [trace] at history
  obtain ⟨first, leading, created⟩ := actor_with_split
    (invocation.context ++ source.selecting.map Program.filesystemEvent) _ history
  obtain ⟨handle, live, raw⟩ := actual_child_handle descriptors source.uid source.container.fd
    PrivateNames.prefixText ⟨source.created, recorded_history_erase (actor_recorded_filesystem created)⟩
  have fd := congrArg Request.first source.operation
  exact ⟨handle, by simpa only [fd, Population.project] using live, raw⟩

-- §FS-host-boundary.acceptance: Every actual application setter has its genuine raw binding.
theorem selected_attribute_handle {kernel : Contract} {runtime : ActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (environment : InterferenceContract kernel)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply}
    (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) (setting : request.op = .setAttribute) :
    ∃ handle, engine.references request.first = some handle ∧ handle.rawOwned = true := by
  rcases selected_authority_safe journal selected action present setting with privateName | publicationName
  · exact selected_private_marker_handle descriptors lifetimes references environment journal selected action present
      setting privateName
  · exact selected_publisher_marker_handle descriptors lifetimes references environment journal selected action present
      setting publicationName

end LeanCage.Host.Kernel
