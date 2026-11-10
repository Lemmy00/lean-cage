import FilesystemDirectoryHandles
import FilesystemCryptography

namespace LeanCage.Host.Kernel
open Filesystem

private theorem prepared_marker_handle {kernel : Contract} (laws : DescriptorContract kernel)
    (bundle : Validation.Bundle) (input : Publication.Input) (display stdoutHash stderrHash : ByteArray)
    (parent : Directories.Parent) (stage : Directories.Fresh)
    {beforeCalls : List (Request × Option Reply)} {request : Request}
    (source : Publication.PreparedMarkerCall bundle input display stdoutHash stderrHash parent stage beforeCalls request)
    (handle : Handle) {before after : World}
    (history : History kernel before (source.hashing ++ source.authenticating ++ source.filling) after)
    (live : before.handles stage.directory.fd = some handle) : after.handles request.first = some handle := by
  rw [List.append_assoc] at history
  obtain ⟨hashed, hashing, rest⟩ := history_split source.hashing _ history
  have hashLive := (borrow_returns (hash_borrow laws stage.directory.fd handle input.policy.raw)
    ⟨source.hashed, hashing⟩ live).1
  obtain ⟨authenticated, authentication, filling⟩ := history_split source.authenticating source.filling rest
  have authenticatedLive := (borrow_returns
    (authentication_borrow laws stage.directory.fd handle bundle
      (Publication.markerWire input display stdoutHash stderrHash source.policyDigest parent stage))
    ⟨source.authenticated, authentication⟩ hashLive).1
  have finalLive := (borrow_returns
    (publication_fill_borrow laws stage.directory.fd handle parent.uid stage.directory.fd
      (Publication.stagedInput input display) (source.json ++ "\n".toUTF8)
      (Publication.markerWire input display stdoutHash stderrHash source.policyDigest parent stage))
    ⟨source.filled, filling⟩ authenticatedLive).1
  have fd := congrArg Request.first source.operation
  simpa only [fd] using finalLive

def HostMarkerCall.creatingContext {before : List Program.Event} {request : Request} {observed : Option Reply}
    (source : HostMarkerCall before request observed) : List Program.Event :=
  source.invocation.packet.events ++ source.invocation.authenticated.events ++ source.invocation.run.context.events ++
    (source.source.identifying ++ source.source.selecting ++ source.source.source.displaying ++
      source.source.source.selecting).map Program.filesystemEvent

theorem marker_creation_trace {before : List Program.Event} {request : Request} {observed : Option Reply}
    (source : HostMarkerCall before request observed) :
    before = source.creatingContext ++ source.source.source.creating.map Program.filesystemEvent ++
      (source.source.source.marker.hashing ++ source.source.source.marker.authenticating ++
        source.source.source.marker.filling).map Program.filesystemEvent := by
  conv =>
    lhs
    rw [source.invocation.trace, source.invocation.run.trace, source.projection, source.source.trace,
      source.source.source.trace, source.source.source.marker.trace]
  simp only [List.map_append, completed_filesystem_events, HostMarkerCall.creatingContext, List.append_assoc]

-- §FS-host-boundary.publication: The real setter still owns its own actual opened raw stage FD.
theorem selected_publisher_marker_handle {kernel : Contract} {runtime : ActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (environment : InterferenceContract kernel)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply}
    (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (setting : request.op = .setAttribute) (named : request.left = Publication.attributeName) :
    ∃ handle, engine.references request.first = some handle ∧ handle.rawOwned = true := by
  obtain ⟨source⟩ := selected_publisher_marker journal selected action present setting named
  obtain ⟨actorHistory⟩ := actual_selected_actor_history descriptors lifetimes references environment
    journal selected action present
  have history := actorHistory.history
  rw [marker_creation_trace source] at history
  rw [List.append_assoc] at history
  obtain ⟨first, leading, rest⟩ := actor_with_split source.creatingContext _ history
  obtain ⟨created, creating, preparation⟩ := actor_with_split
    (source.source.source.creating.map Program.filesystemEvent) _ rest
  have createdPhysical := recorded_history_erase (actor_recorded_filesystem creating)
  obtain ⟨⟨handle, live, raw⟩, container⟩ := actual_fresh_handles descriptors source.source.source.parent
    ⟨source.source.source.created, createdPhysical⟩
  have preparedPhysical := recorded_history_erase (actor_recorded_filesystem preparation)
  have targetLive := prepared_marker_handle descriptors _ _ _ _ _ _ _ source.source.source.marker
    handle preparedPhysical live
  exact ⟨handle, targetLive, raw⟩

end LeanCage.Host.Kernel
