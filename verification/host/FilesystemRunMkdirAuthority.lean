import FilesystemMkdirOrigins
import FilesystemObservedAuthority

namespace LeanCage.Host.Kernel
open Filesystem

structure RunMkdirAuthority {kernel : Contract} (runtime : ActorRuntime kernel)
    (engine : EngineState) (world : World) (request : Request) (observed : Option Reply) (hostUid : Nat) where
  invocation : RunCreationPrefix engine.events request observed
  source : RunChildCall invocation.inside request
  parent : Handle
  live : engine.references request.first = some parent
  raw : parent.rawOwned = true
  information : Stat
  current : world.information parent.object = some information
  trusted : Directories.trusted hostUid information = true
  uid : source.uid = hostUid
  component : Directories.component request.left = true
  reserved : PrivateNames.reservedBytes request.left = true
  mode : request.second = 448

-- §FS-host-boundary.ownership: A run/validator mkdir uses its actual checked /tmp parent.
theorem run_creation_mkdir_authority {kernel : Contract} {runtime : ActorRuntime kernel}
    {process : ProcessContract runtime} {primitive : ChildPrimitive kernel} {hostUid : Nat}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (environment : InterferenceContract kernel)
    (raw : RawReferenceLifetimeContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (accounts : AccountContract kernel hostUid) (metadata : GlobalAuthorityContract runtime primitive)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    (backend : BackendAuthorityProducer process primitive ticks) {afterProcesses : Processes}
    (recording : ExternalJournal process primitive hostUid Processes.empty ticks afterProcesses)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply} (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) (mkdir : request.op = .mkdirAt)
    (invocation : RunCreationPrefix engine.events request observed) :
    Nonempty (RunMkdirAuthority runtime engine tick.before.shared request observed hostUid) := by
  obtain ⟨source⟩ := actual_run_child_call invocation.active mkdir
  have trace : engine.events = invocation.context ++ source.selecting.map Program.filesystemEvent ++
      source.child.randomEvents.map Program.filesystemEvent := by
    conv => lhs; rw [invocation.trace, source.trace, source.child.trace]
    simp only [List.map_append, completed_filesystem_events, List.append_assoc]
  obtain ⟨actorHistory⟩ := actual_selected_actor_history descriptors lifetimes references environment
    journal selected action present
  have history := actorHistory.history
  rw [trace, List.append_assoc] at history
  obtain ⟨selectingBefore, leading, rest⟩ := actor_with_split invocation.context _ history
  obtain ⟨selectedWorld, selecting, randomizing⟩ := actor_with_split
    (source.selecting.map Program.filesystemEvent) (source.child.randomEvents.map Program.filesystemEvent) rest
  obtain ⟨parent, identity, identityEarlier⟩ := temporary_parent_recorded descriptors _ invocation.context.length
    ⟨source.selected, by simpa only [Nat.zero_add] using actor_recorded_filesystem selecting⟩
  have now : engine.references source.container.fd = some parent.handle := by
    have kept := (borrow_returns (directoryRandom_borrow descriptors source.container.fd parent.handle _ _ _)
      ⟨source.child.randomness, recorded_history_erase (actor_recorded_filesystem randomizing)⟩ parent.live).1
    exact kept
  have bound : invocation.context.length + source.selecting.length ≤ engine.events.length := by
    have count := congrArg List.length trace
    simp only [List.length_append, List.length_map] at count
    omega
  obtain ⟨information, known, same, trusted⟩ := observed_directory_current_authority descriptors lifetimes references
    raw sdk accounts metadata journal backend recording selected present parent identity now bound
  have fd : request.first = source.container.fd := congrArg Request.first source.child.operation
  have name : request.left = (PrivateNames.prefixText ++ Snapshot.hex source.child.random).toUTF8 :=
    congrArg Request.left source.child.operation
  refine ⟨⟨invocation, source, parent.handle, ?_, parent.raw, information, known, trusted,
    sampled_uid_is_host accounts identity, ?_, ?_, congrArg Request.second source.child.operation⟩⟩
  · rw [fd]
    exact now
  · rw [name]
    exact source.child.component
  · rw [name]
    exact private_prefix_reserved _

end LeanCage.Host.Kernel
