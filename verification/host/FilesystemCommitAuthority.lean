import FilesystemPublicationHandles
import FilesystemObservedAuthority

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.publication: Current authority is derived for the actual selected rename.
structure CommitAuthority {kernel : Contract} (runtime : ActorRuntime kernel) (ticks : List (ActorTick runtime))
    (actor : ActorId) (engine : EngineState) (world : World) (request : Request) (observed : Option Reply)
    (hostUid : Nat) where
  handles : CommitHandles runtime ticks actor engine request observed
  information : Stat
  current : world.information handles.parent.object = some information
  trusted : Directories.trusted hostUid information = true
  uid : handles.source.source.commit.parent.uid = hostUid

-- §FS-host-boundary.acceptance: Error and lost rename acknowledgements use the same source cut.
theorem selected_commit_authority {kernel : Contract} {runtime : ActorRuntime kernel}
    {process : ProcessContract runtime} {primitive : ChildPrimitive kernel} {hostUid : Nat}
    (descriptors : DescriptorContract kernel) (namespaceLaws : NamespaceContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (environment : InterferenceContract kernel) (raw : RawReferenceLifetimeContract kernel)
    (sdk : RuntimeDescriptorContract runtime) (accounts : AccountContract kernel hostUid)
    (metadata : GlobalAuthorityContract runtime primitive)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    (backend : BackendAuthorityProducer process primitive ticks) {afterProcesses : Processes}
    (recording : ExternalJournal process primitive hostUid Processes.empty ticks afterProcesses)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply}
    (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) (rename : request.op = .renameNew) :
    Nonempty (CommitAuthority runtime ticks actor engine tick.before.shared request observed hostUid) := by
  obtain ⟨source⟩ := selected_publisher_commit journal selected action present rename
  obtain ⟨actorHistory⟩ := actual_selected_actor_history descriptors lifetimes references environment
    journal selected action present
  have history := actorHistory.history
  rw [commit_parent_trace source, List.append_assoc] at history
  obtain ⟨selectedBefore, leading, rest⟩ := actor_with_split source.selectingContext _ history
  obtain ⟨selectedAfter, selecting, rest⟩ := actor_with_split
    (source.source.commit.selecting.map Program.filesystemEvent) _ rest
  obtain ⟨createdAfter, creating, preparing⟩ := actor_with_split
    (source.source.commit.creating.map Program.filesystemEvent)
    (source.source.commit.preparing.map Program.filesystemEvent)
    (by simpa only [List.map_append] using rest)
  have selectedRun := actor_recorded_filesystem selecting
  obtain ⟨parent⟩ := parent_recorded descriptors _ source.selectingContext.length source.source.target true
    ⟨source.source.commit.selected, by simpa only [Nat.zero_add] using selectedRun⟩
  have createdRun := recorded_history_erase (actor_recorded_filesystem creating)
  have preparedRun := recorded_history_erase (actor_recorded_filesystem preparing)
  have freshRun : ConcurrentRun kernel (Directories.fresh source.source.commit.parent)
      selectedAfter source.source.commit.creating createdAfter (.ok source.source.commit.stage) :=
    ⟨source.source.commit.created, createdRun⟩
  obtain ⟨container, containerLive, sameParent, containerRaw⟩ := fresh_container_alias descriptors namespaceLaws
    _ parent.directory.handle freshRun parent.directory.live
  obtain ⟨⟨stage, stageLive, stageRaw⟩, _⟩ := actual_fresh_handles descriptors _ freshRun
  have parentAfter := (actual_fresh_retains_parent descriptors _ parent.directory.handle
    freshRun parent.directory.live).1
  have retained : ∀ held handle, createdAfter.handles held = some handle →
      (tick.before.project engine).handles held = some handle := by
    intro held handle live
    exact (borrow_returns (publication_prepare_borrow descriptors held handle _ _ _ _ _ _ _)
      ⟨source.source.commit.prepared, preparedRun⟩ live).1
  let handles : CommitHandles runtime ticks actor engine request observed :=
    ⟨source, parent.directory.handle, container, stage, retained _ _ parentAfter, retained _ _ containerLive,
      retained _ _ stageLive, parent.directory.raw, containerRaw, stageRaw, sameParent⟩
  have bound : source.selectingContext.length + source.source.commit.selecting.length ≤ engine.events.length := by
    have count := congrArg List.length (commit_parent_trace source)
    simp only [List.length_append, List.length_map] at count
    omega
  obtain ⟨information, known, same, trusted⟩ := observed_directory_current_authority descriptors lifetimes
    references raw sdk accounts metadata journal backend recording selected present parent.directory parent.identity
    handles.parentLive bound
  exact ⟨⟨handles, information, known, trusted, sampled_uid_is_host accounts parent.identity⟩⟩

end LeanCage.Host.Kernel
