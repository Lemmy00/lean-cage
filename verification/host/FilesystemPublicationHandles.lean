import FilesystemParentHandles

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: A dot-open is a new FD referring to the retained actual directory.
theorem directory_open_alias {kernel : Contract} (laws : DescriptorContract kernel)
    (namespaceLaws : NamespaceContract kernel) (uid : Nat) (parent : UInt64) (parentHandle : Handle)
    {before after : World} {events : List (Request × Reply)} {opened : Directories.Opened}
    (run : ConcurrentRun kernel (Directories.openAt uid parent ".".toUTF8) before events after (.ok opened))
    (live : before.handles parent = some parentHandle) :
    ∃ handle, after.handles opened.fd = some handle ∧ handle.object = parentHandle.object ∧ handle.rawOwned = true := by
  obtain ⟨handle, actual, openedWorld, observing, queried, reply, statReply,
    leading, operation, recognized, between, observed, parsed, final, afterLive, atStat, information, trusted⟩ :=
    directory_open_handle kernel laws uid parent ".".toUTF8 run
  have parentLive : actual.handles parent = some parentHandle := by
    rw [random_history_handles leading (by intro event impossible; cases impossible)]
    exact live
  obtain ⟨aliasHandle, aliasLive, sameObject⟩ := namespaceLaws.open_dot _ _ _ _ _ _ operation
    rfl rfl parentLive rfl recognized
  have openedLive : openedWorld.handles opened.fd = some handle := by
    rw [← random_history_handles between (by intro event impossible; cases impossible)]
    exact atStat
  have same := Option.some.inj (aliasLive.symm.trans openedLive)
  subst aliasHandle
  exact ⟨handle, afterLive, sameObject, laws.allocated_raw _ _ _ _ _ _ operation (.inl rfl) recognized openedLive⟩

-- §FS-host-boundary.publication: The fresh stage retains its actual public-parent alias.
theorem fresh_container_alias {kernel : Contract} (laws : DescriptorContract kernel)
    (namespaceLaws : NamespaceContract kernel) (parent : Directories.Parent) (parentHandle : Handle)
    {before after : World} {events : List (Request × Reply)} {stage : Directories.Fresh}
    (run : ConcurrentRun kernel (Directories.fresh parent) before events after (.ok stage))
    (live : before.handles parent.directory.fd = some parentHandle) :
    ∃ handle, after.handles stage.container.fd = some handle ∧ handle.object = parentHandle.object ∧
      handle.rawOwned = true := by
  have source := run.1
  unfold Directories.fresh at source
  obtain ⟨opening, container, later, opened, following, shape⟩ := Snapshot.returns_bind_split _ _ source
  cases container with
  | error error => cases following
  | ok container =>
    obtain ⟨creating, result, last, created, final, childShape⟩ := Snapshot.returns_bind_split _ _ following
    cases result with
    | error error => have impossible := (Snapshot.closeResult_provenance _ _ final).1; cases impossible
    | ok child =>
      obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq final
      cases same
      have full : events = opening ++ creating := by simpa only [childShape, List.append_nil] using shape
      have history := run.2
      rw [full] at history
      obtain ⟨middle, first, last⟩ := history_split opening creating history
      obtain ⟨handle, openedLive, sameObject, raw⟩ := directory_open_alias laws namespaceLaws _ _ _ ⟨opened, first⟩ live
      have kept := (borrow_returns (directoryChild_borrow laws container.fd handle _ _ _)
        ⟨created, last⟩ openedLive).1
      exact ⟨handle, kept, sameObject, raw⟩

def HostCommitCall.selectingContext {before : List Program.Event} {request : Request} {observed : Option Reply}
    (source : HostCommitCall before request observed) : List Program.Event :=
  source.invocation.packet.events ++ source.invocation.authenticated.events ++ source.invocation.run.context.events ++
    (source.source.identifying ++ source.source.selecting ++ source.source.commit.displaying).map Program.filesystemEvent

theorem commit_parent_trace {before : List Program.Event} {request : Request} {observed : Option Reply}
    (source : HostCommitCall before request observed) :
    before = source.selectingContext ++ source.source.commit.selecting.map Program.filesystemEvent ++
      (source.source.commit.creating ++ source.source.commit.preparing).map Program.filesystemEvent := by
  conv =>
    lhs
    rw [source.invocation.trace, source.invocation.run.trace, source.projection, source.source.trace,
      source.source.commit.trace]
  simp only [List.map_append, completed_filesystem_events, HostCommitCall.selectingContext, List.append_assoc]

-- §FS-host-boundary.publication: Real commit operands keep their actual source-selected handles.
structure CommitHandles {kernel : Contract} (runtime : ActorRuntime kernel) (ticks : List (ActorTick runtime))
    (actor : ActorId) (engine : EngineState) (request : Request) (observed : Option Reply) where
  source : HostCommitCall engine.events request observed
  parent : Handle
  container : Handle
  stage : Handle
  parentLive : engine.references source.source.commit.parent.directory.fd = some parent
  containerLive : engine.references source.source.commit.stage.container.fd = some container
  stageLive : engine.references source.source.commit.stage.directory.fd = some stage
  parentRaw : parent.rawOwned = true
  containerRaw : container.rawOwned = true
  stageRaw : stage.rawOwned = true
  sameParent : container.object = parent.object

-- §FS-host-boundary.acceptance: All acknowledgements/losses use these same three real resources.
theorem selected_commit_handles {kernel : Contract} {runtime : ActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (namespaceLaws : NamespaceContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (environment : InterferenceContract kernel)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply}
    (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) (rename : request.op = .renameNew) :
    Nonempty (CommitHandles runtime ticks actor engine request observed) := by
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
    (source.source.commit.preparing.map Program.filesystemEvent) (by
      simpa only [List.map_append] using rest)
  have selectedRun := recorded_history_erase (actor_recorded_filesystem selecting)
  have createdRun := recorded_history_erase (actor_recorded_filesystem creating)
  have preparedRun := recorded_history_erase (actor_recorded_filesystem preparing)
  obtain ⟨parent, parentLive, parentRaw⟩ := parent_handle descriptors source.source.target true
    ⟨source.source.commit.selected, selectedRun⟩
  have freshRun : ConcurrentRun kernel (Directories.fresh source.source.commit.parent)
      selectedAfter source.source.commit.creating createdAfter (.ok source.source.commit.stage) :=
    ⟨source.source.commit.created, createdRun⟩
  obtain ⟨container, containerLive, sameParent, containerRaw⟩ := fresh_container_alias descriptors namespaceLaws
    _ parent freshRun parentLive
  obtain ⟨⟨stage, stageLive, stageRaw⟩, _⟩ := actual_fresh_handles descriptors _ freshRun
  have parentAfter := (actual_fresh_retains_parent descriptors _ parent freshRun parentLive).1
  have retained : ∀ held handle, createdAfter.handles held = some handle →
      (tick.before.project engine).handles held = some handle := by
    intro held handle live
    exact (borrow_returns (publication_prepare_borrow descriptors held handle _ _ _ _ _ _ _)
      ⟨source.source.commit.prepared, preparedRun⟩ live).1
  exact ⟨⟨source, parent, container, stage, retained _ _ parentAfter, retained _ _ containerLive,
    retained _ _ stageLive, parentRaw, containerRaw, stageRaw, sameParent⟩⟩

end LeanCage.Host.Kernel
