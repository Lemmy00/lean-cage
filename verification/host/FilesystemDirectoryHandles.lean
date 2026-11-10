import FilesystemPublicationBorrowing

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: The source observation alone reconstructs the actual open program.
theorem directory_observation_returns (uid : Nat) (parent : UInt64) (name : ByteArray)
    {events : List (Request × Reply)} {opened : Directories.Opened}
    (source : Retrieval.DirectoryOpening uid parent name events opened) :
    Returns (Directories.openAt uid parent name) events (.ok opened) := by
  obtain ⟨reply, information, rfl, recognized, parsed, trusted⟩ := source
  unfold Directories.openAt
  apply Returns.call
  rw [recognized]
  unfold Directories.inspect
  apply Returns.call
  rw [parsed]
  simp only [trusted, ↓reduceIte]
  exact .pure _

-- §FS-host-boundary.ownership: Successful source inspection retains its freshly opened raw lease.
theorem directory_observation_handle {kernel : Contract} (laws : DescriptorContract kernel)
    (uid : Nat) (parent : UInt64) (name : ByteArray)
    {before after : World} {events : List (Request × Reply)} {opened : Directories.Opened}
    (source : Retrieval.DirectoryOpening uid parent name events opened)
    (history : History kernel before events after) :
    ∃ handle, after.handles opened.fd = some handle ∧ handle.rawOwned = true := by
  obtain ⟨handle, actual, openedWorld, observing, queried, openReply, statReply,
    leading, operation, recognized, between, observed, parsed, final, live, atStat, information, trusted⟩ :=
    directory_open_handle kernel laws uid parent name ⟨directory_observation_returns uid parent name source, history⟩
  have openedLive : openedWorld.handles opened.fd = some handle := by
    rw [← random_history_handles between (by intro event impossible; cases impossible)]
    exact atStat
  exact ⟨handle, live, laws.allocated_raw _ _ _ _ _ _ operation (.inl rfl) recognized openedLive⟩

-- §FS-host-boundary.ownership: An acknowledged raw FD remains genuine when its path changes.
theorem created_observation_handle {kernel : Contract} (laws : DescriptorContract kernel)
    (uid : Nat) (parent : UInt64) (prefixName : String)
    {before after : World} {events : List (Request × Reply)} {child : Directories.NewDirectory}
    (source : Publication.CreatedObservation uid parent prefixName events child)
    (history : History kernel before events after) :
    ∃ handle, after.handles child.directory.fd = some handle ∧ handle.rawOwned = true := by
  obtain ⟨random, randomEvents, made, opening, shape, randomized, sized, name, component,
    madeZero, madeEmpty, opened, owner, mode⟩ := source
  rw [shape] at history
  obtain ⟨first, initial, final⟩ := history_split (randomEvents ++ [(_, made)]) opening history
  exact directory_observation_handle laws uid parent child.name opened final

theorem actual_child_handle {kernel : Contract} (laws : DescriptorContract kernel)
    (uid : Nat) (parent : UInt64) (prefixName : String)
    {before after : World} {events : List (Request × Reply)} {child : Directories.NewDirectory}
    (run : ConcurrentRun kernel (Directories.newChild uid parent prefixName) before events after (.ok child)) :
    ∃ handle, after.handles child.directory.fd = some handle ∧ handle.rawOwned = true :=
  created_observation_handle laws uid parent prefixName (Publication.newChild_source uid parent prefixName run.1) run.2

-- §FS-host-boundary.publication: Both actual stage resources come from the same successful setup.
theorem actual_fresh_handles {kernel : Contract} (laws : DescriptorContract kernel)
    (parent : Directories.Parent) {before after : World} {events : List (Request × Reply)} {stage : Directories.Fresh}
    (run : ConcurrentRun kernel (Directories.fresh parent) before events after (.ok stage)) :
    (∃ handle, after.handles stage.directory.fd = some handle ∧ handle.rawOwned = true) ∧
    (∃ handle, after.handles stage.container.fd = some handle ∧ handle.rawOwned = true) := by
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
      have full : events = opening ++ creating := by
        simpa only [childShape, List.append_nil] using shape
      have history := run.2
      rw [full] at history
      obtain ⟨middle, first, last⟩ := history_split opening creating history
      obtain ⟨containerHandle, containerLive, containerRaw⟩ := directory_observation_handle laws
        parent.uid parent.directory.fd ".".toUTF8 (Retrieval.directoryOpening_source _ _ _ opened) first
      have childRun : ConcurrentRun kernel (Directories.newChild parent.uid container.fd PrivateNames.prefixText)
          middle creating after (.ok child) := ⟨created, last⟩
      have childLive := actual_child_handle laws _ _ _ childRun
      have kept := (borrow_returns (directoryChild_borrow laws container.fd containerHandle _ _ _) childRun containerLive).1
      exact ⟨childLive, containerHandle, kept, containerRaw⟩

end LeanCage.Host.Kernel
