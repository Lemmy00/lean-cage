import FilesystemDirectoryAliases
import FilesystemLoweredParentObservations
import FilesystemLoweredPublicationBorrowing

namespace LeanCage.Host.Kernel.Lowered
open Filesystem

-- §FS-host-boundary.publication: The container is an actual new descriptor alias of the
-- source-retained parent, including all raw pre/post-open probes and the real fstat.
theorem directory_open_alias_recorded {kernel : Contract} (laws : DescriptorContract kernel)
    (aliases : DirectoryAliasContract kernel)
    (origin : FilesystemOrigin) (ordinal uid : Nat) (parent : UInt64) (parentHandle : Handle)
    {before after : World} {events : List (Request × Reply)} {directory : Directories.Opened}
    (run : RecordedRun kernel origin ordinal (Directories.openAt uid parent ".".toUTF8).lower
      before events after (.ok directory)) (parentLive : before.handles parent = some parentHandle) :
    ∃ observation : ObservedDirectory kernel origin (ordinal + events.length) after uid directory,
      observation.handle.object = parentHandle.object := by
  let request : Request := {op := .openAt, first := parent, second := directoryFlags, left := ".".toUTF8}
  let next (reply : Reply) : Filesystem.Program (Result Directories.Opened) := match descriptor reply with
    | none => .pure (.error (failure "directory openat" reply))
    | some fd => Directories.inspect uid fd
  have stage : RecordedRun kernel origin ordinal ((guardedCall request).bind (fun reply => (next reply).lower))
      before events after (.ok directory) := run
  obtain ⟨opening, reply, following, openedWorld, trace, opened, remaining⟩ := Kernel.recorded_run_bind_split _ _ stage
  unfold next at remaining
  split at remaining
  · cases remaining.1
  · rename_i fd recognized
    obtain ⟨actualOpen, live, parentAtOpen⟩ := guarded_open_recorded_retained laws opened rfl recognized parentLive
    obtain ⟨aliasHandle, aliasLive, sameObject⟩ := aliases.dot _ _ _ _ _ _ actualOpen.actual rfl rfl
      parentAtOpen rfl actualOpen.recognized
    have aliasSame := Option.some.inj (aliasLive.symm.trans actualOpen.live)
    subst aliasHandle
    have inspected : RecordedRun kernel origin (ordinal + opening.length) (Directories.inspect uid fd)
        openedWorld following after (.ok directory) := ⟨directory_inspect_identity _ _ ▸ remaining.1, remaining.2⟩
    obtain ⟨observed⟩ := Kernel.directory_inspect_recorded laws origin (ordinal + opening.length) uid fd actualOpen.handle
      inspected live actualOpen.raw
    have finalLive : after.handles directory.fd = some actualOpen.handle := by
      obtain ⟨sameFd, reply, inspectionTrace, parsed, trusted⟩ := Retrieval.directoryInspection_source _ _ inspected.1
      rw [sameFd]
      rw [recorded_retaining_handles laws inspected.2 (by
        intro event member
        have same : event = ({op := .stat, first := fd}, reply) := by simpa only [inspectionTrace, List.mem_singleton] using member
        rw [same]
        simp [RetainsDescriptors])]
      exact live
    have same := Option.some.inj (observed.live.symm.trans finalLive)
    exact ⟨⟨observed.handle, observed.live, observed.raw, observed.sample,
      by simpa only [trace, List.length_append, Nat.add_assoc] using observed.earlier, observed.trusted⟩,
      (congrArg Handle.object same).trans sameObject⟩

theorem directory_child_recorded {kernel : Contract} (laws : DescriptorContract kernel)
    (origin : FilesystemOrigin) (ordinal uid : Nat) (parent : UInt64) (prefixName : String)
    {before after : World} {events : List (Request × Reply)} {child : Directories.NewDirectory}
    (run : RecordedRun kernel origin ordinal (Directories.newChild uid parent prefixName).lower
      before events after (.ok child)) :
    Nonempty (ObservedDirectory kernel origin (ordinal + events.length) after uid child.directory) := by
  have source := run
  unfold Directories.newChild at source
  obtain ⟨randomEvents, result, rest, randomWorld, trace, randomized, afterRandom⟩ := recorded_run_bind_split _ _ source
  cases result with
  | error error => cases afterRandom.1
  | ok bytes =>
    dsimp only at afterRandom
    split at afterRandom
    · cases afterRandom.1
    · let name := (prefixName ++ Snapshot.hex bytes).toUTF8
      let request : Request := {op := .mkdirAt, first := parent, second := 448, left := name}
      let next (made : Reply) : Filesystem.Program (Result Directories.NewDirectory) := do
        if made.1 != 0 || !made.2.isEmpty then return .error (failure "fresh stage mkdirat" made)
        let opened ← Directories.openAt uid parent name
        match opened with
        | .error error => return .error error
        | .ok directory =>
          if directory.information.uid != uid || (directory.information.mode &&& 511) != 448 then
            closeResult directory.fd (.error "fresh stage authority differs")
          else return .ok ⟨directory, name⟩
      have stage : RecordedRun kernel origin (ordinal + randomEvents.length)
          ((guardedCall request).bind (fun reply => (next reply).lower))
          randomWorld rest after (.ok child) := afterRandom
      obtain ⟨making, made, following, createdWorld, makeTrace, madeRun, afterMade⟩ := Kernel.recorded_run_bind_split _ _ stage
      unfold next at afterMade
      split at afterMade
      · cases afterMade.1
      · obtain ⟨opening, opened, finishing, openedWorld, openTrace, openedRun, final⟩ := recorded_run_bind_split _ _ afterMade
        cases opened with
        | error error => cases final.1
        | ok directory =>
          dsimp only at final
          split at final
          · obtain ⟨logical, rejected⟩ := returns_source _ final.1
            have impossible := (Snapshot.closeResult_provenance _ _ rejected).1
            cases impossible
          · obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq final.1
            cases same
            obtain ⟨observed⟩ := directory_open_recorded laws origin _ uid parent name openedRun
            have live : after.handles directory.fd = some observed.handle := by
              rw [empty_recorded_handles final.2]
              exact observed.live
            exact ⟨observed.advance live (by
              simp only [trace, makeTrace, openTrace, List.length_append]
              omega)⟩

structure ObservedFresh (kernel : Contract) (origin : FilesystemOrigin) (limit : Nat)
    (world : World) (parent : Directories.Parent) (stage : Directories.Fresh) (parentHandle : Handle) where
  directory : ObservedDirectory kernel origin limit world parent.uid stage.directory
  container : ObservedDirectory kernel origin limit world parent.uid stage.container
  parentLive : world.handles parent.directory.fd = some parentHandle
  sameParent : container.handle.object = parentHandle.object
  distinct : stage.directory.fd ≠ parent.directory.fd ∧ stage.container.fd ≠ parent.directory.fd ∧
    stage.directory.fd ≠ stage.container.fd

-- §FS-host-boundary.publication: The actual fresh helper produces all three live resources;
-- the later custody fold connects its child handle to the same recorded mkdir birth.
theorem fresh_recorded {kernel : Contract} (laws : DescriptorContract kernel)
    (aliases : DirectoryAliasContract kernel) (origin : FilesystemOrigin) (ordinal : Nat)
    (parent : Directories.Parent) (parentHandle : Handle)
    {before after : World} {events : List (Request × Reply)} {stage : Directories.Fresh}
    (run : RecordedRun kernel origin ordinal (Directories.fresh parent).lower before events after (.ok stage))
    (parentLive : before.handles parent.directory.fd = some parentHandle) :
    Nonempty (ObservedFresh kernel origin (ordinal + events.length) after parent stage parentHandle) := by
  have source := run
  unfold Directories.fresh at source
  obtain ⟨opening, result, rest, openedWorld, trace, opened, afterOpen⟩ := recorded_run_bind_split _ _ source
  cases result with
  | error error => cases afterOpen.1
  | ok container =>
    obtain ⟨creating, result, last, createdWorld, createTrace, created, final⟩ := recorded_run_bind_split _ _ afterOpen
    cases result with
    | error error =>
      obtain ⟨logical, rejected⟩ := returns_source _ final.1
      have impossible := (Snapshot.closeResult_provenance _ _ rejected).1
      cases impossible
    | ok child =>
      obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq final.1
      cases same
      obtain ⟨observedContainer, aliasObject⟩ := directory_open_alias_recorded laws aliases origin ordinal parent.uid
        parent.directory.fd parentHandle opened parentLive
      obtain ⟨observedChild⟩ := directory_child_recorded laws origin (ordinal + opening.length) parent.uid
        container.fd PrivateNames.prefixText created
      have containerKept := history_borrow container.fd observedContainer.handle
        (directoryChild_borrow laws container.fd observedContainer.handle _ _ _) created observedContainer.live
      have originalKept := history_borrow parent.directory.fd parentHandle
        (directoryFresh_borrow laws parent.directory.fd parentHandle parent) run parentLive
      have childLive : after.handles child.directory.fd = some observedChild.handle := by
        rw [empty_recorded_handles final.2]
        exact observedChild.live
      have containerLive : after.handles container.fd = some observedContainer.handle := by
        rw [empty_recorded_handles final.2]
        exact containerKept.1
      refine ⟨⟨observedChild.advance childLive ?_, observedContainer.advance containerLive ?_, originalKept.1,
        aliasObject, originalKept.2.1, originalKept.2.2, containerKept.2⟩⟩
      · simp only [trace, createTrace, List.length_append]; omega
      · simp only [trace, createTrace, List.length_append]; omega

end LeanCage.Host.Kernel.Lowered
