import FilesystemLoweredAliases

namespace LeanCage.Host.Kernel.Lowered
open Filesystem

-- §FS-host-boundary.ownership: Keep the actual successful child open alongside its
-- fstat/lease. The later custody join must use this same raw source occurrence and handle.
theorem directory_child_recorded_owned {kernel : Contract} (laws : DescriptorContract kernel)
    (origin : FilesystemOrigin) (ordinal uid : Nat) (parent : UInt64) (prefixName : String)
    {before after : World} {events : List (Request × Reply)} {child : Directories.NewDirectory}
    (run : RecordedRun kernel origin ordinal (Directories.newChild uid parent prefixName).lower
      before events after (.ok child)) :
    ∃ opening : RecordedOpen kernel origin
      {op := .openAt, first := parent, second := directoryFlags, left := child.name} child.directory.fd,
      ∃ observation : ObservedDirectory kernel origin (ordinal + events.length) after uid child.directory,
        observation.handle = opening.handle := by
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
      · obtain ⟨openingEvents, opened, finishing, openedWorld, openTrace, openedRun, final⟩ := recorded_run_bind_split _ _ afterMade
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
            obtain ⟨actualOpen, observed, sameHandle⟩ := directory_open_recorded_owned laws origin _ uid parent name openedRun
            have live : after.handles directory.fd = some observed.handle := by
              rw [empty_recorded_handles final.2]
              exact observed.live
            exact ⟨actualOpen, observed.advance live (by
              simp only [trace, makeTrace, openTrace, List.length_append]
              omega), sameHandle⟩

end LeanCage.Host.Kernel.Lowered
