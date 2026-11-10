import FilesystemLoweredHistory
import FilesystemDirectoryObservations
import FilesystemGuardedOpens

namespace LeanCage.Host.Kernel.Lowered
open Filesystem

theorem close_identity_profile {α : Type} (fd : UInt64) (value : Result α) :
    RequestProfile (fun request => guardedCall request = Filesystem.Program.effect request) (closeResult fd value) := by
  unfold closeResult
  apply RequestProfile.call (allowed := fun request => guardedCall request = Filesystem.Program.effect request) _ _ rfl
  intro reply
  cases value with
  | error => exact .pure _
  | ok value =>
    dsimp only
    split <;> exact .pure _

theorem directory_inspect_identity (uid : Nat) (fd : UInt64) :
    (Directories.inspect uid fd).lower = Directories.inspect uid fd := by
  apply lowering_identity
  unfold Directories.inspect
  apply RequestProfile.call (allowed := fun request => guardedCall request = Filesystem.Program.effect request) _ _ rfl
  intro reply
  split
  · exact close_identity_profile _ _
  · split
    · exact .pure _
    · exact close_identity_profile _ _

-- §FS-host-boundary.ownership: The directory lease and source fstat are produced by the raw
-- guard's actual open, followed by the unchanged executable inspection helper.
theorem directory_open_recorded_owned {kernel : Contract} (laws : DescriptorContract kernel)
    (origin : FilesystemOrigin) (ordinal uid : Nat) (parent : UInt64) (name : ByteArray)
    {before after : World} {events : List (Request × Reply)} {directory : Directories.Opened}
    (run : RecordedRun kernel origin ordinal (Directories.openAt uid parent name).lower
      before events after (.ok directory)) :
    ∃ opening : RecordedOpen kernel origin
      {op := .openAt, first := parent, second := directoryFlags, left := name} directory.fd,
      ∃ observation : ObservedDirectory kernel origin (ordinal + events.length) after uid directory,
        observation.handle = opening.handle := by
  let request : Request := { op := .openAt, first := parent, second := directoryFlags, left := name }
  let next (reply : Reply) : Filesystem.Program (Result Directories.Opened) := match descriptor reply with
    | none => .pure (.error (failure "directory openat" reply))
    | some fd => Directories.inspect uid fd
  have stage : RecordedRun kernel origin ordinal ((guardedCall request).bind (fun reply => (next reply).lower))
      before events after (.ok directory) := run
  obtain ⟨opening, reply, following, openedWorld, trace, opened, remaining⟩ :=
    Kernel.recorded_run_bind_split _ _ stage
  unfold next at remaining
  split at remaining
  · cases remaining.1
  · rename_i fd recognized
    obtain ⟨actualOpen, live⟩ := guarded_open_recorded laws opened rfl recognized
    have inspected : RecordedRun kernel origin (ordinal + opening.length) (Directories.inspect uid fd)
        openedWorld following after (.ok directory) := ⟨directory_inspect_identity _ _ ▸ remaining.1, remaining.2⟩
    obtain ⟨observed⟩ := Kernel.directory_inspect_recorded laws origin (ordinal + opening.length) uid fd actualOpen.handle
      inspected live actualOpen.raw
    obtain ⟨sameFd, reply, inspectionTrace, parsed, trusted⟩ := Retrieval.directoryInspection_source _ _ inspected.1
    subst fd
    have frame := recorded_retaining_handles laws inspected.2 (by
      intro event member
      have same : event = ({op := .stat, first := directory.fd}, reply) := by simpa only [inspectionTrace, List.mem_singleton] using member
      rw [same]
      simp [RetainsDescriptors])
    have finalLive : after.handles directory.fd = some actualOpen.handle := by rw [frame]; exact live
    have same : observed.handle = actualOpen.handle := Option.some.inj (observed.live.symm.trans finalLive)
    exact ⟨actualOpen, ⟨observed.handle, observed.live, observed.raw, observed.sample,
      by simpa only [trace, List.length_append, Nat.add_assoc] using observed.earlier, observed.trusted⟩, same⟩

theorem directory_open_recorded {kernel : Contract} (laws : DescriptorContract kernel)
    (origin : FilesystemOrigin) (ordinal uid : Nat) (parent : UInt64) (name : ByteArray)
    {before after : World} {events : List (Request × Reply)} {directory : Directories.Opened}
    (run : RecordedRun kernel origin ordinal (Directories.openAt uid parent name).lower
      before events after (.ok directory)) :
    Nonempty (ObservedDirectory kernel origin (ordinal + events.length) after uid directory) := by
  obtain ⟨opening, observed, same⟩ := directory_open_recorded_owned laws origin ordinal uid parent name run
  exact ⟨observed⟩

end LeanCage.Host.Kernel.Lowered
