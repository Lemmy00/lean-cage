import FilesystemPrivateDirectoryOpens
import FilesystemPublicTraversal
import PublicationProofs.Frontier

namespace LeanCage.Host.Kernel.Lowered
open Filesystem

-- §FS-host-boundary.ownership: The child's current scope follows its actual raw
-- open and retained parent. Probe failures and inspection rejection remain real
-- paths; only an acknowledged successful source result provides this child.
theorem directory_open_private {kernel : Contract} (laws : DescriptorContract kernel)
    {origin : FilesystemOrigin} {family : Family} (opens : PrivateDirectoryOpens kernel origin family)
    (ordinal uid : Nat) (parent : UInt64) (name : ByteArray) (parentHandle : Handle) (scope : ObjectId)
    {before after : World} {events : List (Request × Reply)} {directory : Directories.Opened}
    (run : RecordedRun kernel origin ordinal (Directories.openAt uid parent name).lower
      before events after (.ok directory)) (parentLive : before.handles parent = some parentHandle)
    (privateParent : family parentHandle.object = some scope) (component : Directories.component name = true)
    (notDot : name ≠ ".".toUTF8) (notUp : name ≠ "..".toUTF8) :
    ∃ observation : ObservedDirectory kernel origin (ordinal + events.length) after uid directory,
      family observation.handle.object = some scope := by
  let request : Request := {op := .openAt, first := parent, second := directoryFlags, left := name}
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
    have privateObject := opens actualOpen.ordinal actualOpen.before actualOpen.after request actualOpen.reply parentHandle
      fd actualOpen.handle scope actualOpen.sampled actualOpen.actual rfl rfl parentAtOpen actualOpen.recognized actualOpen.live
      component notDot notUp privateParent
    have inspected : RecordedRun kernel origin (ordinal + opening.length) (Directories.inspect uid fd)
        openedWorld following after (.ok directory) := ⟨directory_inspect_identity _ _ ▸ remaining.1, remaining.2⟩
    obtain ⟨observed⟩ := Kernel.directory_inspect_recorded laws origin (ordinal + opening.length) uid fd actualOpen.handle
      inspected live actualOpen.raw
    obtain ⟨sameFd, reply, inspectionTrace, parsed, trusted⟩ := Retrieval.directoryInspection_source _ _ inspected.1
    subst fd
    have frame := recorded_retaining_handles laws inspected.2 (by
      intro event member
      have same : event = ({op := .stat, first := directory.fd}, reply) := by
        simpa only [inspectionTrace, List.mem_singleton] using member
      rw [same]
      simp [RetainsDescriptors])
    have finalLive : after.handles directory.fd = some actualOpen.handle := by rw [frame]; exact live
    have same : observed.handle = actualOpen.handle := Option.some.inj (observed.live.symm.trans finalLive)
    refine ⟨⟨observed.handle, observed.live, observed.raw, observed.sample, ?_, observed.trusted⟩, ?_⟩
    · simpa only [trace, List.length_append, Nat.add_assoc] using observed.earlier
    · simpa only [same] using privateObject

theorem directory_ensure_private {kernel : Contract} (laws : DescriptorContract kernel)
    {origin : FilesystemOrigin} {family : Family} (opens : PrivateDirectoryOpens kernel origin family)
    (ordinal uid : Nat) (parent : UInt64) (name : ByteArray) (parentHandle : Handle) (scope : ObjectId)
    {before after : World} {events : List (Request × Reply)} {directory : Directories.Opened}
    (run : RecordedRun kernel origin ordinal (Directories.ensureAt uid parent name).lower
      before events after (.ok directory)) (parentLive : before.handles parent = some parentHandle)
    (privateParent : family parentHandle.object = some scope) (component : Directories.component name = true)
    (notDot : name ≠ ".".toUTF8) (notUp : name ≠ "..".toUTF8) :
    ∃ observation : ObservedDirectory kernel origin (ordinal + events.length) after uid directory,
      family observation.handle.object = some scope := by
  let request : Request := {op := .mkdirAt, first := parent, second := 448, left := name}
  let next (made : Reply) : Filesystem.Program (Result Directories.Opened) :=
    if made.1 == 0 && made.2.isEmpty then Directories.openAt uid parent name
    else if nativeError made && errorNumber made == 17 then Directories.openAt uid parent name
    else pure (.error (failure "parent mkdirat" made))
  have stage : RecordedRun kernel origin ordinal ((guardedCall request).bind (fun reply => (next reply).lower))
      before events after (.ok directory) := run
  obtain ⟨making, reply, opening, middle, trace, made, remaining⟩ := Kernel.recorded_run_bind_split _ _ stage
  have stillLive := (borrow_returns (guarded_passive_borrow laws parent parentHandle request (by simp [RetainsDescriptors]))
    ⟨made.1, recorded_history_erase made.2⟩ parentLive).1
  unfold next at remaining
  split at remaining
  · obtain ⟨observed, privateObject⟩ := directory_open_private laws opens (ordinal + making.length) uid parent name
      parentHandle scope remaining stillLive privateParent component notDot notUp
    exact ⟨observed.advance observed.live (by simp only [trace, List.length_append]; omega), privateObject⟩
  · split at remaining
    · obtain ⟨observed, privateObject⟩ := directory_open_private laws opens (ordinal + making.length) uid parent name
        parentHandle scope remaining stillLive privateParent component notDot notUp
      exact ⟨observed.advance observed.live (by simp only [trace, List.length_append]; omega), privateObject⟩
    · cases remaining.1

end LeanCage.Host.Kernel.Lowered
