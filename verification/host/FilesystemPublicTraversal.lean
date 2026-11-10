import FilesystemHistoricalLookup
import FilesystemLoweredPublicStart

namespace LeanCage.Host.Kernel.Lowered
open Filesystem

-- §FS-host-boundary.ownership: This open uses the same retained public parent at the actual
-- raw lookup. Its final observed handle is the one returned by that operation.
theorem directory_open_public {kernel : Contract} (laws : DescriptorContract kernel)
    {origin : FilesystemOrigin} {family : Family} (opens : PublicDirectoryOpens kernel origin family)
    (ordinal uid : Nat) (parent : UInt64) (name : ByteArray) (parentHandle : Handle)
    {before after : World} {events : List (Request × Reply)} {directory : Directories.Opened}
    (run : RecordedRun kernel origin ordinal (Directories.openAt uid parent name).lower
      before events after (.ok directory)) (parentLive : before.handles parent = some parentHandle)
    (publicParent : family parentHandle.object = none) (component : Directories.component name = true)
    (publicName : PrivateNames.reservedBytes name = false) :
    ∃ observation : ObservedDirectory kernel origin (ordinal + events.length) after uid directory,
      family observation.handle.object = none := by
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
    have publicObject := opens actualOpen.ordinal actualOpen.before actualOpen.after request actualOpen.reply parentHandle
      fd actualOpen.handle actualOpen.sampled actualOpen.actual rfl rfl parentAtOpen actualOpen.recognized actualOpen.live
      component publicName publicParent
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
    · simpa only [same] using publicObject

theorem directory_ensure_public {kernel : Contract} (laws : DescriptorContract kernel)
    {origin : FilesystemOrigin} {family : Family} (opens : PublicDirectoryOpens kernel origin family)
    (ordinal uid : Nat) (parent : UInt64) (name : ByteArray) (parentHandle : Handle)
    {before after : World} {events : List (Request × Reply)} {directory : Directories.Opened}
    (run : RecordedRun kernel origin ordinal (Directories.ensureAt uid parent name).lower
      before events after (.ok directory)) (parentLive : before.handles parent = some parentHandle)
    (publicParent : family parentHandle.object = none) (component : Directories.component name = true)
    (publicName : PrivateNames.reservedBytes name = false) :
    ∃ observation : ObservedDirectory kernel origin (ordinal + events.length) after uid directory,
      family observation.handle.object = none := by
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
  · obtain ⟨observed, publicObject⟩ := directory_open_public laws opens (ordinal + making.length) uid parent name parentHandle
      remaining stillLive publicParent component publicName
    exact ⟨observed.advance observed.live (by simp only [trace, List.length_append]; omega), publicObject⟩
  · split at remaining
    · obtain ⟨observed, publicObject⟩ := directory_open_public laws opens (ordinal + making.length) uid parent name parentHandle
        remaining stillLive publicParent component publicName
      exact ⟨observed.advance observed.live (by simp only [trace, List.length_append]; omega), publicObject⟩
    · cases remaining.1

theorem directory_public_public {kernel : Contract} (laws : DescriptorContract kernel)
    {origin : FilesystemOrigin} {family : Family} (opens : PublicDirectoryOpens kernel origin family)
    (ordinal uid : Nat) (parent : UInt64) (name : ByteArray) (create : Bool) (parentHandle : Handle)
    {before after : World} {events : List (Request × Reply)} {directory : Directories.Opened}
    (run : RecordedRun kernel origin ordinal (Directories.publicAt uid parent name create).lower
      before events after (.ok directory)) (parentLive : before.handles parent = some parentHandle)
    (publicParent : family parentHandle.object = none) (component : Directories.component name = true)
    (publicName : PrivateNames.reservedBytes name = false) :
    ∃ observation : ObservedDirectory kernel origin (ordinal + events.length) after uid directory,
      family observation.handle.object = none := by
  have source := run
  cases create <;> unfold Directories.publicAt at source
  all_goals simp only [Bool.false_eq_true, ↓reduceIte] at source
  all_goals
    obtain ⟨opening, result, rest, middle, shape, openedRun, following⟩ := recorded_run_bind_split _ _ source
    cases result with
    | error error => cases following.1
    | ok opened =>
      have known : ∃ observation : ObservedDirectory kernel origin (ordinal + opening.length) middle uid opened,
          family observation.handle.object = none := by
        first | exact directory_open_public laws opens ordinal uid parent name parentHandle
                  openedRun parentLive publicParent component publicName
              | exact directory_ensure_public laws opens ordinal uid parent name parentHandle
                  openedRun parentLive publicParent component publicName
      obtain ⟨known, publicObject⟩ := known
      obtain ⟨checking, result, last, checked, checkedShape, checkedRun, final⟩ := recorded_run_bind_split _ _ following
      cases result with
      | error error => cases final.1
      | ok fd =>
        obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq final.1
        cases same
        obtain ⟨rfl, checkedLive⟩ := public_handle_same laws origin _ opened.fd known.handle checkedRun known.live
        have finalLive : after.handles opened.fd = some known.handle := by
          rw [empty_recorded_handles final.2]
          exact checkedLive
        exact ⟨known.advance finalLive (by simp only [shape, checkedShape, List.length_append]; omega), publicObject⟩

-- §FS-host-boundary.ownership: The real source walk opens the next public directory before
-- closing the old FD. Errors/invalid closes cannot produce a successful later path result.
theorem directory_descend_public {kernel : Contract} (laws : DescriptorContract kernel)
    {origin : FilesystemOrigin} {family : Family} (opens : PublicDirectoryOpens kernel origin family)
    (ordinal uid : Nat) (create : Bool) (initial : Directories.Opened) (names : List ByteArray) (parentHandle : Handle)
    {before after : World} {events : List (Request × Reply)} {directory : Directories.Opened}
    (run : RecordedRun kernel origin ordinal (Directories.descend uid create initial names).lower
      before events after (.ok directory)) (parentLive : before.handles initial.fd = some parentHandle)
    (publicParent : family parentHandle.object = none)
    (components : ∀ name ∈ names, Directories.component name = true ∧ PrivateNames.reservedBytes name = false) :
    ∃ handle, after.handles directory.fd = some handle ∧ family handle.object = none := by
  induction names generalizing ordinal initial before events parentHandle with
  | nil =>
    obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq run.1
    cases same
    exact ⟨parentHandle, by rw [empty_recorded_handles run.2]; exact parentLive, publicParent⟩
  | cons name rest ih =>
    have source := run
    unfold Directories.descend at source
    obtain ⟨opening, result, remaining, openedWorld, trace, opened, following⟩ := recorded_run_bind_split _ _ source
    obtain ⟨closing, closed, last, closedWorld, closeTrace, closeRun, final⟩ := recorded_run_bind_split _ _ following
    cases closed with
    | error error =>
      cases result with
      | error original => cases final.1
      | ok next =>
        obtain ⟨logical, rejected⟩ := returns_source _ final.1
        have impossible := (Snapshot.closeResult_provenance _ _ rejected).1
        cases impossible
    | ok next =>
      have same := (Snapshot.closeResult_provenance _ _ (close_result_identity _ _ ▸ closeRun.1)).1
      cases same
      obtain ⟨observed, publicObject⟩ := directory_public_public laws opens ordinal uid initial.fd name create parentHandle
        opened parentLive publicParent (components name (by simp)).1 (components name (by simp)).2
      have different := (history_borrow _ _ (public_at_borrow laws initial.fd parentHandle _ _ _ _)
        opened parentLive).2
      have live := (history_borrow _ _ (close_borrow laws initial.fd next.fd observed.handle (.ok next) different)
        closeRun observed.live).1
      exact ih _ _ observed.handle final live publicObject
        (by intro component member; exact components component (by simp [member]))

end LeanCage.Host.Kernel.Lowered
