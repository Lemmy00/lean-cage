import FilesystemParentHandles
import FilesystemReferenceLifetime
import FilesystemMetadata

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: Keep the actual fstat call and its source/global ordinal.
structure StatSample (kernel : Contract) (origin : FilesystemOrigin) (fd : UInt64) (handle : Handle)
    (information : Stat) where
  ordinal : Nat
  before : World
  after : World
  reply : Reply
  actual : kernel.step before {op := .stat, first := fd} (some reply) after
  sampled : origin ordinal {op := .stat, first := fd} reply before after
  live : before.handles fd = some handle
  parsed : parseStat reply = some information

structure ObservedDirectory (kernel : Contract) (origin : FilesystemOrigin) (limit : Nat)
    (world : World) (uid : Nat) (directory : Directories.Opened) where
  handle : Handle
  live : world.handles directory.fd = some handle
  raw : handle.rawOwned = true
  sample : StatSample kernel origin directory.fd handle directory.information
  earlier : sample.ordinal < limit
  trusted : Directories.trusted uid directory.information = true

structure UidSample (kernel : Contract) (origin : FilesystemOrigin) (uid : Nat) where
  ordinal : Nat
  before : World
  after : World
  reply : Reply
  actual : kernel.step before {op := .euid} (some reply) after
  sampled : origin ordinal {op := .euid} reply before after
  success : nativeError reply = false
  empty : reply.2 = .empty
  identity : reply.1.toNat = uid

def ObservedDirectory.advance {kernel : Contract} {origin : FilesystemOrigin} {limit final : Nat}
    {before after : World} {uid : Nat} {directory : Directories.Opened}
    (observation : ObservedDirectory kernel origin limit before uid directory)
    (live : after.handles directory.fd = some observation.handle) (later : limit ≤ final) :
    ObservedDirectory kernel origin final after uid directory :=
  ⟨observation.handle, live, observation.raw, observation.sample, Nat.lt_of_lt_of_le observation.earlier later,
    observation.trusted⟩

theorem directory_inspect_recorded {kernel : Contract} (laws : DescriptorContract kernel)
    (origin : FilesystemOrigin) (ordinal uid : Nat) (fd : UInt64) (handle : Handle)
    {before after : World} {events : List (Request × Reply)} {directory : Directories.Opened}
    (run : RecordedRun kernel origin ordinal (Directories.inspect uid fd) before events after (.ok directory))
    (live : before.handles fd = some handle) (raw : handle.rawOwned = true) :
    Nonempty (ObservedDirectory kernel origin (ordinal + events.length) after uid directory) := by
  obtain ⟨sameFd, reply, shape, parsed, trusted⟩ := Retrieval.directoryInspection_source _ _ run.1
  have history := run.2
  rw [shape] at history
  obtain ⟨actual, checked, leading, operation, sampled, trailing⟩ := recorded_history_head history
  have actualLive : actual.handles fd = some handle := by
    rw [empty_recorded_handles leading]
    exact live
  have finalLive : after.handles directory.fd = some handle := by
    rw [sameFd, empty_recorded_handles trailing,
      laws.retained _ _ _ _ operation (by simp [RetainsDescriptors])]
    exact actualLive
  refine ⟨⟨handle, finalLive, raw,
    ⟨ordinal, actual, checked, reply, ?_, ?_, ?_, parsed⟩, ?_, trusted⟩⟩
  · simpa only [sameFd] using operation
  · simpa only [sameFd] using sampled
  · simpa only [sameFd] using actualLive
  · simp only [shape, List.length_singleton]
    omega

theorem directory_open_recorded {kernel : Contract} (laws : DescriptorContract kernel)
    (origin : FilesystemOrigin) (ordinal uid : Nat) (parent : UInt64) (name : ByteArray)
    {before after : World} {events : List (Request × Reply)} {directory : Directories.Opened}
    (run : RecordedRun kernel origin ordinal (Directories.openAt uid parent name) before events after (.ok directory)) :
    Nonempty (ObservedDirectory kernel origin (ordinal + events.length) after uid directory) := by
  obtain ⟨openedReply, statReply, shape, recognized, parsed, trusted⟩ :=
    Retrieval.directoryOpening_source _ _ _ run.1
  have history := run.2
  rw [shape] at history
  obtain ⟨actual, openedWorld, leading, operation, openSample, rest⟩ := recorded_history_head history
  obtain ⟨fresh, handle, openedLive⟩ := laws.allocated_fresh _ _ _ _ _ operation (.inl rfl) recognized
  obtain ⟨observing, checked, between, observed, sampled, trailing⟩ := recorded_history_head rest
  have atStat : observing.handles directory.fd = some handle := by
    rw [empty_recorded_handles between]
    exact openedLive
  have atEnd : after.handles directory.fd = some handle := by
    rw [empty_recorded_handles trailing, laws.retained _ _ _ _ observed (by simp [RetainsDescriptors])]
    exact atStat
  refine ⟨⟨handle, atEnd, laws.allocated_raw _ _ _ _ _ _ operation (.inl rfl) recognized openedLive,
    ⟨ordinal + 1, observing, checked, statReply, observed, sampled, atStat, parsed⟩, ?_, trusted⟩⟩
  simp only [shape, List.length_cons, List.length_nil]
  omega

theorem directory_ensure_recorded {kernel : Contract} (laws : DescriptorContract kernel)
    (origin : FilesystemOrigin) (ordinal uid : Nat) (parent : UInt64) (name : ByteArray)
    {before after : World} {events : List (Request × Reply)} {directory : Directories.Opened}
    (run : RecordedRun kernel origin ordinal (Directories.ensureAt uid parent name) before events after (.ok directory)) :
    Nonempty (ObservedDirectory kernel origin (ordinal + events.length) after uid directory) := by
  obtain ⟨made, opening, shape, recognized, observation⟩ := Publication.ensureAt_source _ _ _ run.1
  have history := run.2
  rw [shape] at history
  obtain ⟨actual, created, leading, operation, sampled, trailing⟩ := recorded_history_head history
  obtain ⟨observed⟩ := directory_open_recorded laws origin (ordinal + 1) uid parent name
    ⟨directory_observation_returns uid parent name observation, trailing⟩
  exact ⟨observed.advance observed.live (by simp only [shape, List.length_cons]; omega)⟩

private theorem public_handle_same {kernel : Contract} (laws : DescriptorContract kernel)
    (origin : FilesystemOrigin) (ordinal : Nat) (fd : UInt64) (handle : Handle)
    {before after : World} {events : List (Request × Reply)} {result : UInt64}
    (run : RecordedRun kernel origin ordinal (SourcePaths.publicHandle fd) before events after (.ok result))
    (live : before.handles fd = some handle) : result = fd ∧ after.handles fd = some handle := by
  have source := run.1
  unfold SourcePaths.publicHandle at source
  obtain ⟨reply, last, shape, following⟩ := Snapshot.returns_call_split source
  split at following
  · obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq following
    cases same
    have history := run.2
    rw [shape] at history
    obtain ⟨actual, checked, leading, operation, sampled, trailing⟩ := recorded_history_head history
    refine ⟨rfl, ?_⟩
    rw [empty_recorded_handles trailing, laws.retained _ _ _ _ operation (by simp [RetainsDescriptors]),
      empty_recorded_handles leading]
    exact live
  · have impossible := (Snapshot.closeResult_provenance _ _ following).1
    cases impossible

theorem directory_public_recorded {kernel : Contract} (laws : DescriptorContract kernel)
    (origin : FilesystemOrigin) (ordinal uid : Nat) (parent : UInt64) (name : ByteArray) (create : Bool)
    {before after : World} {events : List (Request × Reply)} {directory : Directories.Opened}
    (run : RecordedRun kernel origin ordinal (Directories.publicAt uid parent name create)
      before events after (.ok directory)) :
    Nonempty (ObservedDirectory kernel origin (ordinal + events.length) after uid directory) := by
  have source := run
  cases create <;> unfold Directories.publicAt at source
  all_goals simp only [Bool.false_eq_true, ↓reduceIte] at source
  all_goals
    obtain ⟨opening, result, rest, middle, shape, openedRun, following⟩ := recorded_run_bind_split _ _ source
    cases result with
    | error error => cases following.1
    | ok opened =>
      have known : Nonempty (ObservedDirectory kernel origin (ordinal + opening.length) middle uid opened) := by
        first | exact directory_open_recorded laws origin ordinal uid parent name openedRun
              | exact directory_ensure_recorded laws origin ordinal uid parent name openedRun
      obtain ⟨known⟩ := known
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
        exact ⟨known.advance finalLive (by simp only [shape, checkedShape, List.length_append]; omega)⟩

-- §FS-host-boundary.ownership: The final directory's own fstat follows it through traversal.
theorem directory_descend_recorded {kernel : Contract} (laws : DescriptorContract kernel)
    (origin : FilesystemOrigin) (ordinal uid : Nat) (create : Bool)
    (current : Directories.Opened) (names : List ByteArray) {before after : World}
    {events : List (Request × Reply)} {directory : Directories.Opened}
    (known : ObservedDirectory kernel origin ordinal before uid current)
    (run : RecordedRun kernel origin ordinal (Directories.descend uid create current names)
      before events after (.ok directory)) :
    Nonempty (ObservedDirectory kernel origin (ordinal + events.length) after uid directory) := by
  induction names generalizing current before events ordinal with
  | nil =>
    obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq run.1
    cases same
    exact ⟨known.advance (by rw [empty_recorded_handles run.2]; exact known.live) (by simp)⟩
  | cons name rest ih =>
    have source := run
    unfold Directories.descend at source
    obtain ⟨opening, result, following, middle, shape, openedRun, afterOpen⟩ := recorded_run_bind_split _ _ source
    obtain ⟨closing, closed, ending, closedWorld, closeShape, closedRun, afterClose⟩ :=
      recorded_run_bind_split _ _ afterOpen
    cases closed with
    | error error =>
      cases result with
      | error original => cases afterClose.1
      | ok next => have impossible := (Snapshot.closeResult_provenance _ _ afterClose.1).1; cases impossible
    | ok next =>
      have same := (Snapshot.closeResult_provenance _ _ closedRun.1).1
      cases same
      obtain ⟨child⟩ := directory_public_recorded laws origin ordinal uid current.fd name create openedRun
      have different := (borrow_returns (public_at_borrow laws current.fd known.handle uid current.fd name create)
        ⟨openedRun.1, recorded_history_erase openedRun.2⟩ known.live).2
      have nextLive := (borrow_returns (close_borrow laws current.fd next.fd child.handle (.ok next) different)
        ⟨closedRun.1, recorded_history_erase closedRun.2⟩ child.live).1
      obtain ⟨final⟩ := ih _ next (child.advance nextLive (Nat.le_add_right _ _)) afterClose
      exact ⟨final.advance final.live (by simp only [shape, closeShape, List.length_append]; omega)⟩

structure ObservedParent (kernel : Contract) (origin : FilesystemOrigin) (limit : Nat)
    (world : World) (parent : Directories.Parent) where
  directory : ObservedDirectory kernel origin limit world parent.uid parent.directory
  identity : UidSample kernel origin parent.uid
  identityEarlier : identity.ordinal < limit

-- §FS-host-boundary.ownership: The actual parent producer retains both UID and fstat observations.
theorem parent_recorded {kernel : Contract} (laws : DescriptorContract kernel)
    (origin : FilesystemOrigin) (ordinal : Nat) (path : ByteArray) (create : Bool)
    {before after : World} {events : List (Request × Reply)} {parent : Directories.Parent}
    (run : RecordedRun kernel origin ordinal (Directories.parent path create) before events after (.ok parent)) :
    Nonempty (ObservedParent kernel origin (ordinal + events.length) after parent) := by
  have source := run.1
  unfold Directories.parent at source
  obtain ⟨selecting, result, rest, selectedSource, afterSelect, shape⟩ := Snapshot.returns_bind_split _ _ source
  have history := run.2
  rw [shape] at history
  obtain ⟨selectedWorld, selectingHistory, remaining⟩ := recorded_history_split selecting rest history
  cases result with
  | error error => cases afterSelect
  | ok selected =>
    obtain ⟨base⟩ := source_start_guard_recorded laws origin ordinal path ⟨selectedSource, selectingHistory⟩
    have baseRaw : base.handle.rawOwned = true := by
      apply laws.after_raw _ _ _ _ base.guard.actual selected.base base.handle
      rw [(kernel.attribute_frame _ _ _ _ base.guard.actual rfl).1]
      exact base.guard.live
    dsimp only at afterSelect
    split at afterSelect
    · rename_i name named
      split at afterSelect
      · have impossible := (Snapshot.closeResult_provenance _ _ afterSelect).1; cases impossible
      · obtain ⟨identity, later, identityShape, afterIdentity⟩ := Snapshot.returns_call_split afterSelect
        rw [identityShape] at remaining
        obtain ⟨identityBefore, identityAfter, initial, operation, sampled, afterUid⟩ := recorded_history_head remaining
        have identityLive : identityBefore.handles selected.base = some base.handle := by
          rw [empty_recorded_handles initial]
          exact base.live
        have afterIdentityLive : identityAfter.handles selected.base = some base.handle := by
          rw [laws.retained _ _ _ _ operation (by simp [RetainsDescriptors])]
          exact identityLive
        dsimp only [Filesystem.Program.bind] at afterIdentity
        split at afterIdentity
        · have impossible := (Snapshot.closeResult_provenance _ _ afterIdentity).1; cases impossible
        · rename_i valid
          have identityFields : nativeError identity = false ∧ identity.2.isEmpty = true ∧
              identity.1.toNat ≤ 2 ^ 32 - 1 := by
            simpa [Bool.or_eq_true, and_assoc] using valid
          obtain ⟨inspecting, result, descending, inspected, afterInspect, inspectShape⟩ :=
            Snapshot.returns_bind_split _ _ afterIdentity
          rw [inspectShape] at afterUid
          obtain ⟨inspectedWorld, inspectingHistory, descendingHistory⟩ :=
            recorded_history_split inspecting descending afterUid
          cases result with
          | error error => cases afterInspect
          | ok inspectedDirectory =>
            obtain ⟨inspectedObservation⟩ := directory_inspect_recorded laws origin
              (ordinal + selecting.length + 1) identity.1.toNat selected.base base.handle
              ⟨inspected, inspectingHistory⟩ afterIdentityLive baseRaw
            obtain ⟨descending, result, last, descended, final, descendShape⟩ :=
              Snapshot.returns_bind_split _ _ afterInspect
            obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq final
            cases result with
            | error error => cases same
            | ok directory =>
              cases same
              rw [descendShape] at descendingHistory
              obtain ⟨observed⟩ := directory_descend_recorded laws origin _ _ create inspectedDirectory
                selected.parts.dropLast inspectedObservation
                ⟨descended, by simpa only [List.append_nil] using descendingHistory⟩
              refine ⟨⟨observed.advance observed.live ?_,
                ⟨ordinal + selecting.length, identityBefore, identityAfter, identity, operation, sampled,
                  identityFields.1, ?_, rfl⟩, ?_⟩⟩
              · simp only [shape, identityShape, inspectShape, descendShape, List.length_append,
                  List.length_cons, List.length_nil]
                omega
              · exact ByteArray.size_eq_zero_iff.mp
                  (by simpa only [ByteArray.isEmpty, beq_iff_eq] using identityFields.2.1)
              · simp only [shape, identityShape, inspectShape, descendShape, List.length_append,
                  List.length_cons, List.length_nil]
                omega
    · have impossible := (Snapshot.closeResult_provenance _ _ afterSelect).1; cases impossible

-- §FS-host-boundary.ownership: Internal /tmp selection uses the same two real observations.
theorem temporary_parent_recorded {kernel : Contract} (laws : DescriptorContract kernel)
    (origin : FilesystemOrigin) (ordinal : Nat) {before after : World} {events : List (Request × Reply)}
    {directory : Directories.Opened} {uid : Nat}
    (run : RecordedRun kernel origin ordinal Directories.temporaryParent before events after
      (.ok (directory, "/tmp", uid))) :
    ∃ _observed : ObservedDirectory kernel origin (ordinal + events.length) after uid directory,
      ∃ identity : UidSample kernel origin uid, identity.ordinal < ordinal + events.length := by
  obtain ⟨_, identity, opening, shape, success, empty, uidSame, bounded, opened⟩ :=
    RunDirectory.temporaryParent_source run.1
  have history := run.2
  rw [shape] at history
  obtain ⟨actual, identified, leading, operation, sampled, following⟩ := recorded_history_head history
  obtain ⟨observed⟩ := directory_open_recorded laws origin (ordinal + 1) uid cwd "/tmp".toUTF8
    ⟨directory_observation_returns uid cwd "/tmp".toUTF8 opened, following⟩
  refine ⟨observed.advance observed.live (by simp only [shape, List.length_cons]; omega),
    ⟨ordinal, actual, identified, identity, operation, sampled, success, empty, uidSame.symm⟩, ?_⟩
  simp only [shape, List.length_cons]
  omega

-- §FS-host-boundary.ownership: The directory's account is the actual primitive UID, not a label.
theorem sampled_uid_is_host {kernel : Contract} {hostUid : Nat} (accounts : AccountContract kernel hostUid)
    {origin : FilesystemOrigin} {uid : Nat} (sample : UidSample kernel origin uid) : uid = hostUid :=
  sample.identity.symm.trans (accounts.effective _ _ _ _ sample.actual rfl sample.success sample.empty)

end LeanCage.Host.Kernel
