import FilesystemLoweredDirectoryBorrowing

namespace LeanCage.Host.Kernel.Lowered
open Filesystem

theorem public_handle_same {kernel : Contract} (laws : DescriptorContract kernel)
    (origin : FilesystemOrigin) (ordinal : Nat) (fd : UInt64) (handle : Handle)
    {before after : World} {events : List (Request × Reply)} {result : UInt64}
    (run : RecordedRun kernel origin ordinal (SourcePaths.publicHandle fd).lower before events after (.ok result))
    (live : before.handles fd = some handle) : result = fd ∧ after.handles fd = some handle := by
  have source := run.1
  change Returns (Filesystem.Program.call
    {op := .getAttribute, first := fd, second := 1, left := PrivateNames.attributeName}
    (fun reply => (if nativeError reply && errorNumber reply == 61 then
      Filesystem.Program.pure (.ok fd)
    else closeResult fd (.error "caller path enters private application state")).lower)) events (.ok result) at source
  obtain ⟨reply, last, trace, following⟩ := Snapshot.returns_call_split source
  split at following
  · obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq following
    cases same
    have history := run.2
    rw [trace] at history
    obtain ⟨actual, checked, leading, operation, sampled, trailing⟩ := recorded_history_head history
    refine ⟨rfl, ?_⟩
    rw [empty_recorded_handles trailing, laws.retained _ _ _ _ operation (by simp [RetainsDescriptors]),
      empty_recorded_handles leading]
    exact live
  · obtain ⟨logical, rejected⟩ := returns_source _ following
    have impossible := (Snapshot.closeResult_provenance _ _ rejected).1
    cases impossible

-- §FS-host-boundary.ownership: Parent creation's actual mkdir probes remain in the transcript;
-- the final observation comes from the following actual guarded directory open and fstat.
theorem directory_ensure_recorded {kernel : Contract} (laws : DescriptorContract kernel)
    (origin : FilesystemOrigin) (ordinal uid : Nat) (parent : UInt64) (name : ByteArray)
    {before after : World} {events : List (Request × Reply)} {directory : Directories.Opened}
    (run : RecordedRun kernel origin ordinal (Directories.ensureAt uid parent name).lower
      before events after (.ok directory)) :
    Nonempty (ObservedDirectory kernel origin (ordinal + events.length) after uid directory) := by
  let request : Request := {op := .mkdirAt, first := parent, second := 448, left := name}
  let next (made : Reply) : Filesystem.Program (Result Directories.Opened) :=
    if made.1 == 0 && made.2.isEmpty then Directories.openAt uid parent name
    else if nativeError made && errorNumber made == 17 then Directories.openAt uid parent name
    else pure (.error (failure "parent mkdirat" made))
  have stage : RecordedRun kernel origin ordinal ((guardedCall request).bind (fun reply => (next reply).lower))
      before events after (.ok directory) := run
  obtain ⟨making, reply, opening, middle, trace, made, remaining⟩ := Kernel.recorded_run_bind_split _ _ stage
  unfold next at remaining
  split at remaining
  · obtain ⟨observation⟩ := directory_open_recorded laws origin (ordinal + making.length) uid parent name remaining
    exact ⟨observation.advance observation.live (by simp only [trace, List.length_append]; omega)⟩
  · split at remaining
    · obtain ⟨observation⟩ := directory_open_recorded laws origin (ordinal + making.length) uid parent name remaining
      exact ⟨observation.advance observation.live (by simp only [trace, List.length_append]; omega)⟩
    · cases remaining.1

theorem directory_public_recorded {kernel : Contract} (laws : DescriptorContract kernel)
    (origin : FilesystemOrigin) (ordinal uid : Nat) (parent : UInt64) (name : ByteArray) (create : Bool)
    {before after : World} {events : List (Request × Reply)} {directory : Directories.Opened}
    (run : RecordedRun kernel origin ordinal (Directories.publicAt uid parent name create).lower
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

-- §FS-host-boundary.ownership: The same fstat provenance follows the actual raw path walk,
-- including all lookup probes and closing the previous directory only after retaining the next.
theorem directory_descend_recorded {kernel : Contract} (laws : DescriptorContract kernel)
    (origin : FilesystemOrigin) (ordinal uid : Nat) (create : Bool)
    (current : Directories.Opened) (names : List ByteArray) {before after : World}
    {events : List (Request × Reply)} {directory : Directories.Opened}
    (known : ObservedDirectory kernel origin ordinal before uid current)
    (run : RecordedRun kernel origin ordinal (Directories.descend uid create current names).lower
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
      | ok next =>
        have impossible := (Snapshot.closeResult_provenance _ _ (close_result_identity _ _ ▸ afterClose.1)).1
        cases impossible
    | ok next =>
      have same := (Snapshot.closeResult_provenance _ _ (close_result_identity _ _ ▸ closedRun.1)).1
      cases same
      obtain ⟨child⟩ := directory_public_recorded laws origin ordinal uid current.fd name create openedRun
      have different := (history_borrow _ _ (public_at_borrow laws current.fd known.handle uid current.fd name create)
        openedRun known.live).2
      have nextLive := (history_borrow _ _ (close_borrow laws current.fd next.fd child.handle (.ok next) different)
        closedRun child.live).1
      obtain ⟨final⟩ := ih _ next (child.advance nextLive (Nat.le_add_right _ _)) afterClose
      exact ⟨final.advance final.live (by simp only [shape, closeShape, List.length_append]; omega)⟩

-- §FS-host-boundary.ownership: The returned parent retains real UID/fstat provenance from
-- the actual retained-CWD traversal and its full expanded primitive transcript.
theorem parent_recorded {kernel : Contract} (laws : DescriptorContract kernel)
    (origin : FilesystemOrigin) (ordinal : Nat) (path : ByteArray) (create : Bool)
    {before after : World} {events : List (Request × Reply)} {parent : Directories.Parent}
    (run : RecordedRun kernel origin ordinal (Directories.parent path create).lower
      before events after (.ok parent)) :
    Nonempty (ObservedParent kernel origin (ordinal + events.length) after parent) := by
  have source := run
  unfold Directories.parent at source
  obtain ⟨selecting, result, rest, selectedWorld, shape, selectedRun, afterSelect⟩ := recorded_run_bind_split _ _ source
  cases result with
  | error error => cases afterSelect.1
  | ok selected =>
    obtain ⟨base⟩ := source_start_guard_recorded laws origin ordinal path selectedRun
    have baseRaw : base.handle.rawOwned = true := by
      apply laws.after_raw _ _ _ _ base.guard.actual selected.base base.handle
      rw [(kernel.attribute_frame _ _ _ _ base.guard.actual rfl).1]
      exact base.guard.live
    have restSource := afterSelect.1
    dsimp only at restSource
    split at restSource
    · rename_i name named
      split at restSource
      · obtain ⟨logical, rejected⟩ := returns_source _ restSource
        have impossible := (Snapshot.closeResult_provenance _ _ rejected).1
        cases impossible
      · obtain ⟨identity, later, identityShape, afterIdentity⟩ := Snapshot.returns_call_split restSource
        have remaining := afterSelect.2
        rw [identityShape] at remaining
        obtain ⟨identityBefore, identityAfter, initial, operation, sampled, afterUid⟩ := recorded_history_head remaining
        have identityLive : identityBefore.handles selected.base = some base.handle := by
          rw [empty_recorded_handles initial]
          exact base.live
        have afterIdentityLive : identityAfter.handles selected.base = some base.handle := by
          rw [laws.retained _ _ _ _ operation (by simp [RetainsDescriptors])]
          exact identityLive
        change Returns (if nativeError identity || !identity.2.isEmpty || identity.1.toNat > 2 ^ 32 - 1 then
          closeResult selected.base (.error (failure "host identity" identity))
        else do
          let base ← Directories.inspect identity.1.toNat selected.base
          match base with
          | .error error => pure (.error error)
          | .ok base => do
            let result ← Directories.descend identity.1.toNat create base selected.parts.dropLast
            pure (result.map (fun directory => (⟨directory, name, identity.1.toNat⟩ : Directories.Parent)))).lower
          later (.ok parent) at afterIdentity
        split at afterIdentity
        · obtain ⟨logical, rejected⟩ := returns_source _ afterIdentity
          have impossible := (Snapshot.closeResult_provenance _ _ rejected).1
          cases impossible
        · rename_i valid
          have identityFields : nativeError identity = false ∧ identity.2.isEmpty = true ∧
              identity.1.toNat ≤ 2 ^ 32 - 1 := by
            simpa [Bool.or_eq_true, and_assoc] using valid
          have afterIdentityRun : RecordedRun kernel origin (ordinal + selecting.length + 1) _
              identityAfter later after (.ok parent : Result Directories.Parent) := ⟨afterIdentity, afterUid⟩
          obtain ⟨inspecting, result, descending, inspectedWorld, inspectShape, inspected, afterInspect⟩ :=
            recorded_run_bind_split _ _ afterIdentityRun
          cases result with
          | error error => cases afterInspect.1
          | ok inspectedDirectory =>
            obtain ⟨inspectedObservation⟩ := Kernel.directory_inspect_recorded laws origin
              (ordinal + selecting.length + 1) identity.1.toNat selected.base base.handle
              ⟨directory_inspect_identity _ _ ▸ inspected.1, inspected.2⟩ afterIdentityLive baseRaw
            obtain ⟨descending, result, last, descendedWorld, descendShape, descended, final⟩ :=
              recorded_run_bind_split _ _ afterInspect
            obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq final.1
            cases result with
            | error error => cases same
            | ok directory =>
              cases same
              obtain ⟨observed⟩ := directory_descend_recorded laws origin _ _ create inspectedDirectory
                selected.parts.dropLast inspectedObservation descended
              have finalLive : after.handles directory.fd = some observed.handle := by
                rw [empty_recorded_handles final.2]
                exact observed.live
              refine ⟨⟨observed.advance finalLive ?_,
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
    · obtain ⟨logical, rejected⟩ := returns_source _ restSource
      have impossible := (Snapshot.closeResult_provenance _ _ rejected).1
      cases impossible

end LeanCage.Host.Kernel.Lowered
