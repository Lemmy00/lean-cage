import SnapshotProofs.Inputs
import SnapshotProofs.Copy

namespace LeanCage.Host.Snapshot

open Filesystem

theorem publicHandle_input (fd : UInt64) : InputProgram (SourcePaths.publicHandle fd) := by
  unfold SourcePaths.publicHandle
  apply InputProgram.call (by exact ⟨rfl, rfl⟩)
  intro reply
  split
  · exact .pure _
  · exact closeResult_input _ _

theorem sourceOpenAt_input (parent : UInt64) (name : ByteArray) (directory : Bool) :
    InputProgram (SourcePaths.openAt parent name directory) := by
  unfold SourcePaths.openAt
  apply InputProgram.call (by cases directory; exact .inl rfl; exact .inr rfl)
  intro opened
  split
  · exact .pure _
  · exact publicHandle_input _

theorem releaseParent_input (parent : UInt64) (child : Result UInt64) :
    InputProgram (SourcePaths.releaseParent parent child) := by
  unfold SourcePaths.releaseParent
  apply input_bind (closeResult_input _ _)
  intro result
  cases result with
  | ok => exact .pure _
  | error =>
    cases child with
    | error => exact .pure _
    | ok => exact closeResult_input _ _

theorem sourceWalk_input (parent : UInt64) (parts : List ByteArray) (directory : Bool) :
    InputProgram (SourcePaths.walk parent parts directory) := by
  induction parts generalizing parent with
  | nil => exact .pure _
  | cons name rest ih =>
    unfold SourcePaths.walk
    apply input_bind (sourceOpenAt_input _ _ _)
    intro opened
    apply input_bind (releaseParent_input _ _)
    intro released
    cases released with
    | error => exact .pure _
    | ok child => exact ih child

theorem sourceAbsolute_input (path : ByteArray) : InputProgram (SourcePaths.absolute path) := by
  unfold SourcePaths.absolute
  split
  · exact .pure _
  · split
    · exact .pure _
    · apply InputProgram.call (by trivial)
      intro current
      dsimp only [Filesystem.Program.bind]
      split
      · exact .pure _
      · split <;> exact .pure _

theorem sourceIdentity_input (fd : UInt64) : InputProgram (SourcePaths.identity fd) := by
  unfold SourcePaths.identity
  apply InputProgram.call (by trivial)
  intro reply
  split <;> exact .pure _

theorem sourceAncestry_input (fuel : Nat) (current : UInt64) (root : ByteArray) :
    InputProgram (SourcePaths.ancestry fuel current root) := by
  induction fuel generalizing current with
  | zero => exact closeResult_input _ _
  | succ fuel ih =>
    unfold SourcePaths.ancestry
    apply input_bind (sourceIdentity_input _)
    intro observed
    cases observed with
    | error => exact closeResult_input _ _
    | ok observed =>
      dsimp only
      split
      · exact closeResult_input _ _
      · apply input_bind (sourceOpenAt_input _ _ _)
        intro parent
        apply input_bind (releaseParent_input _ _)
        intro released
        cases released with
        | error => exact .pure _
        | ok parent => exact ih _

theorem sourceCheckAncestry_input (base : UInt64) : InputProgram (SourcePaths.checkAncestry base) := by
  unfold SourcePaths.checkAncestry
  apply input_bind (sourceOpenAt_input _ _ _)
  intro root
  cases root with
  | error => exact .pure _
  | ok root =>
    apply input_bind (input_bind (sourceIdentity_input _) (closeResult_input _))
    intro observed
    cases observed with
    | error => exact .pure _
    | ok identity =>
      apply input_bind (sourceOpenAt_input _ _ _)
      intro duplicate
      cases duplicate with
      | error => exact .pure _
      | ok duplicate => exact sourceAncestry_input _ _ _

theorem sourceStart_input (path : ByteArray) : InputProgram (SourcePaths.start path) := by
  unfold SourcePaths.start
  split
  · exact .pure _
  · split
    · apply input_bind (sourceOpenAt_input _ _ _)
      intro root
      exact .pure _
    · apply input_bind (sourceOpenAt_input _ _ _)
      intro base
      cases base with
      | error => exact .pure _
      | ok base =>
        apply InputProgram.call (by trivial)
        intro spelling
        dsimp only [Filesystem.Program.bind]
        split
        · exact closeResult_input _ _
        · apply input_bind (sourceCheckAncestry_input _)
          intro checked
          cases checked with
          | error => exact closeResult_input _ _
          | ok checkedUnit => cases checkedUnit; exact .pure _

theorem sourceOpen_input (path : ByteArray) (directory : Bool) :
    InputProgram (SourcePaths.open path directory) := by
  unfold SourcePaths.open
  apply input_bind (sourceStart_input _)
  intro selected
  cases selected with
  | error => exact .pure _
  | ok selected => exact sourceWalk_input _ _ _

theorem sourceCopyFile_input (path : ByteArray) (limit : Nat) :
    InputProgram (SourcePaths.copyFile path limit) := by
  unfold SourcePaths.copyFile
  apply input_bind (sourceOpen_input _ _)
  intro opened
  cases opened with
  | error => exact .pure _
  | ok fd => exact input_bind (copyOpened_input _ _) (closeResult_input _)

def SourceOpening (parent : UInt64) (name : ByteArray) (directory : Bool)
    (events : List (Request × Reply)) (fd : UInt64) : Prop :=
  ∃ opened observedAttribute,
    events = [({
      op := .openAt
      first := parent
      second := if directory then directoryFlags else readFlags
      left := name }, opened),
      ({ op := .getAttribute, first := fd, second := 1, left := PrivateNames.attributeName }, observedAttribute)] ∧
    descriptor opened = some fd ∧ nativeError observedAttribute = true ∧
    errorNumber observedAttribute = 61

-- §FS-host-boundary.ownership: Every successful open checks the actual returned object's attribute.
theorem sourceOpenAt_source (parent : UInt64) (name : ByteArray) (directory : Bool)
    {events : List (Request × Reply)} {fd : UInt64}
    (run : Returns (SourcePaths.openAt parent name directory) events (.ok fd)) :
    SourceOpening parent name directory events fd := by
  unfold SourcePaths.openAt at run
  obtain ⟨opened, rest, rfl, tail⟩ := returns_call_split run
  split at tail
  · cases tail
  · rename_i child recognized
    unfold SourcePaths.publicHandle at tail
    obtain ⟨observedAttribute, last, rfl, checked⟩ := returns_call_split tail
    split at checked
    · rename_i publicResult
      obtain ⟨rfl, same⟩ := returns_pure_eq checked
      cases same
      have fields : nativeError observedAttribute = true ∧
          errorNumber observedAttribute = 61 := by
        simpa only [Bool.and_eq_true, beq_iff_eq] using publicResult
      exact ⟨opened, observedAttribute, rfl, recognized, fields.1, fields.2⟩
    · have impossible := (closeResult_provenance _ _ checked).1
      cases impossible

private theorem source_guard {α : Type} {condition : Bool} {error : Failure}
    {next : Unit → Result α} {answer : α}
    (accepted : (if condition then (Except.error error).bind next else next ()) = .ok answer) :
    condition = false ∧ next () = .ok answer := by
  cases condition with
  | false => exact ⟨rfl, accepted⟩
  | true => cases accepted

-- §FS-host-boundary.ownership: All caller components are checked before the first path open.
theorem sourceComponents_fields (path : ByteArray) (parts : List ByteArray)
    (accepted : SourcePaths.components path = .ok parts) :
    path.isEmpty = false ∧ rawPathValid path = true ∧
    parts = ((path.data.toList.splitOn 47).filter (fun part => !part.isEmpty)).map
      (fun part => ByteArray.mk part.toArray) ∧
    ∀ part ∈ parts, part.size ≤ 255 ∧ PrivateNames.reservedBytes part = false := by
  unfold SourcePaths.components at accepted
  obtain ⟨root, accepted⟩ := source_guard accepted
  obtain ⟨bounded, accepted⟩ := source_guard accepted
  cases accepted
  have actualRoot : path.isEmpty = false ∧ rawPathValid path = true := by
    simpa [Bool.or_eq_true, and_assoc] using Bool.eq_false_iff.mp root
  have actualBound : (((path.data.toList.splitOn 47).filter (fun part => !part.isEmpty)).map
      (fun part => ByteArray.mk part.toArray)).all
      (fun part => part.size ≤ 255 && !PrivateNames.reservedBytes part) = true := by
    simpa using bounded
  exact ⟨actualRoot.1, actualRoot.2, rfl, fun part member => by
    simpa using List.all_eq_true.mp actualBound part member⟩

inductive SourceWalk : UInt64 → List ByteArray → Bool → List (Request × Reply) → UInt64 → Prop where
  | done (fd : UInt64) (directory : Bool) : SourceWalk fd [] directory [] fd
  | next (parent child final : UInt64) (name : ByteArray) (rest : List ByteArray) (directory : Bool)
      (opening closing following : List (Request × Reply))
      (opened : SourceOpening parent name (directory || !rest.isEmpty) opening child)
      (closed : Returns (closeResult parent (.ok child)) closing (.ok child))
      (tail : SourceWalk child rest directory following final) :
      SourceWalk parent (name :: rest) directory (opening ++ closing ++ following) final

theorem releaseParent_source (parent : UInt64) (child : Result UInt64)
    {events : List (Request × Reply)} {fd : UInt64}
    (run : Returns (SourcePaths.releaseParent parent child) events (.ok fd)) :
    child = .ok fd ∧ Returns (closeResult parent (.ok fd)) events (.ok fd) := by
  unfold SourcePaths.releaseParent at run
  obtain ⟨closing, result, last, closed, final, shape⟩ := returns_bind_split _ _ run
  cases result with
  | error error =>
    cases child with
    | error => cases final
    | ok => have impossible := (closeResult_provenance _ _ final).1; cases impossible
  | ok value =>
    obtain ⟨rfl, same⟩ := returns_pure_eq final
    cases same
    have childValue := (closeResult_provenance _ _ closed).1
    cases childValue
    exact ⟨rfl, by simpa only [shape, List.append_nil] using closed⟩

theorem sourceWalk_source (parent : UInt64) (parts : List ByteArray) (directory : Bool)
    {events : List (Request × Reply)} {fd : UInt64}
    (run : Returns (SourcePaths.walk parent parts directory) events (.ok fd)) :
    SourceWalk parent parts directory events fd := by
  induction parts generalizing parent events fd with
  | nil => cases run; exact .done _ _
  | cons name rest ih =>
    unfold SourcePaths.walk at run
    obtain ⟨opening, opened, last, openRun, afterOpen, shape⟩ := returns_bind_split _ _ run
    obtain ⟨closing, released, following, releaseRun, final, releaseShape⟩ := returns_bind_split _ _ afterOpen
    cases released with
    | error => cases final
    | ok child =>
      obtain ⟨same, closed⟩ := releaseParent_source _ _ releaseRun
      cases same
      have observed := SourceWalk.next parent child fd name rest directory opening closing following
        (sourceOpenAt_source _ _ _ openRun) closed (ih _ final)
      simpa only [shape, releaseShape, List.append_assoc] using observed

def DirectoryIdentity (fd : UInt64) (events : List (Request × Reply)) (value : ByteArray) : Prop :=
  value.size = 24 ∧ events = [({ op := .directoryIdentity, first := fd }, (0, value))]

theorem sourceIdentity_source (fd : UInt64) {events : List (Request × Reply)} {value : ByteArray}
    (run : Returns (SourcePaths.identity fd) events (.ok value)) : DirectoryIdentity fd events value := by
  unfold SourcePaths.identity at run
  obtain ⟨reply, rest, rfl, tail⟩ := returns_call_split run
  split at tail
  · rename_i checked
    obtain ⟨rfl, same⟩ := returns_pure_eq tail
    cases same
    have fields : reply.1 = 0 ∧ reply.2.size = 24 := by simpa using checked
    exact ⟨fields.2, by cases reply; simp_all⟩
  · cases tail

inductive Ancestry (root : ByteArray) : Nat → UInt64 → List (Request × Reply) → Prop where
  | reached (fuel : Nat) (current : UInt64) (observing closing : List (Request × Reply))
      (identified : DirectoryIdentity current observing root)
      (closed : Returns (closeResult current (.ok ())) closing (.ok ())) :
      Ancestry root (fuel + 1) current (observing ++ closing)
  | parent (fuel : Nat) (current parent : UInt64) (value : ByteArray)
      (observing opening closing following : List (Request × Reply))
      (identified : DirectoryIdentity current observing value) (different : value ≠ root)
      (opened : SourceOpening current "..".toUTF8 true opening parent)
      (closed : Returns (closeResult current (.ok parent)) closing (.ok parent))
      (tail : Ancestry root fuel parent following) :
      Ancestry root (fuel + 1) current (observing ++ opening ++ closing ++ following)

-- §FS-host-boundary.ownership: Bounded '..' checks keep the original CWD descriptor separate.
theorem sourceAncestry_source (fuel : Nat) (current : UInt64) (root : ByteArray)
    {events : List (Request × Reply)}
    (run : Returns (SourcePaths.ancestry fuel current root) events (.ok ())) :
    Ancestry root fuel current events := by
  induction fuel generalizing current events with
  | zero => have impossible := (closeResult_provenance _ _ run).1; cases impossible
  | succ fuel ih =>
    unfold SourcePaths.ancestry at run
    obtain ⟨observing, result, rest, identified, afterIdentity, shape⟩ := returns_bind_split _ _ run
    cases result with
    | error => have impossible := (closeResult_provenance _ _ afterIdentity).1; cases impossible
    | ok value =>
      dsimp only at afterIdentity
      split at afterIdentity
      · rename_i same
        have same : value = root := by simpa using same
        cases same
        exact shape ▸ .reached fuel current observing rest (sourceIdentity_source _ identified) afterIdentity
      · rename_i different
        obtain ⟨opening, parent, later, opened, afterOpen, nextShape⟩ := returns_bind_split _ _ afterIdentity
        obtain ⟨closing, released, following, closed, final, closeShape⟩ := returns_bind_split _ _ afterOpen
        cases released with
        | error => cases final
        | ok parent =>
          obtain ⟨same, closedSource⟩ := releaseParent_source _ _ closed
          cases same
          have result := Ancestry.parent fuel current parent value observing opening closing following
            (sourceIdentity_source _ identified) (by simpa using different)
            (sourceOpenAt_source _ _ _ opened) closedSource (ih _ final)
          simpa only [shape, nextShape, closeShape, List.append_assoc] using result

def CheckedAncestry (base : UInt64) (events : List (Request × Reply)) : Prop :=
  ∃ root rootValue duplicate opening observing rootClose duplication following,
    events = opening ++ observing ++ rootClose ++ duplication ++ following ∧
    SourceOpening cwd "/".toUTF8 true opening root ∧
    DirectoryIdentity root observing rootValue ∧
    Returns (closeResult root (.ok rootValue)) rootClose (.ok rootValue) ∧
    SourceOpening base ".".toUTF8 true duplication duplicate ∧ Ancestry rootValue 4096 duplicate following

theorem sourceCheckAncestry_source (base : UInt64) {events : List (Request × Reply)}
    (run : Returns (SourcePaths.checkAncestry base) events (.ok ())) : CheckedAncestry base events := by
  unfold SourcePaths.checkAncestry at run
  obtain ⟨opening, result, rest, opened, afterOpen, shape⟩ := returns_bind_split _ _ run
  cases result with
  | error => cases afterOpen
  | ok root =>
    obtain ⟨reading, result, later, readRun, afterRead, readingShape⟩ := returns_bind_split _ _ afterOpen
    cases result with
    | error => cases afterRead
    | ok value =>
      obtain ⟨observing, readResult, rootClose, identityRun, closeRun, readShape⟩ :=
        returns_bind_split _ _ readRun
      have same := (closeResult_provenance _ _ closeRun).1
      cases same
      obtain ⟨duplication, duplicateResult, following, dupRun, final, dupShape⟩ :=
        returns_bind_split _ _ afterRead
      cases duplicateResult with
      | error => cases final
      | ok duplicate =>
        exact ⟨root, value, duplicate, opening, observing, rootClose, duplication, following,
          by simpa only [readingShape, readShape, dupShape, List.append_assoc] using shape,
          sourceOpenAt_source _ _ _ opened, sourceIdentity_source _ identityRun, closeRun,
          sourceOpenAt_source _ _ _ dupRun, sourceAncestry_source _ _ _ final⟩

theorem currentSpelling_source (reply : Reply)
    (accepted : SourcePaths.currentSpelling reply = .ok ()) :
    reply.1 = 0 ∧ reply.2.isEmpty = false ∧ reply.2[0]! = 47 ∧
      ∃ parts, SourcePaths.components reply.2 = .ok parts := by
  unfold SourcePaths.currentSpelling at accepted
  obtain ⟨checked, accepted⟩ := source_guard accepted
  have fields : reply.1 = 0 ∧ reply.2.isEmpty = false ∧ reply.2[0]! = 47 := by
    simpa [Bool.or_eq_true, and_assoc] using Bool.eq_false_iff.mp checked
  cases parsed : SourcePaths.components reply.2 with
  | error error => simp only [parsed] at accepted; cases accepted
  | ok parts => exact ⟨fields.1, fields.2.1, fields.2.2, parts, rfl⟩

inductive StartObservation (path : ByteArray) (selected : SourcePaths.Started) :
    List (Request × Reply) → Prop where
  | absolute (events : List (Request × Reply))
      (parts : SourcePaths.components path = .ok selected.parts) (absolute : path[0]! = 47)
      (opened : SourceOpening cwd "/".toUTF8 true events selected.base) : StartObservation path selected events
  | relative (opening checking : List (Request × Reply)) (spelling : Reply)
      (parts : SourcePaths.components path = .ok selected.parts) (relative : path[0]! ≠ 47)
      (opened : SourceOpening cwd ".".toUTF8 true opening selected.base)
      (spelled : SourcePaths.currentSpelling spelling = .ok ())
      (ancestry : CheckedAncestry selected.base checking) :
      StartObservation path selected (opening ++ [({op := .workingDirectory}, spelling)] ++ checking)

-- §FS-host-boundary.ownership: Successful selection retains raw parts and the actual starting FD.
theorem sourceStart_source (path : ByteArray) {events : List (Request × Reply)}
    {selected : SourcePaths.Started} (run : Returns (SourcePaths.start path) events (.ok selected)) :
    StartObservation path selected events := by
  unfold SourcePaths.start at run
  split at run
  · cases run
  · rename_i parts checked
    split at run
    · rename_i absolute
      obtain ⟨opening, result, last, opened, final, shape⟩ := returns_bind_split _ _ run
      obtain ⟨rfl, same⟩ := returns_pure_eq final
      cases result with
      | error => cases same
      | ok base =>
        cases same
        simpa only [shape, List.append_nil] using (StartObservation.absolute (selected := ⟨base, parts⟩) opening checked
          (by simpa using absolute) (sourceOpenAt_source _ _ _ opened))
    · rename_i relative
      obtain ⟨opening, result, rest, opened, afterOpen, shape⟩ := returns_bind_split _ _ run
      cases result with
      | error => cases afterOpen
      | ok base =>
        obtain ⟨spelling, checking, rfl, checkedRun⟩ := returns_call_split afterOpen
        dsimp only [Filesystem.Program.bind] at checkedRun
        split at checkedRun
        · have impossible := (closeResult_provenance _ _ checkedRun).1; cases impossible
        · rename_i spellingUnit spelled
          obtain ⟨auditing, result, last, checkedAncestry, final, auditShape⟩ :=
            returns_bind_split _ _ checkedRun
          cases result with
          | error => have impossible := (closeResult_provenance _ _ final).1; cases impossible
          | ok checkedUnit =>
            cases checkedUnit
            obtain ⟨rfl, same⟩ := returns_pure_eq final
            cases same
            have result := StartObservation.relative (selected := ⟨base, parts⟩) opening auditing spelling checked
              (by simpa using relative) (sourceOpenAt_source _ _ _ opened) spelled
              (sourceCheckAncestry_source _ checkedAncestry)
            simpa only [shape, auditShape, List.append_nil, List.append_assoc, List.singleton_append] using result

def SourcePathObservation (path : ByteArray) (directory : Bool)
    (events : List (Request × Reply)) (fd : UInt64) : Prop :=
  ∃ selected selection following,
    events = selection ++ following ∧
    StartObservation path selected selection ∧
    SourceWalk selected.base selected.parts directory following fd

-- §FS-host-boundary.ownership: Relative traversal uses the selected live CWD.
theorem sourceOpen_source (path : ByteArray) (directory : Bool)
    {events : List (Request × Reply)} {fd : UInt64}
    (run : Returns (SourcePaths.open path directory) events (.ok fd)) :
    SourcePathObservation path directory events fd := by
  unfold SourcePaths.open at run
  obtain ⟨selection, result, following, selectedRun, final, shape⟩ := returns_bind_split _ _ run
  cases result with
  | error => cases final
  | ok selected =>
    exact ⟨selected, selection, following, shape, sourceStart_source _ selectedRun, sourceWalk_source _ _ _ final⟩

def SourceCopiedFile (path : ByteArray) (limit : Nat) (events : List (Request × Reply))
    (copied : CopiedFile) : Prop :=
  ∃ fd opening copies closing,
    events = opening ++ copies ++ closing ∧ SourcePathObservation path false opening fd ∧
    CopiedObservation fd copies copied ∧ copied.bytes.size ≤ limit ∧
    Returns (closeResult fd (.ok copied)) closing (.ok copied)

theorem sourceCopyFile_source (path : ByteArray) (limit : Nat)
    {events : List (Request × Reply)} {copied : CopiedFile}
    (run : Returns (SourcePaths.copyFile path limit) events (.ok copied)) :
    SourceCopiedFile path limit events copied := by
  unfold SourcePaths.copyFile at run
  obtain ⟨opening, result, last, opened, afterOpen, shape⟩ := returns_bind_split _ _ run
  cases result with
  | error => cases afterOpen
  | ok fd =>
    obtain ⟨copies, result, closing, copyRun, closeRun, closeShape⟩ := returns_bind_split _ _ afterOpen
    have same := (closeResult_provenance _ _ closeRun).1
    cases same
    obtain ⟨bounded, observed⟩ := copyOpened_provenance _ _ copyRun
    exact ⟨fd, opening, copies, closing, by simpa only [closeShape, List.append_assoc] using shape,
      sourceOpen_source _ _ opened, observed, bounded, closeRun⟩

end LeanCage.Host.Snapshot
