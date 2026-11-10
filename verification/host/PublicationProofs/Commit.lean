import PublicationProofs.Creation
import PublicationProofs.Prepare

namespace LeanCage.Host.Publication

open Filesystem

def OwnedCloses (parent : Directories.Parent) (stage : Directories.Fresh)
    (events : List (Request × Reply)) : Prop :=
  ∃ first second third,
    events = [({op := .close, first := stage.directory.fd}, first),
      ({op := .close, first := stage.container.fd}, second),
      ({op := .close, first := parent.directory.fd}, third)]

theorem closeOwned_source (parent : Directories.Parent) (stage : Directories.Fresh)
    {events : List (Request × Reply)} (run : Returns (closeOwned parent stage) events ()) :
    OwnedCloses parent stage events := by
  unfold closeOwned at run
  obtain ⟨first, rest, rfl, afterFirst⟩ := Snapshot.returns_call_split run
  dsimp only [Filesystem.Program.bind] at afterFirst
  obtain ⟨second, last, rfl, afterSecond⟩ := Snapshot.returns_call_split afterFirst
  dsimp only [Filesystem.Program.bind] at afterSecond
  obtain ⟨third, finalEvents, rfl, final⟩ := Snapshot.returns_call_split afterSecond
  obtain ⟨rfl, _⟩ := Snapshot.returns_pure_eq final
  exact ⟨first, second, third, rfl⟩

def CommittedObservation (bundle : Validation.Bundle) (input : Input) (target : ByteArray)
    (stdoutHash stderrHash : ByteArray) (events : List (Request × Reply)) (outcome : Outcome) : Prop :=
  ∃ display parent stage displaying selecting creating preparing renamed closing,
    events = displaying ++ selecting ++ creating ++ preparing ++ [({
      op := .renameNew
      first := stage.container.fd
      second := parent.directory.fd
      left := stage.name
      right := parent.name }, renamed)] ++ closing ∧
    Returns (absolute target) displaying (.ok display) ∧ Retrieval.ParentObservation target true selecting parent ∧
    FreshObservation parent creating stage ∧
    PreparedObservation bundle input display stdoutHash stderrHash parent stage preparing outcome ∧
    renamed.1 = 0 ∧ renamed.2 = .empty ∧ OwnedCloses parent stage closing

-- §FS-host-boundary.publication: Marker preparation precedes the real nonreplacement commit.
theorem attempt_source (bundle : Validation.Bundle) (input : Input) (target : ByteArray)
    (stdoutHash stderrHash : ByteArray) {events : List (Request × Reply)} {outcome : Outcome}
    (run : Returns (attempt bundle input target stdoutHash stderrHash) events (.ok outcome)) :
    CommittedObservation bundle input target stdoutHash stderrHash events outcome := by
  unfold attempt at run
  obtain ⟨displaying, result, rest, displayed, afterDisplay, shape⟩ := Snapshot.returns_bind_split _ _ run
  cases result with
  | error => cases afterDisplay
  | ok display =>
    obtain ⟨selecting, result, later, selected, afterSelect, selectShape⟩ :=
      Snapshot.returns_bind_split _ _ afterDisplay
    cases result with
    | error => cases afterSelect
    | ok parent =>
      obtain ⟨creating, result, following, created, afterCreate, createShape⟩ :=
        Snapshot.returns_bind_split _ _ afterSelect
      cases result with
      | error => have impossible := (Snapshot.closeResult_provenance _ _ afterCreate).1; cases impossible
      | ok stage =>
        obtain ⟨preparing, result, committing, prepared, afterPrepare, prepareShape⟩ :=
          Snapshot.returns_bind_split _ _ afterCreate
        cases result with
        | error error =>
          obtain ⟨_, _, _, _, closed, _⟩ := Snapshot.returns_bind_split _ _ afterPrepare
          have impossible := (Snapshot.closeResult_provenance _ _ closed).1
          cases impossible
        | ok candidate =>
          obtain ⟨renamed, afterEvents, rfl, afterRename⟩ := Snapshot.returns_call_split afterPrepare
          dsimp only [Filesystem.Program.bind] at afterRename
          unfold finishCommit at afterRename
          obtain ⟨closing, closeValue, last, closed, final, closeShape⟩ :=
            Snapshot.returns_bind_split _ _ afterRename
          cases closeValue
          split at final
          · rename_i committed
            obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq final
            cases same
            have fields : renamed.1 = 0 ∧ renamed.2.isEmpty = true := by simpa using committed
            refine ⟨display, parent, stage, displaying, selecting, creating, preparing, renamed, closing,
              ?_, displayed, Retrieval.parent_source _ _ selected, fresh_source _ created,
              prepare_source _ _ _ _ _ _ _ prepared, fields.1, ?_, closeOwned_source _ _ closed⟩
            · simpa only [selectShape, createShape, prepareShape, closeShape, List.append_nil,
                List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using shape
            · exact ByteArray.size_eq_zero_iff.mp
                (by simpa only [ByteArray.isEmpty, beq_iff_eq] using fields.2)
          · split at final <;> cases final

theorem attempt_report (bundle : Validation.Bundle) (input : Input) (target : ByteArray)
    (stdoutHash stderrHash : ByteArray) {events : List (Request × Reply)} {outcome : Outcome}
    (run : Returns (attempt bundle input target stdoutHash stderrHash) events (.ok outcome)) :
    outcome.report = input.outcome.report := by
  obtain ⟨display, _, _, _, _, _, _, _, _, _, _, _, _, prepared, _⟩ :=
    attempt_source _ _ _ _ _ run
  rw [prepared.1]
  rfl

end LeanCage.Host.Publication
