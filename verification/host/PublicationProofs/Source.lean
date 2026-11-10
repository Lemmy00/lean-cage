import PublicationProofs.Content
import PublicationProofs.Exports
import PublicationProofs.Reporting
import PublicationProofs.Cuts

namespace LeanCage.Host.Publication
open Filesystem

def Identification (input : Input) (result : Result (ByteArray × ByteArray)) (effective : Input)
    (stdoutHash stderrHash : ByteArray) : Prop :=
  (result = .ok (stdoutHash, stderrHash) ∧ effective = input) ∨
    ∃ error, result = .error error ∧ effective = invalidate input error.message ∧
      stdoutHash = .empty ∧ stderrHash = .empty

def StoredPublicationObservation (request : GatewayWire.Request) (bundle : Validation.Bundle) (input : Input)
    (events : List (Request × Reply)) (output : Output) : Prop :=
  ∃ identified effective stdoutHash stderrHash target identifying selecting publishing,
    events = identifying ++ selecting ++ publishing ∧
    Returns input.outcome.identify identifying identified ∧
    Identification input identified effective stdoutHash stderrHash ∧
    Returns (destination request bundle effective.outcome.requestId) selecting (.ok target) ∧
    CommittedObservation bundle effective target stdoutHash stderrHash publishing output.outcome ∧
    output.metadata = output.outcome.metadata stdoutHash stderrHash

-- §FS-host-boundary.publication: The actual public publisher consumes its same derived content.
theorem publish_stored_source (request : GatewayWire.Request) (bundle : Validation.Bundle) (input : Input)
    {events : List (Request × Reply)} {output : Output} (run : Returns (publish request bundle input) events output)
    (stored : output.outcome.publication = "stored") :
    StoredPublicationObservation request bundle input events output := by
  unfold publish at run
  obtain ⟨identifying, identified, rest, identifiedRun, afterIdentify, shape⟩ := Snapshot.returns_bind_split _ _ run
  cases identified with
  | error hashError =>
    obtain ⟨selecting, target, later, selected, afterTarget, targetShape⟩ :=
      Snapshot.returns_bind_split _ _ afterIdentify
    cases target with
    | error error =>
      obtain ⟨_, same⟩ := Snapshot.returns_pure_eq afterTarget
      cases same
      exact False.elim ((by decide : ("failed" : String) ≠ "stored") stored)
    | ok target =>
      obtain ⟨publishing, published, last, attempted, final, publishShape⟩ :=
        Snapshot.returns_bind_split _ _ afterTarget
      obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq final
      cases same
      cases published with
      | error => exact False.elim ((by decide : ("failed" : String) ≠ "stored") stored)
      | ok outcome =>
        refine ⟨.error hashError, invalidate input hashError.message, .empty, .empty, target,
          identifying, selecting, publishing, ?_, identifiedRun, .inr ⟨hashError, rfl, rfl, rfl, rfl⟩,
          selected, attempt_source bundle (invalidate input hashError.message) target .empty .empty attempted, rfl⟩
        simpa only [targetShape, publishShape, List.append_nil, List.append_assoc] using shape
  | ok hashes =>
    rcases hashes with ⟨stdoutHash, stderrHash⟩
    obtain ⟨selecting, target, later, selected, afterTarget, targetShape⟩ :=
      Snapshot.returns_bind_split _ _ afterIdentify
    cases target with
    | error error =>
      obtain ⟨_, same⟩ := Snapshot.returns_pure_eq afterTarget
      cases same
      exact False.elim ((by decide : ("failed" : String) ≠ "stored") stored)
    | ok target =>
      obtain ⟨publishing, published, last, attempted, final, publishShape⟩ :=
        Snapshot.returns_bind_split _ _ afterTarget
      obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq final
      cases same
      cases published with
      | error => exact False.elim ((by decide : ("failed" : String) ≠ "stored") stored)
      | ok outcome =>
        refine ⟨.ok (stdoutHash, stderrHash), input, stdoutHash, stderrHash, target,
          identifying, selecting, publishing, ?_, identifiedRun, .inl ⟨rfl, rfl⟩,
          selected, attempt_source bundle input target stdoutHash stderrHash attempted, rfl⟩
        simpa only [targetShape, publishShape, List.append_nil, List.append_assoc] using shape

-- §FS-host-boundary.publication: Each emitted file has the same source plan and relative write.
theorem exports_file_source (uid : Nat) (stage : UInt64) (input : Input)
    {events : List (Request × Reply)} (run : Returns (exports uid stage input) events (.ok ())) :
    ∀ file ∈ input.outcome.files, ∃ root writing,
      RelativeWrite uid root file writing ∧ ∀ event ∈ writing, event ∈ events := by
  obtain ⟨made, root, opening, making, writing, closing, shape, _, _, _, _, traced, _⟩ :=
    exports_source _ _ _ run
  intro file member
  obtain ⟨selected, called, included⟩ := actionTrace_member traced file member
  exact ⟨root.fd, selected, writeRelative_source _ _ _ called, by
    intro event member
    rw [shape]
    simp [included event member]⟩

end LeanCage.Host.Publication

namespace LeanCage.Host.Publication
open Filesystem

-- §FS-host-boundary.publication: Returned exports are written below this invocation's fresh stage.
theorem published_files_source (request : GatewayWire.Request) (bundle : Validation.Bundle) (input : Input)
    {events : List (Request × Reply)} {output : Output} (run : Returns (publish request bundle input) events output)
    (stored : output.outcome.publication = "stored") :
    ∀ file ∈ output.outcome.files, ∃ parent stage root creating opening writing,
      FreshObservation parent creating stage ∧
      Retrieval.DirectoryOpening parent.uid stage.directory.fd "export".toUTF8 opening root ∧
      RelativeWrite parent.uid root.fd file writing ∧
      (∀ event ∈ creating, event ∈ events) ∧ (∀ event ∈ opening, event ∈ events) ∧
      (∀ event ∈ writing, event ∈ events) := by
  obtain ⟨identified, effective, stdoutHash, stderrHash, target, identifying, selecting, publishing,
    fullShape, identifiedRun, chosen, selected, committed, sameMetadata⟩ := publish_stored_source _ _ _ run stored
  obtain ⟨display, parent, stage, displaying, parents, creating, preparing, renamed, closing,
    commitShape, displayed, parentSource, fresh, prepared, commitAck⟩ := committed
  obtain ⟨same, policyDigest, json, tag, hashing, authenticating, filling, marked, prepared⟩ := prepared
  dsimp only at prepared
  obtain ⟨prepareShape, hashed, rendered, jsonBound, wireBound, authenticated, filled, markerAck⟩ := prepared
  obtain ⟨files, writing, exporting, plan, fillShape, standardWrites, exported⟩ := fill_source _ _ _ _ _ filled
  obtain ⟨made, root, opening, making, fileWriting, exportClose, exportShape, madeAck, madeEmpty,
    exportRoot, madeDirs, written, closed⟩ := exports_source _ _ _ exported
  intro file member
  have original : file ∈ (stagedInput effective display).outcome.files := by
    simpa only [same, stagedInput, candidate] using member
  obtain ⟨selected, called, included⟩ := actionTrace_member written file original
  refine ⟨parent, stage, root, creating, opening, selected, fresh, exportRoot,
    writeRelative_source _ _ _ called, ?_, ?_, ?_⟩
  · intro event member
    rw [fullShape, commitShape]
    simp [member]
  · intro event member
    rw [fullShape, commitShape, prepareShape, fillShape, exportShape]
    simp [member]
  · intro event member
    rw [fullShape, commitShape, prepareShape, fillShape, exportShape]
    simp [included event member]

end LeanCage.Host.Publication
