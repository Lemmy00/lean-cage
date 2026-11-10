import PublicationMarkerProofs.Effects
import FilesystemPublicationSource

namespace LeanCage.Host.Publication
open Filesystem

private theorem no_attribute_last {α : Type} {program : Filesystem.Program α}
    (profile : RequestProgram NoAttribute program) {before : List (Request × Option Reply)}
    {event : Request × Option Reply} (source : Prefix program (before ++ [event]))
    (marked : event.1.op = .setAttribute) : False :=
  request_prefix profile source event (by simp) marked

private theorem pure_no_last {α : Type} (value : α) (before : List (Request × Option Reply))
    (event : Request × Option Reply) : ¬ Prefix (.pure value) (before ++ [event]) := by
  intro source
  have shape := Snapshot.prefix_pure_empty source
  have length := congrArg List.length shape
  simp only [List.length_append, List.length_singleton, List.length_nil] at length
  omega

private theorem attribute_call_last {α : Type} (request : Request) (next : Reply → Filesystem.Program α)
    (profile : ∀ reply, RequestProgram NoAttribute (next reply))
    {before : List (Request × Option Reply)} {event : Request × Option Reply}
    (source : Prefix (.call request next) (before ++ [event]))
    (marked : event.1.op = .setAttribute) : before = [] ∧ event.1 = request := by
  cases before with
  | nil =>
    rcases event with ⟨operation, observed⟩
    cases observed <;> cases source <;> exact ⟨rfl, rfl⟩
  | cons first rest =>
    cases rest with
    | nil =>
      change Prefix (.call request next) [first, event] at source
      cases source with
      | returned _ _ reply events following =>
        exact False.elim (no_attribute_last (profile reply) (before := []) following marked)
    | cons second rest =>
      change Prefix (.call request next) (first :: second :: (rest ++ [event])) at source
      cases source with
      | returned _ _ reply events following =>
        exact False.elim (no_attribute_last (profile reply) (before := second :: rest) following marked)

def markerWire (input : Input) (target stdoutHash stderrHash policyDigest : ByteArray)
    (parent : Directories.Parent) (stage : Directories.Fresh) : ByteArray :=
  GatewayWire.encodeResponse 0 (envelope (stagedInput input target)
    ((candidate input target).metadata stdoutHash stderrHash) policyDigest parent stage)

structure PreparedMarkerCall (bundle : Validation.Bundle) (input : Input) (target : ByteArray)
    (stdoutHash stderrHash : ByteArray) (parent : Directories.Parent) (stage : Directories.Fresh)
    (before : List (Request × Option Reply)) (request : Request) where
  policyDigest : ByteArray
  json : ByteArray
  tag : ByteArray
  hashing : List (Request × Reply)
  authenticating : List (Request × Reply)
  filling : List (Request × Reply)
  hashed : Returns (Filesystem.hash input.policy.raw) hashing (.ok policyDigest)
  rendered : WireJson.render GatewayWire.valueDepthMax ((candidate input target).metadata stdoutHash stderrHash) =
    .ok json
  jsonBound : json.size ≤ metadataMax
  wireBound : (markerWire input target stdoutHash stderrHash policyDigest parent stage).size ≤ metadataMax
  authenticated : Returns (authenticate bundle (markerWire input target stdoutHash stderrHash policyDigest parent stage))
    authenticating (.ok tag)
  filled : Returns (fill parent.uid stage.directory.fd (stagedInput input target)
    (json ++ "\n".toUTF8) (markerWire input target stdoutHash stderrHash policyDigest parent stage)) filling (.ok ())
  trace : before = completed (hashing ++ authenticating ++ filling)
  operation : request = {
    op := .setAttribute
    first := stage.directory.fd
    left := attributeName
    right := marker tag }

-- §FS-host-boundary.publication: Possible tag exposure includes errors and loss at the marker call.
theorem prepare_marker_call (bundle : Validation.Bundle) (input : Input) (target : ByteArray)
    (stdoutHash stderrHash : ByteArray) (parent : Directories.Parent) (stage : Directories.Fresh)
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (active : Prefix (prepare bundle input target stdoutHash stderrHash parent stage)
      (before ++ [(request, observed)])) (marked : request.op = .setAttribute) :
    Nonempty (PreparedMarkerCall bundle input target stdoutHash stderrHash parent stage before request) := by
  unfold prepare at active
  rcases Kernel.filesystem_last_bind_split _ _ active with hashing |
      ⟨hashing, hashResult, afterHash, hashed, rest, hashShape⟩
  · exact False.elim (no_attribute_last (readOnly_no_attribute
      (Retrieval.readOnly_snapshot (Snapshot.hash_input _))) hashing marked)
  · cases hashResult with
    | error => exact False.elim (pure_no_last _ _ _ rest)
    | ok policyDigest =>
      dsimp only at rest
      split at rest
      · rename_i json rendered
        split at rest
        · exact False.elim (pure_no_last _ _ _ rest)
        · rename_i bounded
          rcases Kernel.filesystem_last_bind_split _ _ rest with authenticating |
              ⟨authenticating, authResult, afterAuth, authenticated, rest, authShape⟩
          · exact False.elim (no_attribute_last (readOnly_no_attribute
              (Retrieval.authenticate_readOnly _ _)) authenticating marked)
          · cases authResult with
            | error => exact False.elim (pure_no_last _ _ _ rest)
            | ok tag =>
              dsimp only at rest
              rcases Kernel.filesystem_last_bind_split _ _ rest with filling |
                  ⟨filling, fillResult, afterFill, filled, rest, fillShape⟩
              · exact False.elim (no_attribute_last (fill_no_attribute _ _ _ _ _) filling marked)
              · cases fillResult with
                | error => exact False.elim (pure_no_last _ _ _ rest)
                | ok filledValue =>
                  cases filledValue
                  obtain ⟨rfl, sameRequest⟩ := attribute_call_last _ _ (fun _ => by
                    dsimp only [Filesystem.Program.bind]
                    split <;> exact .pure _) rest marked
                  have bounds : json.size ≤ metadataMax ∧
                      (markerWire input target stdoutHash stderrHash policyDigest parent stage).size ≤
                        metadataMax := by
                    simpa only [markerWire, stagedInput, candidate, Bool.or_eq_true, decide_eq_true_eq,
                      not_or, Nat.not_lt] using bounded
                  refine ⟨⟨policyDigest, json, tag, hashing, authenticating, filling, hashed,
                    rendered, bounds.1, bounds.2, authenticated, filled, ?_, sameRequest⟩⟩
                  simp only [hashShape, authShape, fillShape, List.append_nil, completed,
                    List.map_append, List.append_assoc]
      · exact False.elim (pure_no_last _ _ _ rest)

structure AttemptMarkerCall (bundle : Validation.Bundle) (input : Input) (target : ByteArray)
    (stdoutHash stderrHash : ByteArray) (before : List (Request × Option Reply)) (request : Request) where
  display : ByteArray
  parent : Directories.Parent
  stage : Directories.Fresh
  displaying : List (Request × Reply)
  selecting : List (Request × Reply)
  creating : List (Request × Reply)
  inside : List (Request × Option Reply)
  displayed : Returns (absolute target) displaying (.ok display)
  selected : Returns (Directories.parent target true) selecting (.ok parent)
  created : Returns (Directories.fresh parent) creating (.ok stage)
  marker : PreparedMarkerCall bundle input display stdoutHash stderrHash parent stage inside request
  trace : before = completed (displaying ++ selecting ++ creating) ++ inside

-- §FS-host-boundary.publication: The marker uses this actual retained parent and fresh stage.
theorem attempt_marker_call (bundle : Validation.Bundle) (input : Input) (target : ByteArray)
    (stdoutHash stderrHash : ByteArray) {before : List (Request × Option Reply)}
    {request : Request} {observed : Option Reply}
    (active : Prefix (attempt bundle input target stdoutHash stderrHash) (before ++ [(request, observed)]))
    (marked : request.op = .setAttribute) :
    Nonempty (AttemptMarkerCall bundle input target stdoutHash stderrHash before request) := by
  unfold attempt at active
  rcases Kernel.filesystem_last_bind_split _ _ active with displaying |
      ⟨displaying, displayResult, afterDisplay, displayed, rest, displayShape⟩
  · exact False.elim (no_attribute_last (readOnly_no_attribute (Retrieval.absolute_readOnly _)) displaying marked)
  · cases displayResult with
    | error => exact False.elim (pure_no_last _ _ _ rest)
    | ok display =>
      rcases Kernel.filesystem_last_bind_split _ _ rest with selecting |
          ⟨selecting, parentResult, afterSelect, selected, rest, selectShape⟩
      · exact False.elim (no_attribute_last (parent_no_attribute _ _) selecting marked)
      · cases parentResult with
        | error => exact False.elim (pure_no_last _ _ _ rest)
        | ok parent =>
          rcases Kernel.filesystem_last_bind_split _ _ rest with creating |
              ⟨creating, stageResult, afterCreate, created, rest, createShape⟩
          · exact False.elim (no_attribute_last (fresh_no_attribute _) creating marked)
          · cases stageResult with
            | error => exact False.elim (no_attribute_last (readOnly_no_attribute
                (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))) rest marked)
            | ok stage =>
              rcases Kernel.filesystem_last_bind_split _ _ rest with preparing |
                  ⟨preparing, preparedResult, afterPrepare, prepared, rest, prepareShape⟩
              · obtain ⟨marker⟩ := prepare_marker_call _ _ _ _ _ _ _ preparing marked
                exact ⟨⟨display, parent, stage, displaying, selecting, creating, afterCreate,
                  displayed, selected, created, marker, by
                    simp only [displayShape, selectShape, createShape, completed,
                      List.map_append, List.append_assoc]⟩⟩
              · cases preparedResult with
                | error error =>
                  exact False.elim (no_attribute_last (request_bind (cleanup_no_attribute _ _ _)
                    (fun _ => readOnly_no_attribute
                      (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _)))) rest marked)
                | ok outcome =>
                  have profile : RequestProgram NoAttribute (.call {
                      op := .renameNew
                      first := stage.container.fd
                      second := parent.directory.fd
                      left := stage.name
                      right := parent.name } (fun reply => finishCommit parent stage outcome reply)) := by
                    apply RequestProgram.call (by change Op.renameNew ≠ Op.setAttribute; decide)
                    intro reply
                    exact readOnly_no_attribute (finishCommit_readOnly _ _ _ _)
                  exact False.elim (no_attribute_last profile rest marked)

private def afterIdentification (request : GatewayWire.Request) (bundle : Validation.Bundle)
    (input : Input) (stdoutHash stderrHash : ByteArray) : Filesystem.Program Output := do
  let target ← destination request bundle input.outcome.requestId
  let published ← match target with
    | .error error => pure (.error error)
    | .ok target => attempt bundle input target stdoutHash stderrHash
  let outcome := match published with
    | .ok outcome => outcome
    | .error error => input.outcome.storageFailure error.message
  return ⟨outcome, outcome.metadata stdoutHash stderrHash⟩

private theorem identified_marker_call (request : GatewayWire.Request) (bundle : Validation.Bundle)
    (input : Input) (stdoutHash stderrHash : ByteArray)
    {before : List (Request × Option Reply)} {operation : Request} {observed : Option Reply}
    (active : Prefix (afterIdentification request bundle input stdoutHash stderrHash)
      (before ++ [(operation, observed)])) (marked : operation.op = .setAttribute) :
    ∃ target selecting inside,
      Returns (destination request bundle input.outcome.requestId) selecting (.ok target) ∧
      before = completed selecting ++ inside ∧
      Nonempty (AttemptMarkerCall bundle input target stdoutHash stderrHash inside operation) := by
  unfold afterIdentification at active
  rcases Kernel.filesystem_last_bind_split _ _ active with selecting |
      ⟨selecting, targetResult, afterSelect, selected, rest, selectShape⟩
  · exact False.elim (no_attribute_last (readOnly_no_attribute
      (Retrieval.publicationDestination_readOnly _ _ _)) selecting marked)
  · cases targetResult with
    | error => exact False.elim (pure_no_last _ _ _ rest)
    | ok target =>
      rcases Kernel.filesystem_last_bind_split _ _ rest with publishing |
          ⟨publishing, result, afterPublish, published, last, publishShape⟩
      · exact ⟨target, selecting, afterSelect, selected, selectShape,
          attempt_marker_call _ _ _ _ _ publishing marked⟩
      · exact False.elim (pure_no_last _ _ _ last)

structure PublishedMarkerCall (request : GatewayWire.Request) (bundle : Validation.Bundle)
    (input : Input) (before : List (Request × Option Reply)) (operation : Request) where
  identified : Result (ByteArray × ByteArray)
  effective : Input
  stdoutHash : ByteArray
  stderrHash : ByteArray
  target : ByteArray
  identifying : List (Request × Reply)
  selecting : List (Request × Reply)
  inside : List (Request × Option Reply)
  identify : Returns input.outcome.identify identifying identified
  identity : Identification input identified effective stdoutHash stderrHash
  select : Returns (destination request bundle effective.outcome.requestId) selecting (.ok target)
  source : AttemptMarkerCall bundle effective target stdoutHash stderrHash inside operation
  trace : before = completed identifying ++ completed selecting ++ inside

-- §FS-host-boundary.publication: Only actual publishers expose tags; verification stays read-only.
theorem publish_marker_call (request : GatewayWire.Request) (bundle : Validation.Bundle) (input : Input)
    {before : List (Request × Option Reply)} {operation : Request} {observed : Option Reply}
    (active : Prefix (publish request bundle input) (before ++ [(operation, observed)]))
    (marked : operation.op = .setAttribute) : Nonempty (PublishedMarkerCall request bundle input before operation) := by
  unfold publish at active
  rcases Kernel.filesystem_last_bind_split _ _ active with identifying |
      ⟨identifying, identified, afterIdentify, identifiedRun, rest, identifyShape⟩
  · exact False.elim (no_attribute_last (readOnly_no_attribute (Retrieval.identify_readOnly _)) identifying marked)
  · cases identified with
    | error error =>
      have remaining : Prefix (afterIdentification request bundle (invalidate input error.message) .empty .empty)
          (afterIdentify ++ [(operation, observed)]) := rest
      obtain ⟨target, selecting, inside, selected, shape, ⟨source⟩⟩ :=
        identified_marker_call _ _ _ _ _ remaining marked
      exact ⟨⟨.error error, invalidate input error.message, .empty, .empty, target,
        identifying, selecting, inside, identifiedRun, .inr ⟨error, rfl, rfl, rfl, rfl⟩,
        selected, source, by rw [identifyShape, shape]; simp only [List.append_assoc]⟩⟩
    | ok hashes =>
      rcases hashes with ⟨stdoutHash, stderrHash⟩
      have remaining : Prefix (afterIdentification request bundle input stdoutHash stderrHash)
          (afterIdentify ++ [(operation, observed)]) := rest
      obtain ⟨target, selecting, inside, selected, shape, ⟨source⟩⟩ :=
        identified_marker_call _ _ _ _ _ remaining marked
      exact ⟨⟨.ok (stdoutHash, stderrHash), input, stdoutHash, stderrHash, target,
        identifying, selecting, inside, identifiedRun, .inl ⟨rfl, rfl⟩,
        selected, source, by rw [identifyShape, shape]; simp only [List.append_assoc]⟩⟩

end LeanCage.Host.Publication
