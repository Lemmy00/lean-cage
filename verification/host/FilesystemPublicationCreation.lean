import FilesystemMkdirOrigins
import FilesystemParentTraversal

namespace LeanCage.Host.Kernel.PublicationCreation
open Filesystem

private theorem readOnly {α : Type} {program : Filesystem.Program α}
    (source : Retrieval.ReadOnly program) : RequestProgram NoMkdir program := by
  induction source with
  | pure => exact .pure _
  | call allowed following ih =>
    apply RequestProgram.call _ ih
    intro mkdir
    unfold Retrieval.Allowed at allowed
    rw [mkdir] at allowed
    exact allowed

private theorem impossible {α : Type} {program : Filesystem.Program α}
    (profile : RequestProgram NoMkdir program)
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix program (before ++ [(request, observed)])) (mkdir : request.op = .mkdirAt) : False :=
  request_prefix profile source (request, observed) (by simp) mkdir

private theorem pure_last {α : Type} (value : α) {before : List (Request × Option Reply)}
    {request : Request} {observed : Option Reply}
    (source : Prefix (.pure value) (before ++ [(request, observed)])) : False := by
  have length := congrArg List.length (Snapshot.prefix_pure_empty source)
  simp only [List.length_append, List.length_singleton, List.length_nil] at length
  omega

theorem under_no_mkdir {α : Type} (uid : Nat) (root : UInt64) (names : List String)
    (action : UInt64 → Filesystem.Program (Result α))
    (permitted : ∀ fd, RequestProgram NoMkdir (action fd)) :
    RequestProgram NoMkdir (Publication.under uid root names false action) := by
  induction names generalizing root with
  | nil => exact permitted root
  | cons name rest ih =>
    unfold Publication.under
    split
    · exact .pure _
    · simp only [Bool.false_eq_true, ↓reduceIte]
      apply request_bind (readOnly (Retrieval.openAt_readOnly _ _ _))
      intro opened
      cases opened with
      | error => exact .pure _
      | ok child =>
        apply request_bind (ih child.fd)
        intro result
        exact readOnly (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))

theorem unlink_relative_no_mkdir (uid : Nat) (root : UInt64) (names : List String) (directory : Bool) :
    RequestProgram NoMkdir (Publication.unlinkRelative uid root names directory) := by
  unfold Publication.unlinkRelative
  split
  · apply request_bind (under_no_mkdir _ _ _ _ (by
      intro fd
      apply RequestProgram.call (by change Op.unlinkAt ≠ Op.mkdirAt; decide)
      intro reply
      dsimp only [Filesystem.Program.bind]
      split <;> exact .pure _))
    intro ignored
    exact .pure _
  · exact .pure _

private theorem cleanup_footer (stage : Directories.Fresh) : RequestProgram NoMkdir (do
    for name in ["policy.json", "boot.log", "vm-report.json", "stdout", "stderr",
        "stored-report.json", "export.manifest", "result.json", "publication.wire"] do
      let _ ← Filesystem.Program.effect {op := .unlinkAt, first := stage.directory.fd, left := name.toUTF8}
    let _ ← Filesystem.Program.effect {
      op := .unlinkAt, first := stage.directory.fd, second := 512, left := "export".toUTF8 }
    let _ ← Filesystem.Program.effect {op := .close, first := stage.directory.fd}
    let _ ← Filesystem.Program.effect {
      op := .unlinkAt, first := stage.container.fd, second := 512, left := stage.name }
    let _ ← Filesystem.Program.effect {op := .close, first := stage.container.fd}
    pure ()) := by
  apply request_bind
  · apply request_forIn
    intro name member state
    apply RequestProgram.call (by change Op.unlinkAt ≠ Op.mkdirAt; decide)
    intro reply
    exact .pure _
  · intro finished
    apply RequestProgram.call (by change Op.unlinkAt ≠ Op.mkdirAt; decide)
    intro reply
    apply RequestProgram.call (by change Op.close ≠ Op.mkdirAt; decide)
    intro reply
    apply RequestProgram.call (by change Op.unlinkAt ≠ Op.mkdirAt; decide)
    intro reply
    apply RequestProgram.call (by change Op.close ≠ Op.mkdirAt; decide)
    intro reply
    exact .pure _

-- §FS-host-boundary.ownership: Pre-commit failure cleanup traverses without creating names.
-- Its real failed opens, unlinks, closes and lost prefixes remain in this source profile.
theorem cleanup_no_mkdir (parent : Directories.Parent) (stage : Directories.Fresh) (input : Publication.Input) :
    RequestProgram NoMkdir (Publication.cleanup parent stage input) := by
  unfold Publication.cleanup
  apply request_bind (readOnly (Retrieval.openAt_readOnly _ _ _))
  intro opened
  dsimp only
  split
  · apply request_bind
    · apply request_forIn
      intro file member state
      apply request_bind (unlink_relative_no_mkdir _ _ _ _)
      intro ignored
      exact .pure _
    · intro finished
      apply request_bind
      · apply request_forIn
        intro path member state
        apply request_bind (unlink_relative_no_mkdir _ _ _ _)
        intro ignored
        exact .pure _
      · intro finished
        apply RequestProgram.call (by change Op.close ≠ Op.mkdirAt; decide)
        intro reply
        exact cleanup_footer _
  · exact cleanup_footer _

private theorem finish_no_mkdir (parent : Directories.Parent) (stage : Directories.Fresh)
    (outcome : Outcome) (renamed : Reply) :
    RequestProgram NoMkdir (Publication.finishCommit parent stage outcome renamed) := by
  unfold Publication.finishCommit Publication.closeOwned
  apply request_bind
  · apply RequestProgram.call (by change Op.close ≠ Op.mkdirAt; decide)
    intro reply
    apply RequestProgram.call (by change Op.close ≠ Op.mkdirAt; decide)
    intro reply
    apply RequestProgram.call (by change Op.close ≠ Op.mkdirAt; decide)
    intro reply
    exact .pure _
  · intro ignored
    split
    · exact .pure _
    · split <;> exact .pure _

structure Displayed (target : ByteArray) where
  display : ByteArray
  displaying : List (Request × Reply)
  displayed : Returns (Publication.absolute target) displaying (.ok display)

structure Selected (target : ByteArray) extends Displayed target where
  parent : Directories.Parent
  selecting : List (Request × Reply)
  selected : Returns (Directories.parent target true) selecting (.ok parent)

structure Staged (target : ByteArray) extends Selected target where
  stage : Directories.Fresh
  creating : List (Request × Reply)
  created : Returns (Directories.fresh parent) creating (.ok stage)

-- §FS-host-boundary.ownership: This classification retains the exact caller selection and
-- actual previous replies. Only the reserved staging branch is a new private-root producer.
inductive AttemptSite (bundle : Validation.Bundle) (input : Publication.Input) (target : ByteArray)
    (stdoutHash stderrHash : ByteArray) (before : List (Request × Option Reply))
    (request : Request) (observed : Option Reply) : Type where
  | selecting (context : Displayed target) (inside : List (Request × Option Reply))
      (cursor : ParentTraversal.ParentMkdir target true inside request)
      (trace : before = Publication.completed context.displaying ++ inside)
  | staging (context : Selected target) (inside : List (Request × Option Reply))
      (child : FreshChildCall context.parent inside request)
      (trace : before = Publication.completed (context.displaying ++ context.selecting) ++ inside)
  | filling (context : Staged target) (inside : List (Request × Option Reply))
      (source : Prefix (Publication.prepare bundle input context.display stdoutHash stderrHash
        context.parent context.stage) (inside ++ [(request, observed)]))
      (trace : before = Publication.completed
        (context.displaying ++ context.selecting ++ context.creating) ++ inside)

theorem attempt_mkdir_site (bundle : Validation.Bundle) (input : Publication.Input) (target : ByteArray)
    (stdoutHash stderrHash : ByteArray) {before : List (Request × Option Reply)}
    {request : Request} {observed : Option Reply}
    (active : Prefix (Publication.attempt bundle input target stdoutHash stderrHash)
      (before ++ [(request, observed)])) (mkdir : request.op = .mkdirAt) :
    Nonempty (AttemptSite bundle input target stdoutHash stderrHash before request observed) := by
  unfold Publication.attempt at active
  rcases filesystem_last_bind_split _ _ active with displaying |
      ⟨displaying, result, afterDisplay, displayed, following, displayTrace⟩
  · exact False.elim (impossible (readOnly (Retrieval.absolute_readOnly _)) displaying mkdir)
  · cases result with
    | error error => exact False.elim (pure_last _ following)
    | ok display =>
      rcases filesystem_last_bind_split _ _ following with selecting |
          ⟨selecting, result, afterSelect, selected, following, selectTrace⟩
      · obtain ⟨cursor⟩ := ParentTraversal.parent_mkdir_cursor target true selecting mkdir
        exact ⟨.selecting ⟨display, displaying, displayed⟩ afterDisplay cursor displayTrace⟩
      · cases result with
        | error error => exact False.elim (pure_last _ following)
        | ok parent =>
          rcases filesystem_last_bind_split _ _ following with creating |
              ⟨creating, result, afterCreate, created, following, createTrace⟩
          · obtain ⟨child⟩ := actual_fresh_child_call parent creating mkdir
            exact ⟨.staging ⟨⟨display, displaying, displayed⟩, parent, selecting, selected⟩ afterSelect child (by
              simp only [displayTrace, selectTrace, Publication.completed, List.map_append, List.append_assoc])⟩
          · cases result with
            | error error => exact False.elim (impossible
                (readOnly (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))) following mkdir)
            | ok stage =>
              rcases filesystem_last_bind_split _ _ following with preparing |
                  ⟨preparing, result, afterPrepare, prepared, following, prepareTrace⟩
              · exact ⟨.filling ⟨⟨⟨display, displaying, displayed⟩, parent, selecting, selected⟩,
                  stage, creating, created⟩ afterCreate preparing (by
                  simp only [displayTrace, selectTrace, createTrace, Publication.completed,
                    List.map_append, List.append_assoc])⟩
              · cases result with
                | error error =>
                  have profile := request_bind (cleanup_no_mkdir parent stage input) (fun _ =>
                    readOnly (Retrieval.readOnly_snapshot (Snapshot.closeResult_input parent.directory.fd
                      (.error error : Result Outcome))))
                  exact False.elim (impossible profile following mkdir)
                | ok outcome =>
                  have profile : RequestProgram NoMkdir (.call {
                      op := .renameNew, first := stage.container.fd, second := parent.directory.fd,
                      left := stage.name, right := parent.name } (Publication.commitTail parent stage input outcome)) := by
                    apply RequestProgram.call (by change Op.renameNew ≠ Op.mkdirAt; decide)
                    intro renamed
                    exact finish_no_mkdir parent stage outcome renamed
                  exact False.elim (impossible profile following mkdir)

private def identified (request : GatewayWire.Request) (bundle : Validation.Bundle)
    (input : Publication.Input) (stdoutHash stderrHash : ByteArray) : Filesystem.Program Publication.Output := do
  let target ← Publication.destination request bundle input.outcome.requestId
  let published ← match target with
    | .error error => pure (.error error)
    | .ok target => Publication.attempt bundle input target stdoutHash stderrHash
  let outcome := match published with
    | .ok outcome => outcome
    | .error error => input.outcome.storageFailure error.message
  return ⟨outcome, outcome.metadata stdoutHash stderrHash⟩

private theorem identified_site (request : GatewayWire.Request) (bundle : Validation.Bundle)
    (input : Publication.Input) (stdoutHash stderrHash : ByteArray)
    {before : List (Request × Option Reply)} {operation : Request} {observed : Option Reply}
    (active : Prefix (identified request bundle input stdoutHash stderrHash)
      (before ++ [(operation, observed)])) (mkdir : operation.op = .mkdirAt) :
    ∃ target selecting inside,
      Returns (Publication.destination request bundle input.outcome.requestId) selecting (.ok target) ∧
      before = Publication.completed selecting ++ inside ∧
      Nonempty (AttemptSite bundle input target stdoutHash stderrHash inside operation observed) := by
  unfold identified at active
  rcases filesystem_last_bind_split _ _ active with selecting |
      ⟨selecting, result, afterSelect, selected, following, selectTrace⟩
  · exact False.elim (impossible (readOnly (Retrieval.publicationDestination_readOnly _ _ _)) selecting mkdir)
  · cases result with
    | error error => exact False.elim (pure_last _ following)
    | ok target =>
      rcases filesystem_last_bind_split _ _ following with attempting |
          ⟨attempting, result, afterAttempt, attempted, following, attemptTrace⟩
      · exact ⟨target, selecting, afterSelect, selected, selectTrace, attempt_mkdir_site _ _ _ _ _ attempting mkdir⟩
      · exact False.elim (pure_last _ following)

structure PublishedSite (request : GatewayWire.Request) (bundle : Validation.Bundle)
    (input : Publication.Input) (before : List (Request × Option Reply))
    (operation : Request) (observed : Option Reply) where
  identified : Result (ByteArray × ByteArray)
  effective : Publication.Input
  stdoutHash : ByteArray
  stderrHash : ByteArray
  target : ByteArray
  identifying : List (Request × Reply)
  selecting : List (Request × Reply)
  inside : List (Request × Option Reply)
  identify : Returns input.outcome.identify identifying identified
  identity : Publication.Identification input identified effective stdoutHash stderrHash
  select : Returns (Publication.destination request bundle effective.outcome.requestId) selecting (.ok target)
  site : AttemptSite bundle effective target stdoutHash stderrHash inside operation observed
  trace : before = Publication.completed identifying ++ Publication.completed selecting ++ inside

-- §FS-host-boundary.ownership: The public publisher consumes the actual recognized report
-- and output selection; failures during identification keep their real invalidated input.
theorem publish_mkdir_site (request : GatewayWire.Request) (bundle : Validation.Bundle) (input : Publication.Input)
    {before : List (Request × Option Reply)} {operation : Request} {observed : Option Reply}
    (active : Prefix (Publication.publish request bundle input) (before ++ [(operation, observed)]))
    (mkdir : operation.op = .mkdirAt) : Nonempty (PublishedSite request bundle input before operation observed) := by
  unfold Publication.publish at active
  rcases filesystem_last_bind_split _ _ active with identifying |
      ⟨identifying, result, afterIdentify, identifiedRun, following, identifyTrace⟩
  · exact False.elim (impossible (readOnly (Retrieval.identify_readOnly _)) identifying mkdir)
  · cases result with
    | error error =>
      have remaining : Prefix (identified request bundle (Publication.invalidate input error.message) .empty .empty)
          (afterIdentify ++ [(operation, observed)]) := following
      obtain ⟨target, selecting, inside, selected, trace, ⟨site⟩⟩ := identified_site _ _ _ _ _ remaining mkdir
      exact ⟨⟨.error error, Publication.invalidate input error.message, .empty, .empty, target,
        identifying, selecting, inside, identifiedRun, .inr ⟨error, rfl, rfl, rfl, rfl⟩, selected, site,
        by rw [identifyTrace, trace]; simp only [List.append_assoc]⟩⟩
    | ok hashes =>
      rcases hashes with ⟨stdoutHash, stderrHash⟩
      have remaining : Prefix (identified request bundle input stdoutHash stderrHash)
          (afterIdentify ++ [(operation, observed)]) := following
      obtain ⟨target, selecting, inside, selected, trace, ⟨site⟩⟩ := identified_site _ _ _ _ _ remaining mkdir
      exact ⟨⟨.ok (stdoutHash, stderrHash), input, stdoutHash, stderrHash, target, identifying, selecting, inside,
        identifiedRun, .inl ⟨rfl, rfl⟩, selected, site,
        by rw [identifyTrace, trace]; simp only [List.append_assoc]⟩⟩

structure HostSite (before : List Program.Event) (operation : Request) (observed : Option Reply) where
  invocation : EntryPublicationCall before (Program.filesystemPrefixEvent (operation, observed))
  earlier : List (Request × Option Reply)
  source : PublishedSite invocation.effective invocation.authenticated.bundle
    invocation.run.context.dispatched.input earlier operation observed
  projection : invocation.run.inside = earlier.map Program.filesystemPrefixEvent

theorem host_mkdir_site {before : List Program.Event} {operation : Request} {observed : Option Reply}
    (invocation : EntryPublicationCall before (Program.filesystemPrefixEvent (operation, observed)))
    (mkdir : operation.op = .mkdirAt) : Nonempty (HostSite before operation observed) := by
  obtain ⟨earlier, source, projection⟩ := selected_filesystem_source invocation.run.active
  obtain ⟨site⟩ := publish_mkdir_site _ _ _ source mkdir
  exact ⟨⟨invocation, earlier, site, projection⟩⟩

end LeanCage.Host.Kernel.PublicationCreation
