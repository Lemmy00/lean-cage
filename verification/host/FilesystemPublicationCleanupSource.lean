import FilesystemPublicationOpening
import FilesystemStagingOpeningSource
import FilesystemPublicationContentProfile
import PublicationProofs.CleanupSource

namespace LeanCage.Host.Kernel.PublicationCleanup
open Filesystem

private theorem readonly_nondestructive {α : Type} {program : Filesystem.Program α}
    (source : Retrieval.ReadOnly program) : RequestProgram (fun request => ¬ DestructiveRequest request) program :=
  request_weaken (read_only_namespace_passive source) (fun _ => namespace_passive_not_destructive)

private theorem ensure_nondestructive (uid : Nat) (parent : UInt64) (name : ByteArray) :
    RequestProgram (fun request => ¬ DestructiveRequest request) (Directories.ensureAt uid parent name) := by
  unfold Directories.ensureAt
  apply RequestProgram.call (by simp [DestructiveRequest])
  intro reply
  dsimp only [Filesystem.Program.bind]
  repeat' first | exact .pure _ | split | exact readonly_nondestructive (Retrieval.openAt_readOnly _ _ _)

private theorem public_at_nondestructive (uid : Nat) (parent : UInt64) (name : ByteArray) (create : Bool) :
    RequestProgram (fun request => ¬ DestructiveRequest request) (Directories.publicAt uid parent name create) := by
  cases create <;> unfold Directories.publicAt
  all_goals simp only [Bool.false_eq_true, ↓reduceIte]
  · apply request_bind (readonly_nondestructive (Retrieval.openAt_readOnly _ _ _))
    intro result
    cases result with
    | error => exact .pure _
    | ok opened =>
      apply request_bind (readonly_nondestructive (Retrieval.readOnly_snapshot (Snapshot.publicHandle_input _)))
      intro allowed
      exact .pure _
  · apply request_bind (ensure_nondestructive _ _ _)
    intro result
    cases result with
    | error => exact .pure _
    | ok opened =>
      apply request_bind (readonly_nondestructive (Retrieval.readOnly_snapshot (Snapshot.publicHandle_input _)))
      intro allowed
      exact .pure _

private theorem descend_nondestructive (uid : Nat) (create : Bool) (current : Directories.Opened)
    (names : List ByteArray) :
    RequestProgram (fun request => ¬ DestructiveRequest request) (Directories.descend uid create current names) := by
  induction names generalizing current with
  | nil => exact .pure _
  | cons name rest ih =>
    unfold Directories.descend
    apply request_bind (public_at_nondestructive _ _ _ _)
    intro next
    apply request_bind (readonly_nondestructive (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _)))
    intro closed
    cases closed with
    | error =>
      cases next with
      | error => exact .pure _
      | ok => exact readonly_nondestructive (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))
    | ok => exact ih _

theorem parent_nondestructive (path : ByteArray) (create : Bool) :
    RequestProgram (fun request => ¬ DestructiveRequest request) (Directories.parent path create) := by
  unfold Directories.parent
  apply request_bind (readonly_nondestructive (Retrieval.readOnly_snapshot (Snapshot.sourceStart_input _)))
  intro selected
  cases selected with
  | error => exact .pure _
  | ok selected =>
    dsimp only
    split
    · split
      · exact readonly_nondestructive (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))
      · apply RequestProgram.call (by simp [DestructiveRequest])
        intro identity
        dsimp only [Filesystem.Program.bind]
        split
        · exact readonly_nondestructive (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))
        · apply request_bind (readonly_nondestructive (Retrieval.inspect_readOnly _ _))
          intro base
          cases base with
          | error => exact .pure _
          | ok base =>
            apply request_bind (descend_nondestructive _ _ _ _)
            intro result
            exact .pure _
    · exact readonly_nondestructive (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))

theorem fresh_nondestructive (parent : Directories.Parent) :
    RequestProgram (fun request => ¬ DestructiveRequest request) (Directories.fresh parent) := by
  unfold Directories.fresh
  apply request_bind (readonly_nondestructive (Retrieval.openAt_readOnly _ _ _))
  intro result
  cases result with
  | error => exact .pure _
  | ok container =>
    apply request_bind
    · apply request_weaken (RunDirectory.directoryChild_requests _ _ _)
      intro request allowed
      cases operation : request.op <;>
        simp_all [RunDirectory.BeforeMarkRequest, RunDirectory.DirectoryRequest, DestructiveRequest]
    · intro result
      cases result with
      | error => exact readonly_nondestructive (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))
      | ok => exact .pure _

private theorem no_unlink_last {α : Type} {program : Filesystem.Program α}
    (profile : RequestProgram (fun request => ¬ DestructiveRequest request) program)
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix program (before ++ [(request, observed)])) (unlink : request.op = .unlinkAt) : False :=
  request_prefix profile source (request, observed) (by simp) (.inl unlink)

private theorem no_unlink_request_last {α : Type} {program : Filesystem.Program α}
    (profile : RequestProgram (fun request => request.op ≠ .unlinkAt) program)
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix program (before ++ [(request, observed)])) (unlink : request.op = .unlinkAt) : False :=
  request_prefix profile source (request, observed) (by simp) unlink

private theorem pure_no_last {α : Type} (value : α) {before : List (Request × Option Reply)}
    {request : Request} {observed : Option Reply}
    (source : Prefix (.pure value) (before ++ [(request, observed)])) : False := by
  have length := congrArg List.length (Snapshot.prefix_pure_empty source)
  simp only [List.length_append, List.length_singleton, List.length_nil] at length
  omega

private theorem finish_nondestructive (parent : Directories.Parent) (stage : Directories.Fresh)
    (outcome : Outcome) (reply : Reply) :
    RequestProgram (fun request => ¬ DestructiveRequest request) (Publication.finishCommit parent stage outcome reply) := by
  unfold Publication.finishCommit Publication.closeOwned
  apply request_bind
  · repeat' first | exact .pure _ | apply RequestProgram.call (by simp [DestructiveRequest]); intro ignored
  · intro ignored
    repeat' first | exact .pure _ | split

structure Attempt (bundle : Validation.Bundle) (input : Publication.Input) (target : ByteArray)
    (stdoutHash stderrHash : ByteArray) (before : List (Request × Option Reply))
    (request : Request) (observed : Option Reply) where
  context : PublicationCreation.Staged target
  error : Failure
  preparing : List (Request × Reply)
  prepared : Returns (Publication.prepare bundle input context.display stdoutHash stderrHash context.parent context.stage)
    preparing (.error error)
  inside : List (Request × Option Reply)
  active : Prefix (Publication.cleanup context.parent context.stage input) (inside ++ [(request, observed)])
  trace : before = Publication.completed
    (context.displaying ++ context.selecting ++ context.creating ++ preparing) ++ inside

-- §FS-host-boundary.publication: Every publisher unlink belongs to the
-- actual failed-preparation cleanup before the first rename attempt. The
-- full earlier selection, creation and error transcript is retained.
theorem attempt_unlink_source (bundle : Validation.Bundle) (input : Publication.Input) (target : ByteArray)
    (stdoutHash stderrHash : ByteArray) {before : List (Request × Option Reply)}
    {request : Request} {observed : Option Reply}
    (active : Prefix (Publication.attempt bundle input target stdoutHash stderrHash)
      (before ++ [(request, observed)])) (unlink : request.op = .unlinkAt) :
    Nonempty (Attempt bundle input target stdoutHash stderrHash before request observed) := by
  unfold Publication.attempt at active
  rcases filesystem_last_bind_split _ _ active with displaying |
      ⟨displaying, result, afterDisplay, displayed, following, displayTrace⟩
  · exact False.elim (no_unlink_last (readonly_nondestructive (Retrieval.absolute_readOnly _)) displaying unlink)
  · cases result with
    | error => exact False.elim (pure_no_last _ following)
    | ok display =>
      rcases filesystem_last_bind_split _ _ following with selecting |
          ⟨selecting, result, afterSelect, selected, following, selectTrace⟩
      · exact False.elim (no_unlink_last (parent_nondestructive _ _) selecting unlink)
      · cases result with
        | error => exact False.elim (pure_no_last _ following)
        | ok parent =>
          rcases filesystem_last_bind_split _ _ following with creating |
              ⟨creating, result, afterCreate, created, following, createTrace⟩
          · exact False.elim (no_unlink_last (fresh_nondestructive _) creating unlink)
          · cases result with
            | error => exact False.elim (no_unlink_last
                (readonly_nondestructive (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))) following unlink)
            | ok stage =>
              rcases filesystem_last_bind_split _ _ following with preparing |
                  ⟨preparing, result, afterPrepare, prepared, following, prepareTrace⟩
              · exact False.elim (no_unlink_last (publication_prepare_nondestructive _ _ _ _ _ _ _) preparing unlink)
              · cases result with
                | error error =>
                  rcases filesystem_last_bind_split _ _ following with cleaning |
                      ⟨cleaning, result, afterCleanup, cleaned, following, cleanupTrace⟩
                  · exact ⟨⟨⟨⟨⟨display, displaying, displayed⟩, parent, selecting, selected⟩, stage, creating, created⟩,
                      error, preparing, prepared, afterPrepare, cleaning, by
                        simp only [displayTrace, selectTrace, createTrace, prepareTrace, Publication.completed,
                          List.map_append, List.append_assoc]⟩⟩
                  · exact False.elim (no_unlink_last
                      (readonly_nondestructive (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))) following unlink)
                | ok outcome =>
                  have profile : RequestProgram (fun request => request.op ≠ .unlinkAt)
                      (.call {
                        op := .renameNew
                        first := stage.container.fd
                        second := parent.directory.fd
                        left := stage.name
                        right := parent.name } (Publication.finishCommit parent stage outcome)) := by
                    apply RequestProgram.call (by intro impossible; cases impossible)
                    intro reply
                    apply request_weaken (finish_nondestructive _ _ _ _)
                    intro request allowed removing
                    exact allowed (.inl removing)
                  exact False.elim (no_unlink_request_last profile following unlink)

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
      (before ++ [(operation, observed)])) (unlink : operation.op = .unlinkAt) :
    ∃ target selecting inside,
      Returns (Publication.destination request bundle input.outcome.requestId) selecting (.ok target) ∧
      before = Publication.completed selecting ++ inside ∧
      Nonempty (Attempt bundle input target stdoutHash stderrHash inside operation observed) := by
  unfold identified at active
  rcases filesystem_last_bind_split _ _ active with selecting |
      ⟨selecting, result, afterSelect, selected, following, selectTrace⟩
  · exact False.elim (no_unlink_last (readonly_nondestructive (Retrieval.publicationDestination_readOnly _ _ _))
      selecting unlink)
  · cases result with
    | error => exact False.elim (pure_no_last _ following)
    | ok target =>
      rcases filesystem_last_bind_split _ _ following with attempting |
          ⟨attempting, result, afterAttempt, attempted, following, attemptTrace⟩
      · exact ⟨target, selecting, afterSelect, selected, selectTrace,
          attempt_unlink_source _ _ _ _ _ attempting unlink⟩
      · exact False.elim (pure_no_last _ following)

structure Published (request : GatewayWire.Request) (bundle : Validation.Bundle)
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
  attempt : Attempt bundle effective target stdoutHash stderrHash inside operation observed
  trace : before = Publication.completed identifying ++ Publication.completed selecting ++ inside

-- §FS-host-boundary.publication: Actual report identification, destination
-- selection and failed preparation all precede this cleanup on the same
-- publisher invocation. Identification failure retains its real invalidation.
theorem published_unlink_source (request : GatewayWire.Request) (bundle : Validation.Bundle) (input : Publication.Input)
    {before : List (Request × Option Reply)} {operation : Request} {observed : Option Reply}
    (active : Prefix (Publication.publish request bundle input) (before ++ [(operation, observed)]))
    (unlink : operation.op = .unlinkAt) : Nonempty (Published request bundle input before operation observed) := by
  unfold Publication.publish at active
  rcases filesystem_last_bind_split _ _ active with identifying |
      ⟨identifying, result, afterIdentify, identifiedRun, following, identifyTrace⟩
  · exact False.elim (no_unlink_last (readonly_nondestructive (Retrieval.identify_readOnly _)) identifying unlink)
  · cases result with
    | error error =>
      have remaining : Prefix (identified request bundle (Publication.invalidate input error.message) .empty .empty)
          (afterIdentify ++ [(operation, observed)]) := following
      obtain ⟨target, selecting, inside, selected, trace, ⟨attempt⟩⟩ := identified_site _ _ _ _ _ remaining unlink
      exact ⟨⟨.error error, Publication.invalidate input error.message, .empty, .empty, target, identifying, selecting, inside,
        identifiedRun, .inr ⟨error, rfl, rfl, rfl, rfl⟩, selected, attempt, by
          rw [identifyTrace, trace]
          simp only [List.append_assoc]⟩⟩
    | ok hashes =>
      rcases hashes with ⟨stdoutHash, stderrHash⟩
      have remaining : Prefix (identified request bundle input stdoutHash stderrHash)
          (afterIdentify ++ [(operation, observed)]) := following
      obtain ⟨target, selecting, inside, selected, trace, ⟨attempt⟩⟩ := identified_site _ _ _ _ _ remaining unlink
      exact ⟨⟨.ok (stdoutHash, stderrHash), input, stdoutHash, stderrHash, target, identifying, selecting, inside,
        identifiedRun, .inl ⟨rfl, rfl⟩, selected, attempt, by
          rw [identifyTrace, trace]
          simp only [List.append_assoc]⟩⟩

structure Host (before : List Program.Event) (operation : Request) where
  invocation : EntryPublicationCall before (.lost (.filesystem operation))
  earlier : List (Request × Option Reply)
  source : Published invocation.effective invocation.authenticated.bundle
    invocation.run.context.dispatched.input earlier operation none
  projection : invocation.run.inside = earlier.map Program.filesystemPrefixEvent

theorem host_unlink_source {before : List Program.Event} {operation : Request}
    (invocation : EntryPublicationCall before (.lost (.filesystem operation)))
    (unlink : operation.op = .unlinkAt) : Nonempty (Host before operation) := by
  obtain ⟨earlier, source, projection⟩ := selected_filesystem_source
    (request := operation) (observed := none) invocation.run.active
  obtain ⟨published⟩ := published_unlink_source _ _ _ source unlink
  exact ⟨⟨invocation, earlier, published, projection⟩⟩

private theorem prefix_bind_return {α β : Type} {program : Filesystem.Program α}
    {next : α → Filesystem.Program β} {first : List (Request × Reply)} {last : List (Request × Option Reply)}
    {value : α} (source : Returns program first value) (tail : Prefix (next value) last) :
    Prefix (program.bind next) (Publication.completed first ++ last) := by
  induction source with
  | pure => exact tail
  | call request continuation reply events value rest ih => exact .returned _ _ _ _ (ih tail)

private theorem prefix_bind_left {α β : Type} {program : Filesystem.Program α}
    {next : α → Filesystem.Program β} {events : List (Request × Option Reply)}
    (source : Prefix program events) : Prefix (program.bind next) events := by
  induction source with
  | empty => exact .empty _
  | lost request continuation => exact .lost request (fun reply => (continuation reply).bind next)
  | returned request continuation reply tail rest ih => exact .returned _ _ _ _ ih

def Host.selectingContext {before : List Program.Event} {request : Request}
    (source : Host before request) : List Program.Event :=
  source.invocation.packet.events ++ source.invocation.authenticated.events ++ source.invocation.run.context.events ++
    (source.source.identifying ++ source.source.selecting ++ source.source.attempt.context.displaying).map Program.filesystemEvent

theorem Host.cleanup_trace {before : List Program.Event} {request : Request}
    (source : Host before request) :
    before = source.selectingContext ++ source.source.attempt.context.selecting.map Program.filesystemEvent ++
      (source.source.attempt.context.creating ++ source.source.attempt.preparing).map Program.filesystemEvent ++
        source.source.attempt.inside.map Program.filesystemPrefixEvent := by
  conv =>
    lhs
    rw [source.invocation.trace, source.invocation.run.trace, source.projection, source.source.trace, source.source.attempt.trace]
  simp only [Host.selectingContext, List.map_append, completed_filesystem_events, List.append_assoc]

private theorem attempt_staging_prefix (bundle : Validation.Bundle) (input : Publication.Input)
    (stdoutHash stderrHash : ByteArray) {target : ByteArray} (selection : PublicationCreation.Selected target)
    {inside : List (Request × Option Reply)} (active : Prefix (Directories.fresh selection.parent) inside) :
    Prefix (Publication.attempt bundle input target stdoutHash stderrHash)
      (Publication.completed (selection.displaying ++ selection.selecting) ++ inside) := by
  unfold Publication.attempt
  simp only [Publication.completed, List.map_append, List.append_assoc]
  apply prefix_bind_return selection.displayed
  apply prefix_bind_return selection.selected
  exact prefix_bind_left active

private theorem publish_staging_prefix (request : GatewayWire.Request) (bundle : Validation.Bundle)
    (input effective : Publication.Input) (result : Result (ByteArray × ByteArray))
    (stdoutHash stderrHash : ByteArray) (target : ByteArray)
    {identifying selecting : List (Request × Reply)}
    (identify : Returns input.outcome.identify identifying result)
    (identity : Publication.Identification input result effective stdoutHash stderrHash)
    (chosen : Returns (Publication.destination request bundle effective.outcome.requestId) selecting (.ok target))
    {inside : List (Request × Option Reply)}
    (active : Prefix (Publication.attempt bundle effective target stdoutHash stderrHash) inside) :
    Prefix (Publication.publish request bundle input)
      (Publication.completed identifying ++ Publication.completed selecting ++ inside) := by
  unfold Publication.publish
  rw [List.append_assoc]
  rcases identity with ⟨rfl, rfl⟩ | ⟨error, rfl, rfl, rfl, rfl⟩
  all_goals
    apply prefix_bind_return identify
    apply prefix_bind_return chosen
    exact prefix_bind_left active

-- §FS-host-boundary.publication: Reconstruct the earlier source stage call from the SAME
-- cleanup's completed producer chain, including error identification and selected public parent.
def Host.staging_opening_source {before : List Program.Event} {request : Request}
    (source : Host before request) {inside : List (Request × Option Reply)} {opening : Request}
    (active : Prefix (Directories.fresh source.source.attempt.context.parent) (inside ++ [(opening, none)])) :
    StagingOpeningCall (source.selectingContext ++ source.source.attempt.context.selecting.map Program.filesystemEvent ++
      inside.map Program.filesystemPrefixEvent) opening := by
  let selection : PublicationCreation.Selected source.source.target := {
    display := source.source.attempt.context.display
    displaying := source.source.attempt.context.displaying
    displayed := source.source.attempt.context.displayed
    parent := source.source.attempt.context.parent
    selecting := source.source.attempt.context.selecting
    selected := source.source.attempt.context.selected }
  let attemptBefore := Publication.completed (selection.displaying ++ selection.selecting) ++ inside
  let allBefore := Publication.completed source.source.identifying ++ Publication.completed source.source.selecting ++ attemptBefore
  let outside := source.invocation.packet.events ++ source.invocation.authenticated.events ++ source.invocation.run.context.events
  have attempted := attempt_staging_prefix source.invocation.authenticated.bundle source.source.effective
    source.source.stdoutHash source.source.stderrHash selection active
  have published := publish_staging_prefix source.invocation.effective source.invocation.authenticated.bundle
    source.invocation.run.context.dispatched.input source.source.effective source.source.identified
    source.source.stdoutHash source.source.stderrHash source.source.target source.source.identify source.source.identity
    source.source.select attempted
  have published : Prefix (Publication.publish source.invocation.effective source.invocation.authenticated.bundle
      source.invocation.run.context.dispatched.input) (allBefore ++ [(opening, none)]) := by
    simpa only [allBefore, attemptBefore, List.append_assoc] using published
  let run : RunPublicationCall source.invocation.effective source.invocation.authenticated.bundle source.invocation.duration
      (source.invocation.run.context.events ++ allBefore.map Program.filesystemPrefixEvent) (.lost (.filesystem opening)) := {
    context := source.invocation.run.context
    inside := allBefore.map Program.filesystemPrefixEvent
    active := by
      simpa only [List.map_append, List.map_cons, List.map_nil, Program.filesystemPrefixEvent] using
        Program.lift_filesystem_prefix published
    trace := rfl }
  let invocation : EntryPublicationCall (outside ++ allBefore.map Program.filesystemPrefixEvent) (.lost (.filesystem opening)) := {
    packet := source.invocation.packet
    original := source.invocation.original
    effective := source.invocation.effective
    duration := source.invocation.duration
    accepted := source.invocation.accepted
    invocation := source.invocation.invocation
    authenticated := source.invocation.authenticated
    command := source.invocation.command
    runBefore := source.invocation.run.context.events ++ allBefore.map Program.filesystemPrefixEvent
    run
    trace := by simp only [outside, List.append_assoc] }
  have exactBefore : source.selectingContext ++ source.source.attempt.context.selecting.map Program.filesystemEvent ++
      inside.map Program.filesystemPrefixEvent = outside ++ allBefore.map Program.filesystemPrefixEvent := by
    simp only [Host.selectingContext, outside, allBefore, attemptBefore, selection,
      List.map_append, completed_filesystem_events, List.append_assoc]
  apply Eq.mpr (congrArg (fun context => StagingOpeningCall context opening) exactBefore)
  exact {
    invocation
    earlier := allBefore
    source := {
      identified := source.source.identified
      effective := source.source.effective
      stdoutHash := source.source.stdoutHash
      stderrHash := source.source.stderrHash
      target := source.source.target
      identifying := source.source.identifying
      selecting := source.source.selecting
      inside := attemptBefore
      identify := source.source.identify
      identity := source.source.identity
      select := source.source.select
      site := .staging selection inside active rfl
      trace := rfl }
    projection := rfl
    selection
    inside
    active
    trace := rfl
    classified := rfl }

end LeanCage.Host.Kernel.PublicationCleanup
