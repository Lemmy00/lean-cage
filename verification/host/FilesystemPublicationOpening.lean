import FilesystemRunOpeningSource
import FilesystemStagingParents

namespace LeanCage.Host.Kernel.PublicationOpening
open Filesystem

private theorem no_open_last {α : Type} {program : Filesystem.Program α}
    (profile : RequestProgram (fun request => request.op ≠ .openAt) program)
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix program (before ++ [(request, observed)])) (opening : request.op = .openAt) : False :=
  request_prefix profile source (request, observed) (by simp) opening

private theorem pure_no_last {α : Type} (value : α) {before : List (Request × Option Reply)}
    {event : Request × Option Reply} (source : Prefix (.pure value) (before ++ [event])) : False := by
  have length := congrArg List.length (Snapshot.prefix_pure_empty source)
  simp only [List.length_append, List.length_singleton, List.length_nil] at length
  omega

private theorem hash_no_open (bytes : ByteArray) :
    RequestProgram (fun request => request.op ≠ .openAt) (Filesystem.hash bytes) := by
  unfold Filesystem.hash
  apply RequestProgram.call (by intro invalid; cases invalid)
  intro reply
  split <;> exact .pure _

private theorem identify_no_open (outcome : Outcome) :
    RequestProgram (fun request => request.op ≠ .openAt) outcome.identify := by
  unfold Outcome.identify
  split
  · exact .pure _
  · apply request_bind (hash_no_open _)
    intro result
    cases result with
    | error => exact .pure _
    | ok digest =>
      apply request_bind (hash_no_open _)
      intro result
      cases result <;> exact .pure _

private theorem display_no_open (target : ByteArray) :
    RequestProgram (fun request => request.op ≠ .openAt) (Publication.absolute target) := by
  unfold Publication.absolute
  repeat' first
    | exact .pure _
    | dsimp only [Filesystem.Program.bind]
    | split
    | apply RequestProgram.call (by intro invalid; cases invalid); intro reply

private theorem finish_no_open (parent : Directories.Parent) (stage : Directories.Fresh)
    (outcome : Outcome) (reply : Reply) :
    RequestProgram (fun request => request.op ≠ .openAt) (Publication.finishCommit parent stage outcome reply) := by
  unfold Publication.finishCommit Publication.closeOwned
  apply request_bind
  · repeat' first
      | exact .pure _
      | apply RequestProgram.call (by intro invalid; cases invalid); intro reply
  · intro ignored
    repeat' first | exact .pure _ | split

-- §FS-host-boundary.ownership: Every actual attempt open retains the same completed
-- selection/stage prefix. Failure cleanup is a separate branch before any rename attempt.
inductive AttemptSite (bundle : Validation.Bundle) (input : Publication.Input) (target : ByteArray)
    (stdoutHash stderrHash : ByteArray) (before : List (Request × Option Reply))
    (request : Request) (observed : Option Reply) : Type where
  | selecting (context : PublicationCreation.Displayed target) (inside : List (Request × Option Reply))
      (active : Prefix (Directories.parent target true) (inside ++ [(request, observed)]))
      (trace : before = Publication.completed context.displaying ++ inside)
  | staging (context : PublicationCreation.Selected target) (inside : List (Request × Option Reply))
      (active : Prefix (Directories.fresh context.parent) (inside ++ [(request, observed)]))
      (trace : before = Publication.completed (context.displaying ++ context.selecting) ++ inside)
  | filling (context : PublicationCreation.Staged target) (inside : List (Request × Option Reply))
      (active : Prefix (Publication.prepare bundle input context.display stdoutHash stderrHash
        context.parent context.stage) (inside ++ [(request, observed)]))
      (trace : before = Publication.completed
        (context.displaying ++ context.selecting ++ context.creating) ++ inside)
  | cleaning (context : PublicationCreation.Staged target) (error : Failure)
      (preparing : List (Request × Reply))
      (prepared : Returns (Publication.prepare bundle input context.display stdoutHash stderrHash
        context.parent context.stage) preparing (.error error))
      (inside : List (Request × Option Reply))
      (active : Prefix (Publication.cleanup context.parent context.stage input) (inside ++ [(request, observed)]))
      (trace : before = Publication.completed
        (context.displaying ++ context.selecting ++ context.creating ++ preparing) ++ inside)

theorem attempt_opening_site (bundle : Validation.Bundle) (input : Publication.Input) (target : ByteArray)
    (stdoutHash stderrHash : ByteArray) {before : List (Request × Option Reply)}
    {request : Request} {observed : Option Reply}
    (active : Prefix (Publication.attempt bundle input target stdoutHash stderrHash)
      (before ++ [(request, observed)])) (opening : request.op = .openAt) :
    Nonempty (AttemptSite bundle input target stdoutHash stderrHash before request observed) := by
  unfold Publication.attempt at active
  rcases filesystem_last_bind_split _ _ active with displaying |
      ⟨displaying, result, afterDisplay, displayed, following, displayTrace⟩
  · exact False.elim (no_open_last (display_no_open _) displaying opening)
  · cases result with
    | error => exact False.elim (pure_no_last _ following)
    | ok display =>
      rcases filesystem_last_bind_split _ _ following with selecting |
          ⟨selecting, result, afterSelect, selected, following, selectTrace⟩
      · exact ⟨.selecting ⟨display, displaying, displayed⟩ afterDisplay selecting displayTrace⟩
      · cases result with
        | error => exact False.elim (pure_no_last _ following)
        | ok parent =>
          rcases filesystem_last_bind_split _ _ following with creating |
              ⟨creating, result, afterCreate, created, following, createTrace⟩
          · exact ⟨.staging ⟨⟨display, displaying, displayed⟩, parent, selecting, selected⟩ afterSelect creating (by
              simp only [displayTrace, selectTrace, Publication.completed, List.map_append, List.append_assoc])⟩
          · cases result with
            | error => exact False.elim (no_open_last
                (RequestProgram.call (by intro invalid; cases invalid) (fun _ => .pure _)) following opening)
            | ok stage =>
              rcases filesystem_last_bind_split _ _ following with preparing |
                  ⟨preparing, result, afterPrepare, prepared, following, prepareTrace⟩
              · exact ⟨.filling ⟨⟨⟨display, displaying, displayed⟩, parent, selecting, selected⟩,
                  stage, creating, created⟩ afterCreate preparing (by
                  simp only [displayTrace, selectTrace, createTrace, Publication.completed,
                    List.map_append, List.append_assoc])⟩
              · cases result with
                | error error =>
                  rcases filesystem_last_bind_split _ _ following with cleaning |
                      ⟨cleaning, result, last, cleaned, remaining, cleanupTrace⟩
                  · exact ⟨.cleaning ⟨⟨⟨display, displaying, displayed⟩, parent, selecting, selected⟩,
                      stage, creating, created⟩ error preparing prepared afterPrepare cleaning (by
                      simp only [displayTrace, selectTrace, createTrace, prepareTrace, Publication.completed,
                        List.map_append, List.append_assoc])⟩
                  · exact False.elim (no_open_last
                      (RequestProgram.call (by intro invalid; cases invalid) (fun _ => .pure _)) remaining opening)
                | ok outcome =>
                  apply False.elim
                  apply no_open_last (program := _) ?_ following opening
                  apply RequestProgram.call (by intro invalid; cases invalid)
                  intro reply
                  exact finish_no_open _ _ _ _

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
      (before ++ [(operation, observed)])) (opening : operation.op = .openAt) :
    ∃ target selecting inside,
      Returns (Publication.destination request bundle input.outcome.requestId) selecting (.ok target) ∧
      before = Publication.completed selecting ++ inside ∧
      Nonempty (AttemptSite bundle input target stdoutHash stderrHash inside operation observed) := by
  unfold identified at active
  rcases filesystem_last_bind_split _ _ active with selecting |
      ⟨selecting, result, afterSelect, selected, following, selectTrace⟩
  · unfold Publication.destination at selecting
    dsimp only at selecting
    split at selecting <;> exact False.elim (pure_no_last _ selecting)
  · cases result with
    | error => exact False.elim (pure_no_last _ following)
    | ok target =>
      rcases filesystem_last_bind_split _ _ following with attempting |
          ⟨attempting, result, afterAttempt, attempted, following, attemptTrace⟩
      · exact ⟨target, selecting, afterSelect, selected, selectTrace,
          attempt_opening_site _ _ _ _ _ attempting opening⟩
      · exact False.elim (pure_no_last _ following)

-- §FS-host-boundary.publication: This producer preserves real identification errors and
-- every open phase of the maintained publisher, including its precommit cleanup source.
theorem publish_opening_site (request : GatewayWire.Request) (bundle : Validation.Bundle) (input : Publication.Input)
    {before : List (Request × Option Reply)} {operation : Request} {observed : Option Reply}
    (active : Prefix (Publication.publish request bundle input) (before ++ [(operation, observed)]))
    (opening : operation.op = .openAt) : Nonempty (PublishedSite request bundle input before operation observed) := by
  unfold Publication.publish at active
  rcases filesystem_last_bind_split _ _ active with identifying |
      ⟨identifying, result, afterIdentify, identifiedRun, following, identifyTrace⟩
  · exact False.elim (no_open_last (identify_no_open _) identifying opening)
  · cases result with
    | error error =>
      have remaining : Prefix (identified request bundle (Publication.invalidate input error.message) .empty .empty)
          (afterIdentify ++ [(operation, observed)]) := following
      obtain ⟨target, selecting, inside, selected, trace, ⟨site⟩⟩ := identified_site _ _ _ _ _ remaining opening
      exact ⟨⟨.error error, Publication.invalidate input error.message, .empty, .empty, target,
        identifying, selecting, inside, identifiedRun, .inr ⟨error, rfl, rfl, rfl, rfl⟩, selected, site,
        by rw [identifyTrace, trace]; simp only [List.append_assoc]⟩⟩
    | ok hashes =>
      rcases hashes with ⟨stdoutHash, stderrHash⟩
      have remaining : Prefix (identified request bundle input stdoutHash stderrHash)
          (afterIdentify ++ [(operation, observed)]) := following
      obtain ⟨target, selecting, inside, selected, trace, ⟨site⟩⟩ := identified_site _ _ _ _ _ remaining opening
      exact ⟨⟨.ok (stdoutHash, stderrHash), input, stdoutHash, stderrHash, target,
        identifying, selecting, inside, identifiedRun, .inl ⟨rfl, rfl⟩, selected, site,
        by rw [identifyTrace, trace]; simp only [List.append_assoc]⟩⟩

structure HostSite (before : List Program.Event) (operation : Request) where
  invocation : EntryPublicationCall before (.lost (.filesystem operation))
  earlier : List (Request × Option Reply)
  source : PublishedSite invocation.effective invocation.authenticated.bundle
    invocation.run.context.dispatched.input earlier operation none
  projection : invocation.run.inside = earlier.map Program.filesystemPrefixEvent

-- §AR-host-boundary.interfaces: This is the actual same outer publisher source cut,
-- with all earlier packet/authentication/run events retained rather than chosen anew.
theorem host_opening_site {before : List Program.Event} {operation : Request}
    (invocation : EntryPublicationCall before (.lost (.filesystem operation)))
    (opening : operation.op = .openAt) : Nonempty (HostSite before operation) := by
  obtain ⟨earlier, source, projection⟩ := selected_filesystem_source
    (request := operation) (observed := none) invocation.run.active
  obtain ⟨site⟩ := publish_opening_site _ _ _ source opening
  exact ⟨⟨invocation, earlier, site, projection⟩⟩

end LeanCage.Host.Kernel.PublicationOpening
