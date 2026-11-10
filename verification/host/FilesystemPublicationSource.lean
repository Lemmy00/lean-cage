import FilesystemSourceOrigins
import PublicationCustodyProofs

namespace LeanCage.Host.Kernel
open Filesystem

private theorem returns_as_prefix {α : Type} {program : Filesystem.Program α}
    {events : List (Request × Reply)} {value : α} (source : Returns program events value) :
    Prefix program (Publication.completed events) := by
  induction source with
  | pure => exact .empty _
  | call request next reply tail value source ih => exact .returned request next reply _ ih

-- §FS-host-boundary.acceptance: The same last request is retained across an actual helper return.
theorem filesystem_last_bind_split {α β : Type} (program : Filesystem.Program α)
    (next : α → Filesystem.Program β) {before : List (Request × Option Reply)}
    {event : Request × Option Reply} (source : Prefix (program.bind next) (before ++ [event])) :
    Prefix program (before ++ [event]) ∨ ∃ initial value inside,
      Returns program initial value ∧ Prefix (next value) (inside ++ [event]) ∧
      before = Publication.completed initial ++ inside := by
  rcases Publication.prefix_bind_split program next source with earlier |
      ⟨initial, value, last, returned, ending, shape⟩
  · exact .inl earlier
  · rcases List.eq_nil_or_concat last with empty | ⟨inside, final, finalShape⟩
    · subst last
      simp only [List.append_nil] at shape
      exact .inl (shape.symm ▸ returns_as_prefix returned)
    · rw [List.concat_eq_append] at finalShape
      subst last
      have concatenated : List.concat before event =
          List.concat (Publication.completed initial ++ inside) final := by
        simpa only [List.concat_eq_append, List.append_assoc] using shape
      have same := List.of_concat_eq_concat concatenated
      have finalSame := same.2
      subst final
      exact .inr ⟨initial, value, inside, returned, ending, same.1⟩

private theorem no_last_rename {α : Type} {program : Filesystem.Program α}
    (safe : Publication.SafeProgram program) {before : List (Request × Option Reply)}
    {event : Request × Option Reply} (active : Prefix program (before ++ [event]))
    (rename : event.1.op = .renameNew) : False :=
  Publication.safe_no_rename (Publication.safe_prefix safe active event (by simp)) rename

private theorem pure_no_last {α : Type} (value : α) (before : List (Request × Option Reply))
    (event : Request × Option Reply) : ¬ Prefix (.pure value) (before ++ [event]) := by
  intro source
  have shape := Snapshot.prefix_pure_empty source
  have length := congrArg List.length shape
  simp only [List.length_append, List.length_singleton, List.length_nil] at length
  omega

private theorem rename_call_last {α : Type} (request : Request) (next : Reply → Filesystem.Program α)
    (safe : ∀ reply, Publication.SafeProgram (next reply))
    {before : List (Request × Option Reply)} {event : Request × Option Reply}
    (active : Prefix (.call request next) (before ++ [event])) (rename : event.1.op = .renameNew) :
    before = [] ∧ event.1 = request := by
  cases before with
  | nil =>
    rcases event with ⟨operation, observed⟩
    cases observed <;> cases active <;> exact ⟨rfl, rfl⟩
  | cons first rest =>
    cases rest with
    | nil =>
      change Prefix (.call request next) [first, event] at active
      cases active with
      | returned _ _ reply events following =>
        exact False.elim (no_last_rename (safe reply) (before := []) following rename)
    | cons second rest =>
      change Prefix (.call request next) (first :: second :: (rest ++ [event])) at active
      cases active with
      | returned _ _ reply events following =>
        exact False.elim (no_last_rename (safe reply) (before := second :: rest) following rename)

structure PublicationCommitCall (bundle : Validation.Bundle) (input : Publication.Input)
    (target : ByteArray) (stdoutHash stderrHash : ByteArray)
    (before : List (Request × Option Reply)) (request : Request) where
  display : ByteArray
  parent : Directories.Parent
  stage : Directories.Fresh
  candidate : Outcome
  displaying : List (Request × Reply)
  selecting : List (Request × Reply)
  creating : List (Request × Reply)
  preparing : List (Request × Reply)
  displayed : Returns (Publication.absolute target) displaying (.ok display)
  selected : Returns (Directories.parent target true) selecting (.ok parent)
  created : Returns (Directories.fresh parent) creating (.ok stage)
  prepared : Returns (Publication.prepare bundle input display stdoutHash stderrHash parent stage)
    preparing (.ok candidate)
  trace : before = Publication.completed (displaying ++ selecting ++ creating ++ preparing)
  operation : request = {
    op := .renameNew
    first := stage.container.fd
    second := parent.directory.fd
    left := stage.name
    right := parent.name }

-- §FS-host-boundary.publication: Even a lost commit has the real marker-before-rename producer.
theorem attempt_commit_call (bundle : Validation.Bundle) (input : Publication.Input) (target : ByteArray)
    (stdoutHash stderrHash : ByteArray) {before : List (Request × Option Reply)}
    {request : Request} {observed : Option Reply}
    (active : Prefix (Publication.attempt bundle input target stdoutHash stderrHash) (before ++ [(request, observed)]))
    (rename : request.op = .renameNew) :
    Nonempty (PublicationCommitCall bundle input target stdoutHash stderrHash before request) := by
  unfold Publication.attempt at active
  rcases filesystem_last_bind_split _ _ active with displaying |
      ⟨displaying, displayResult, afterDisplay, displayed, rest, displayShape⟩
  · exact False.elim (no_last_rename (Publication.readOnly_safe (Retrieval.absolute_readOnly _)) displaying rename)
  · cases displayResult with
    | error error => exact False.elim (pure_no_last _ _ _ rest)
    | ok display =>
      rcases filesystem_last_bind_split _ _ rest with selecting |
          ⟨selecting, parentResult, afterSelect, selected, rest, selectShape⟩
      · exact False.elim (no_last_rename (Publication.parent_safe _ _) selecting rename)
      · cases parentResult with
        | error error => exact False.elim (pure_no_last _ _ _ rest)
        | ok parent =>
          rcases filesystem_last_bind_split _ _ rest with creating |
              ⟨creating, stageResult, afterCreate, created, rest, createShape⟩
          · exact False.elim (no_last_rename (Publication.fresh_safe _) creating rename)
          · cases stageResult with
            | error error => exact False.elim (no_last_rename (Publication.readOnly_safe
                (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))) rest rename)
            | ok stage =>
              rcases filesystem_last_bind_split _ _ rest with preparing |
                  ⟨preparing, preparedResult, afterPrepare, prepared, rest, prepareShape⟩
              · exact False.elim (no_last_rename (Publication.prepare_safe _ _ _ _ _ _ _) preparing rename)
              · cases preparedResult with
                | error error =>
                  have safe : Publication.SafeProgram ((Publication.cleanup parent stage input).bind
                      (fun _ => closeResult parent.directory.fd (.error error : Result Outcome))) :=
                    Publication.safe_bind (Publication.cleanup_safe _ _ _) (fun _ => Publication.readOnly_safe
                      (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _)))
                  exact False.elim (no_last_rename safe rest rename)
                | ok candidate =>
                  have callSource : Prefix (.call {
                      op := .renameNew
                      first := stage.container.fd
                      second := parent.directory.fd
                      left := stage.name
                      right := parent.name } (Publication.commitTail parent stage input candidate))
                      (afterPrepare ++ [(request, observed)]) := rest
                  obtain ⟨rfl, sameRequest⟩ := rename_call_last _ _
                    (Publication.commitTail_safe _ _ _ _) callSource rename
                  refine ⟨⟨display, parent, stage, candidate, displaying, selecting, creating, preparing,
                    displayed, selected, created, prepared, ?_, sameRequest⟩⟩
                  simp only [displayShape, selectShape, createShape, prepareShape, List.append_nil,
                    Publication.completed, List.map_append, List.append_assoc]

private def afterIdentification (request : GatewayWire.Request) (bundle : Validation.Bundle)
    (input : Publication.Input) (stdoutHash stderrHash : ByteArray) : Filesystem.Program Publication.Output := do
  let target ← Publication.destination request bundle input.outcome.requestId
  let published ← match target with
    | .error error => pure (.error error)
    | .ok target => Publication.attempt bundle input target stdoutHash stderrHash
  let outcome := match published with
    | .ok outcome => outcome
    | .error error => input.outcome.storageFailure error.message
  return ⟨outcome, outcome.metadata stdoutHash stderrHash⟩

private theorem identified_commit_call (request : GatewayWire.Request) (bundle : Validation.Bundle)
    (input : Publication.Input) (stdoutHash stderrHash : ByteArray)
    {before : List (Request × Option Reply)} {operation : Request} {observed : Option Reply}
    (active : Prefix (afterIdentification request bundle input stdoutHash stderrHash)
      (before ++ [(operation, observed)])) (rename : operation.op = .renameNew) :
    ∃ target selecting inside,
      Returns (Publication.destination request bundle input.outcome.requestId) selecting (.ok target) ∧
      before = Publication.completed selecting ++ inside ∧
      Nonempty (PublicationCommitCall bundle input target stdoutHash stderrHash inside operation) := by
  unfold afterIdentification at active
  rcases filesystem_last_bind_split _ _ active with selecting |
      ⟨selecting, targetResult, afterSelect, selected, rest, selectShape⟩
  · exact False.elim (no_last_rename (Publication.readOnly_safe
      (Retrieval.publicationDestination_readOnly _ _ _)) selecting rename)
  · cases targetResult with
    | error error => exact False.elim (pure_no_last _ _ _ rest)
    | ok target =>
      rcases filesystem_last_bind_split _ _ rest with publishing |
          ⟨publishing, result, afterPublish, published, last, publishShape⟩
      · exact ⟨target, selecting, afterSelect, selected, selectShape,
          attempt_commit_call _ _ _ _ _ publishing rename⟩
      · exact False.elim (pure_no_last _ _ _ last)

structure PublishedCommitCall (request : GatewayWire.Request) (bundle : Validation.Bundle)
    (input : Publication.Input) (before : List (Request × Option Reply)) (operation : Request) where
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
  commit : PublicationCommitCall bundle effective target stdoutHash stderrHash inside operation
  trace : before = Publication.completed identifying ++ Publication.completed selecting ++ inside

-- §FS-host-boundary.publication: Error, partial and lost commits use the same actual fresh stage.
theorem publish_commit_call (request : GatewayWire.Request) (bundle : Validation.Bundle) (input : Publication.Input)
    {before : List (Request × Option Reply)} {operation : Request} {observed : Option Reply}
    (active : Prefix (Publication.publish request bundle input) (before ++ [(operation, observed)]))
    (rename : operation.op = .renameNew) : Nonempty (PublishedCommitCall request bundle input before operation) := by
  unfold Publication.publish at active
  rcases filesystem_last_bind_split _ _ active with identifying |
      ⟨identifying, identified, afterIdentify, identifiedRun, rest, identifyShape⟩
  · exact False.elim (no_last_rename (Publication.readOnly_safe (Retrieval.identify_readOnly _)) identifying rename)
  · cases identified with
    | error error =>
      have remaining : Prefix (afterIdentification request bundle (Publication.invalidate input error.message) .empty .empty)
          (afterIdentify ++ [(operation, observed)]) := rest
      obtain ⟨target, selecting, inside, selected, shape, ⟨commit⟩⟩ :=
        identified_commit_call _ _ _ _ _ remaining rename
      exact ⟨⟨.error error, Publication.invalidate input error.message, .empty, .empty, target,
        identifying, selecting, inside, identifiedRun, .inr ⟨error, rfl, rfl, rfl, rfl⟩,
        selected, commit, by rw [identifyShape, shape]; simp only [List.append_assoc]⟩⟩
    | ok hashes =>
      rcases hashes with ⟨stdoutHash, stderrHash⟩
      have remaining : Prefix (afterIdentification request bundle input stdoutHash stderrHash)
          (afterIdentify ++ [(operation, observed)]) := rest
      obtain ⟨target, selecting, inside, selected, shape, ⟨commit⟩⟩ :=
        identified_commit_call _ _ _ _ _ remaining rename
      exact ⟨⟨.ok (stdoutHash, stderrHash), input, stdoutHash, stderrHash, target,
        identifying, selecting, inside, identifiedRun, .inl ⟨rfl, rfl⟩,
        selected, commit, by rw [identifyShape, shape]; simp only [List.append_assoc]⟩⟩

structure HostCommitCall (before : List Program.Event) (operation : Request) (observed : Option Reply) where
  invocation : EntryPublicationCall before (Program.filesystemPrefixEvent (operation, observed))
  earlier : List (Request × Option Reply)
  source : PublishedCommitCall invocation.effective invocation.authenticated.bundle
    invocation.run.context.dispatched.input earlier operation
  projection : invocation.run.inside = earlier.map Program.filesystemPrefixEvent

-- §FS-host-boundary.publication: Parent/stage/key preparation comes from the maintained caller.
theorem entrypoint_commit_call {before : List Program.Event} {operation : Request} {observed : Option Reply}
    (active : Program.Prefix Entrypoint.run (before ++ [Program.filesystemPrefixEvent (operation, observed)]))
    (rename : operation.op = .renameNew) : Nonempty (HostCommitCall before operation observed) := by
  obtain ⟨invocation⟩ := entrypoint_rename_publication active rename
  obtain ⟨earlier, source, projection⟩ := selected_filesystem_source invocation.run.active
  obtain ⟨commit⟩ := publish_commit_call _ _ _ source rename
  exact ⟨⟨invocation, earlier, commit, projection⟩⟩

-- §FS-host-boundary.acceptance: No independently selected publication receipt enters this join.
theorem selected_publisher_commit {kernel : Contract} {runtime : ActorRuntime kernel}
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply}
    (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) (rename : request.op = .renameNew) :
    Nonempty (HostCommitCall engine.events request observed) :=
  entrypoint_commit_call (selected_source_prefix journal selected action present) rename

end LeanCage.Host.Kernel
