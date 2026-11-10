import PublicationProofs.Prefix

namespace LeanCage.Host.Publication

open Filesystem

def completed (events : List (Request × Reply)) : List (Request × Option Reply) :=
  events.map (fun event => (event.1, some event.2))

-- §AR-host-boundary.interfaces: A prefix stays in a call or crosses its actual return.
theorem prefix_bind_split {α β : Type} (program : Filesystem.Program α)
    (next : α → Filesystem.Program β) {events : List (Request × Option Reply)}
    (run : Prefix (program.bind next) events) :
    Prefix program events ∨ ∃ first value last,
      Returns program first value ∧ Prefix (next value) last ∧ events = completed first ++ last := by
  induction program generalizing events with
  | pure value => exact .inr ⟨[], value, events, .pure value, run, rfl⟩
  | call request rest ih =>
    change Prefix (.call request (fun reply => (rest reply).bind next)) events at run
    cases run with
    | empty => exact .inl (.empty _)
    | lost => exact .inl (.lost _ _)
    | returned _ _ reply tail run =>
      rcases ih reply run with before | after
      · exact .inl (.returned request rest reply tail before)
      · obtain ⟨first, value, last, returned, following, shape⟩ := after
        exact .inr ⟨(request, reply) :: first, value, last,
          .call request rest reply first value returned, following,
          by simpa only [completed, List.map_cons, List.cons_append] using congrArg ((request, some reply) :: ·) shape⟩

theorem safe_returns {α : Type} {program : Filesystem.Program α} {events : List (Request × Reply)} {value : α}
    (safe : SafeProgram program) (run : Returns program events value) :
    ∀ event ∈ events, SafeRequest event.1 := by
  induction run with
  | pure => simp
  | call request next reply tail value run ih =>
    cases safe with
    | call allowed following =>
      intro event member
      rcases List.mem_cons.mp member with rfl | member
      · exact allowed
      · exact ih (following reply) event member

theorem safe_no_rename {request : Request} (safe : SafeRequest request) : request.op ≠ .renameNew := by
  intro rename
  simp only [SafeRequest, rename] at safe

def HasRename (events : List (Request × Option Reply)) : Prop :=
  ∃ event ∈ events, event.1.op = .renameNew

theorem pure_no_rename {α : Type} {value : α} {events : List (Request × Option Reply)}
    (run : Prefix (.pure value) events) (renamed : HasRename events) : False := by
  have empty := Snapshot.prefix_pure_empty run
  subst events
  obtain ⟨_, member, _⟩ := renamed
  cases member

theorem safe_bind_reaches_rename {α β : Type} {program : Filesystem.Program α}
    {next : α → Filesystem.Program β} {events : List (Request × Option Reply)}
    (safe : SafeProgram program) (run : Prefix (program.bind next) events) (renamed : HasRename events) :
    ∃ first value last, Returns program first value ∧ Prefix (next value) last ∧
      events = completed first ++ last ∧ HasRename last := by
  rcases prefix_bind_split _ _ run with before | after
  · obtain ⟨event, member, rename⟩ := renamed
    exact False.elim (safe_no_rename (safe_prefix safe before event member) rename)
  · obtain ⟨first, value, last, returned, following, shape⟩ := after
    refine ⟨first, value, last, returned, following, shape, ?_⟩
    obtain ⟨event, member, rename⟩ := renamed
    rw [shape] at member
    rcases List.mem_append.mp member with before | after
    · obtain ⟨original, present, rfl⟩ := List.mem_map.mp before
      exact False.elim (safe_no_rename (safe_returns safe returned original present) rename)
    · exact ⟨event, after, rename⟩

def commitTail (parent : Directories.Parent) (stage : Directories.Fresh) (_input : Input)
    (outcome : Outcome) (renamed : Reply) : Filesystem.Program (Result Outcome) := do
  finishCommit parent stage outcome renamed

theorem commitTail_safe (parent : Directories.Parent) (stage : Directories.Fresh) (input : Input)
    (outcome : Outcome) (renamed : Reply) : SafeProgram (commitTail parent stage input outcome renamed) := by
  unfold commitTail finishCommit
  apply safe_bind (closeOwned_safe _ _)
  intro ignored
  split
  · exact .pure _
  · split <;> exact .pure _

def CommitPrefix (bundle : Validation.Bundle) (input : Input) (target : ByteArray)
    (stdoutHash stderrHash : ByteArray) (events : List (Request × Option Reply)) : Prop :=
  ∃ display parent stage candidate displaying selecting creating preparing committing,
    events = completed (displaying ++ selecting ++ creating ++ preparing) ++ committing ∧
    Returns (absolute target) displaying (.ok display) ∧
    Returns (Directories.parent target true) selecting (.ok parent) ∧
    Returns (Directories.fresh parent) creating (.ok stage) ∧
    Returns (prepare bundle input display stdoutHash stderrHash parent stage) preparing (.ok candidate) ∧
    Prefix (.call {
      op := .renameNew
      first := stage.container.fd
      second := parent.directory.fd
      left := stage.name
      right := parent.name } (commitTail parent stage input candidate)) committing

-- §FS-host-boundary.publication: Reaching commit requires the same actual prepared source prefix.
theorem attempt_commit_prefix (bundle : Validation.Bundle) (input : Input) (target : ByteArray)
    (stdoutHash stderrHash : ByteArray) {events : List (Request × Option Reply)}
    (run : Prefix (attempt bundle input target stdoutHash stderrHash) events) (renamed : HasRename events) :
    CommitPrefix bundle input target stdoutHash stderrHash events := by
  unfold attempt at run
  obtain ⟨displaying, result, rest, displayed, afterDisplay, shape, inDisplay⟩ :=
    safe_bind_reaches_rename (readOnly_safe (Retrieval.absolute_readOnly _)) run renamed
  cases result with
  | error => exact False.elim (pure_no_rename afterDisplay inDisplay)
  | ok display =>
    obtain ⟨selecting, result, later, selected, afterSelect, selectShape, inSelect⟩ :=
      safe_bind_reaches_rename (parent_safe _ _) afterDisplay inDisplay
    cases result with
    | error => exact False.elim (pure_no_rename afterSelect inSelect)
    | ok parent =>
      obtain ⟨creating, result, following, created, afterCreate, createShape, inCreate⟩ :=
        safe_bind_reaches_rename (fresh_safe _) afterSelect inSelect
      cases result with
      | error =>
        obtain ⟨event, member, rename⟩ := inCreate
        exact False.elim (safe_no_rename (safe_prefix (readOnly_safe
          (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))) afterCreate event member) rename)
      | ok stage =>
        obtain ⟨preparing, result, committing, prepared, afterPrepare, prepareShape, inPrepare⟩ :=
          safe_bind_reaches_rename (prepare_safe _ _ _ _ _ _ _) afterCreate inCreate
        cases result with
        | error error =>
          have safe : SafeProgram ((cleanup parent stage input).bind (fun _ =>
              closeResult parent.directory.fd (.error error : Result Outcome))) :=
            safe_bind (cleanup_safe parent stage input) (fun _ =>
              readOnly_safe (Retrieval.readOnly_snapshot (Snapshot.closeResult_input parent.directory.fd _)))
          obtain ⟨event, member, rename⟩ := inPrepare
          exact False.elim (safe_no_rename (safe_prefix safe afterPrepare event member) rename)
        | ok candidate =>
          refine ⟨display, parent, stage, candidate, displaying, selecting, creating, preparing, committing,
            ?_, displayed, selected, created, prepared, ?_⟩
          · simpa only [selectShape, createShape, prepareShape, completed, List.map_append,
              List.append_assoc] using shape
          · exact afterPrepare

end LeanCage.Host.Publication

namespace LeanCage.Host.Publication
open Filesystem

theorem closeOwned_readOnly (parent : Directories.Parent) (stage : Directories.Fresh) :
    Retrieval.ReadOnly (closeOwned parent stage) := by
  unfold closeOwned
  apply Retrieval.ReadOnly.call (by trivial)
  intro reply
  apply Retrieval.ReadOnly.call (by trivial)
  intro reply
  apply Retrieval.ReadOnly.call (by trivial)
  intro reply
  exact .pure _

-- §FS-host-boundary.publication: Even a native error can acknowledge a committed rename.
theorem finishCommit_readOnly (parent : Directories.Parent) (stage : Directories.Fresh)
    (outcome : Outcome) (reply : Reply) : Retrieval.ReadOnly (finishCommit parent stage outcome reply) := by
  unfold finishCommit
  apply Retrieval.readOnly_bind (closeOwned_readOnly _ _)
  intro ignored
  split
  · exact .pure _
  · split <;> exact .pure _

theorem commitTail_readOnly (parent : Directories.Parent) (stage : Directories.Fresh) (input : Input)
    (outcome : Outcome) (reply : Reply) : Retrieval.ReadOnly (commitTail parent stage input outcome reply) :=
  finishCommit_readOnly _ _ _ _

theorem nonerror_commit_readOnly (parent : Directories.Parent) (stage : Directories.Fresh) (input : Input)
    (outcome : Outcome) (reply : Reply) (nonerror : nativeError reply = false) :
    Retrieval.ReadOnly (commitTail parent stage input outcome reply) := by
  have _ := nonerror
  exact commitTail_readOnly _ _ _ _ _

-- §FS-host-boundary.publication: Every post-attempt prefix preserves commit uncertainty.
theorem finishCommit_no_rollback (parent : Directories.Parent) (stage : Directories.Fresh)
    (outcome : Outcome) (reply : Reply) {events : List (Request × Option Reply)}
    (run : Prefix (finishCommit parent stage outcome reply) events) :
    ∀ event ∈ events, event.1.op ≠ .unlinkAt ∧ event.1.op ≠ .renameNew ∧ event.1.op ≠ .write := by
  intro event member
  have allowed := Retrieval.readOnly_prefix (finishCommit_readOnly _ _ _ _) run event member
  constructor
  · intro changed; simp only [Retrieval.Allowed, changed] at allowed
  · constructor
    · intro changed; simp only [Retrieval.Allowed, changed] at allowed
    · intro changed; simp only [Retrieval.Allowed, changed] at allowed

theorem nonerror_commit_no_rollback (parent : Directories.Parent) (stage : Directories.Fresh) (input : Input)
    (outcome : Outcome) (reply : Reply) (nonerror : nativeError reply = false)
    {events : List (Request × Option Reply)}
    (run : Prefix (commitTail parent stage input outcome reply) events) :
    ∀ event ∈ events, event.1.op ≠ .unlinkAt ∧ event.1.op ≠ .renameNew ∧ event.1.op ≠ .write := by
  have _ := nonerror
  exact finishCommit_no_rollback _ _ _ _ run

end LeanCage.Host.Publication
