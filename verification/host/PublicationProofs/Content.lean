import PublicationProofs.Files

namespace LeanCage.Host.Publication

open Filesystem

def contentFiles (input : Input) (json wire : ByteArray) : Result (List (String × ByteArray)) :=
  if json.size > metadataMax || wire.size > metadataMax || input.policy.raw.size > reportMax ||
      input.boot.size > 4 * 1024 * 1024 then .error "publication metadata exceeds its bound"
  else
    let finish := fun files =>
      let files := if input.outcome.status == "complete" then
        let files := files ++ [("stdout", input.outcome.stdout), ("stderr", input.outcome.stderr)]
        let files := match input.validated.bind (·.stored) with
          | some stored => files ++ [("stored-report.json", stored)]
          | none => files
        match input.validated.bind (·.manifest) with
        | some manifest => files ++ [("export.manifest", manifest)]
        | none => files
      else files
      .ok (files ++ [("result.json", json), ("publication.wire", wire)])
    let files := [("policy.json", input.policy.raw), ("boot.log", input.boot)]
    match input.rawReport with
    | some raw =>
      if raw.size > reportMax then .error "publication report exceeds its bound"
      else finish (files ++ [("vm-report.json", raw)])
    | none => finish files

def fileBody (stage : UInt64) (pair : String × ByteArray) (_state : Option (Result Unit) × Unit) :
    Filesystem.Program (ForInStep (Option (Result Unit) × Unit)) :=
  do
    let written ← writeNew stage pair.1.toUTF8 pair.2
    match written with
    | .error error => pure (.done (some (.error error), ()))
    | _ => pure (.yield (none, ()))

def contentThen (stage : UInt64) (files : List (String × ByteArray))
    (next : Filesystem.Program (Result Unit)) : Filesystem.Program (Result Unit) := do
  let state ← forIn files (none, ()) (fileBody stage)
  match state.1 with
  | some result => pure result
  | none => next

private theorem content_loop_equation (stage : UInt64) (files : List (String × ByteArray))
    (next : Filesystem.Program (Result Unit)) :
    (do
      for (name, bytes) in files do
        let written ← writeNew stage name.toUTF8 bytes
        if let .error error := written then return .error error
      next) = contentThen stage files next := by
  unfold contentThen
  congr 1
  funext state
  rcases state with ⟨result, ignored⟩
  cases result <;> rfl

-- §AR-host-boundary.interfaces: This equation checks the adapter against the maintained program.
theorem fill_content (uid : Nat) (stage : UInt64) (input : Input) (json wire : ByteArray) :
    fill uid stage input json wire =
      match contentFiles input json wire with
      | .error error => pure (.error error)
      | .ok files => contentThen stage files (exports uid stage input) := by
  cases raw : input.rawReport <;>
    cases stored : input.validated.bind (·.stored) <;>
      cases manifest : input.validated.bind (·.manifest) <;>
        cases complete : input.outcome.status == "complete"
  all_goals
    unfold fill contentFiles
    simp only [raw, stored, manifest, complete]
    repeat' first | contradiction | rfl | exact content_loop_equation _ _ _ | (dsimp only; split) | split

inductive FileWrites (stage : UInt64) : List (String × ByteArray) → List (Request × Reply) → Prop where
  | empty : FileWrites stage [] []
  | next (name : String) (bytes : ByteArray) (rest : List (String × ByteArray))
      (writing following : List (Request × Reply))
      (written : NewFileWrite stage name.toUTF8 bytes 384 writing)
      (tail : FileWrites stage rest following) :
      FileWrites stage ((name, bytes) :: rest) (writing ++ following)

private theorem fileLoop_cases (stage : UInt64) {files : List (String × ByteArray)}
    {before after : Option (Result Unit) × Unit} {events : List (Request × Reply)}
    (run : ForInTrace (fileBody stage) files before events after) (initial : before.1 = none) :
    (after.1 = none ∧ FileWrites stage files events) ∨ ∃ error, after.1 = some (.error error) := by
  induction run with
  | empty state => exact .inl ⟨initial, .empty⟩
  | done pair rest before after events step =>
    cases pair with
    | mk name bytes =>
      unfold fileBody at step
      obtain ⟨writing, result, last, written, final, shape⟩ := Snapshot.returns_bind_split _ _ step
      cases result with
      | error error =>
        obtain ⟨_, same⟩ := Snapshot.returns_pure_eq final
        cases same
        exact .inr ⟨error, rfl⟩
      | ok => cases final
  | yield pair rest before middle after first last step tail ih =>
    cases pair with
    | mk name bytes =>
      unfold fileBody at step
      obtain ⟨writing, result, finalEvents, written, final, shape⟩ := Snapshot.returns_bind_split _ _ step
      cases result with
      | error => cases final
      | ok writtenUnit =>
        cases writtenUnit
        obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq final
        cases same
        rcases ih rfl with success | error
        · exact .inl ⟨success.1, by simpa only [shape, List.append_nil] using
            (FileWrites.next name bytes rest writing last (writeNew_source _ _ _ _ written) success.2)⟩
        · exact .inr error

def ContentObservation (uid : Nat) (stage : UInt64) (input : Input) (json wire : ByteArray)
    (events : List (Request × Reply)) : Prop :=
  ∃ files writing exporting,
    contentFiles input json wire = .ok files ∧ events = writing ++ exporting ∧
    FileWrites stage files writing ∧ Returns (exports uid stage input) exporting (.ok ())

-- §FS-host-boundary.publication: Every standard content file is derived from the same input bytes.
theorem fill_source (uid : Nat) (stage : UInt64) (input : Input) (json wire : ByteArray)
    {events : List (Request × Reply)}
    (run : Returns (fill uid stage input json wire) events (.ok ())) :
    ContentObservation uid stage input json wire events := by
  rw [fill_content] at run
  split at run
  · cases run
  · rename_i files plan
    unfold contentThen at run
    obtain ⟨writing, state, exporting, loopRun, final, shape⟩ := Snapshot.returns_bind_split _ _ run
    have traced := forIn_source _ _ _ loopRun
    rcases fileLoop_cases stage traced rfl with success | error
    · simp only [success.1] at final
      exact ⟨files, writing, exporting, plan, shape, success.2, final⟩
    · obtain ⟨error, failed⟩ := error
      simp only [failed] at final
      cases final

end LeanCage.Host.Publication

namespace LeanCage.Host.Publication
open Filesystem

-- §FS-host-boundary.publication: Standard output names are single checked relative components.
theorem contentFiles_components (input : Input) (json wire : ByteArray) (files : List (String × ByteArray))
    (accepted : contentFiles input json wire = .ok files) :
    ∀ pair ∈ files, Snapshot.ValidComponent pair.1 := by
  have checked : files.all (fun pair => decide (Snapshot.ValidComponent pair.1)) = true := by
    cases raw : input.rawReport <;>
      cases stored : input.validated.bind (·.stored) <;>
        cases manifest : input.validated.bind (·.manifest) <;>
          cases complete : input.outcome.status == "complete"
    all_goals
      unfold contentFiles at accepted
      simp only [raw, stored, manifest, complete, Bool.false_eq_true, ↓reduceIte] at accepted
      repeat' first | (split at accepted) | (cases accepted)
    all_goals simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_true]
    all_goals rfl
  intro pair member
  simpa only [decide_eq_true_eq] using List.all_eq_true.mp checked pair member

end LeanCage.Host.Publication
