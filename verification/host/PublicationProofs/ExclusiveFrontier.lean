import FilesystemRunFiles
import PublicationProofs.Frontier
import PublicationProofs.LoopFrontier
import PublicationProofs.CleanupFrontier
import PublicationProofs.CleanupSource
import PublicationProofs.Prepare
import FilesystemSourceReadForms

namespace LeanCage.Host.Publication
open Filesystem Kernel

private theorem readonly_no_exclusive {α : Type} {program : Filesystem.Program α}
    (source : Retrieval.ReadOnly program) : RequestProgram (fun request => ¬ ExclusiveFile request) program :=
  request_weaken (read_only_namespace_passive source) (fun _ => passive_not_exclusive)

private theorem pure_no_last {α : Type} (value : α) {before : List (Request × Option Reply)} {request : Request}
    (source : Prefix (.pure value) (before ++ [(request, none)])) : False := by
  have count := congrArg List.length (Snapshot.prefix_pure_empty source)
  simp only [List.length_append, List.length_singleton, List.length_nil] at count
  omega

theorem DirectoryChain.leaf_fits {uid : Nat} {create : Bool} {root leaf : UInt64} {names : List String}
    {events : List (Request × Reply)} (source : DirectoryChain uid create root names events leaf)
    (initial : SourceReadForms.DescriptorFits root) : SourceReadForms.DescriptorFits leaf := by
  induction source with
  | root => exact initial
  | child component actual below ih =>
    apply ih
    cases create with
    | false =>
      obtain ⟨reply, information, trace, recognized, parsed, trusted⟩ := Retrieval.directoryOpening_source _ _ _ actual
      exact SourceReadForms.descriptor_fits recognized
    | true =>
      obtain ⟨made, opening, trace, acknowledged, opened⟩ := ensureAt_source _ _ _ actual
      obtain ⟨reply, information, trace, recognized, parsed, trusted⟩ := opened
      exact SourceReadForms.descriptor_fits recognized

structure RelativeExclusiveFrontier (uid : Nat) (root : UInt64) (file : Artifacts.ValidatedFile)
    (before : List (Request × Option Reply)) (request : Request) where
  name : String
  named : file.path.components.getLast? = some name
  component : Snapshot.ValidComponent name
  parent : UInt64
  opening : List (Request × Reply)
  chain : DirectoryChain uid false root file.path.components.dropLast opening parent
  operation : request = {
    op := .openAt
    first := parent
    second := newFileFlags
    third := if file.executable then 448 else 384
    left := name.toUTF8 }
  trace : before = completed opening

-- §FS-host-boundary.ownership: This pending artifact file open retains
-- the validated last component and actual earlier checked directory chain,
-- without requiring the file write or traversal to finish later.
theorem relative_exclusive_frontier (uid : Nat) (root : UInt64) (file : Artifacts.ValidatedFile)
    {before : List (Request × Option Reply)} {request : Request}
    (source : Prefix (writeRelative uid root file) (before ++ [(request, none)]))
    (exclusive : ExclusiveFile request) : Nonempty (RelativeExclusiveFrontier uid root file before request) := by
  unfold writeRelative at source
  dsimp only at source
  split at source
  · rename_i name named
    obtain ⟨frontier⟩ := under_action_frontier uid root file.path.components.dropLast false
      (fun parent => writeNew parent name.toUTF8 file.bytes (if file.executable then 448 else 384)) ExclusiveFile
      (fun parent part => by
        change RequestProgram (fun request => ¬ ExclusiveFile request) (Directories.openAt uid parent part.toUTF8)
        exact readonly_no_exclusive (Retrieval.openAt_readOnly _ _ _))
      (fun _ _ => readonly_no_exclusive (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))) source exclusive
    obtain ⟨empty, operation⟩ := writeNew_exclusive_first _ _ _ _ frontier.active exclusive
    exact ⟨{
      name
      named
      component := file.path.valid.2.2.2 name (List.mem_of_getLast? named)
      parent := frontier.parent
      opening := frontier.opening
      chain := frontier.chain
      operation
      trace := frontier.trace.trans (by rw [empty, List.append_nil]) }⟩
  · exact False.elim (pure_no_last _ source)

theorem ensure_no_exclusive (uid : Nat) (parent : UInt64) (name : ByteArray) :
    RequestProgram (fun request => ¬ ExclusiveFile request) (Directories.ensureAt uid parent name) := by
  unfold Directories.ensureAt
  apply RequestProgram.call (by intro other; cases other.1)
  intro reply
  dsimp only [Filesystem.Program.bind]
  split
  · exact readonly_no_exclusive (Retrieval.openAt_readOnly _ _ _)
  · split
    · exact readonly_no_exclusive (Retrieval.openAt_readOnly _ _ _)
    · exact .pure _

theorem under_no_exclusive {α : Type} (uid : Nat) (root : UInt64) (names : List String) (create : Bool)
    (action : UInt64 → Filesystem.Program (Result α))
    (quiet : ∀ parent, RequestProgram (fun request => ¬ ExclusiveFile request) (action parent)) :
    RequestProgram (fun request => ¬ ExclusiveFile request) (under uid root names create action) := by
  induction names generalizing root with
  | nil => exact quiet root
  | cons name names ih =>
    unfold under
    split
    · exact .pure _
    · cases create <;> simp only [Bool.false_eq_true, ↓reduceIte]
      all_goals apply request_bind
      · exact readonly_no_exclusive (Retrieval.openAt_readOnly _ _ _)
      · intro result
        cases result with
        | error => exact .pure _
        | ok child =>
          exact request_bind (ih child.fd)
            (fun _ => readonly_no_exclusive (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _)))
      · exact ensure_no_exclusive _ _ _
      · intro result
        cases result with
        | error => exact .pure _
        | ok child =>
          exact request_bind (ih child.fd)
            (fun _ => readonly_no_exclusive (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _)))

private theorem directories_no_exclusive (uid : Nat) (root : UInt64) (paths : List Artifacts.ExportPath) :
    RequestProgram (fun request => ¬ ExclusiveFile request) (directories uid root paths) := by
  unfold directories
  apply request_bind
  · apply request_forIn
    intro path member state
    apply request_bind (under_no_exclusive _ _ _ _ _ (fun _ => .pure _))
    intro result
    cases result <;> exact .pure _
  · intro state
    dsimp only
    split <;> exact .pure _

structure RelativeLoopExclusiveFrontier (uid : Nat) (root : UInt64) (files : List Artifacts.ValidatedFile)
    (before : List (Request × Option Reply)) (request : Request) where
  loop : LoopFrontier files (none, ()) (actionBody (writeRelative uid root)) before request none
  current : RelativeExclusiveFrontier uid root loop.item loop.inside request

theorem relative_loop_exclusive_frontier (uid : Nat) (root : UInt64) (files : List Artifacts.ValidatedFile)
    {before : List (Request × Option Reply)} {request : Request}
    (source : Prefix (checkedActions (writeRelative uid root) files (pure (.ok ()))) (before ++ [(request, none)]))
    (exclusive : ExclusiveFile request) : Nonempty (RelativeLoopExclusiveFrontier uid root files before request) := by
  unfold checkedActions at source
  rcases filesystem_last_bind_split _ _ source with looping |
      ⟨looping, result, inside, completed, following, trace⟩
  · obtain ⟨loop⟩ := loop_frontier _ _ _ looping
    have active : Prefix (actionBody (writeRelative uid root) loop.item loop.state) (loop.inside ++ [(request, none)]) := loop.active
    unfold actionBody at active
    rcases filesystem_last_bind_split _ _ active with relative |
        ⟨relative, result, inside, completed, following, trace⟩
    · obtain ⟨frontier⟩ := relative_exclusive_frontier uid root loop.item relative exclusive
      exact ⟨⟨loop, frontier⟩⟩
    · cases result <;> exact False.elim (pure_no_last _ following)
  · rcases result with ⟨result, stateValue⟩
    cases result <;> exact False.elim (pure_no_last _ following)

private theorem call_after_other {α : Type} (head : Request) (next : Reply → Filesystem.Program α)
    {before : List (Request × Option Reply)} {request : Request}
    (source : Prefix (.call head next) (before ++ [(request, none)])) (different : request.op ≠ head.op) :
    ∃ reply inside, before = (head, some reply) :: inside ∧ Prefix (next reply) (inside ++ [(request, none)]) := by
  cases before with
  | nil => cases source; exact False.elim (different rfl)
  | cons first rest =>
    cases rest with
    | nil =>
      cases source with
      | returned _ _ reply events following => exact ⟨reply, [], rfl, following⟩
    | cons second rest =>
      cases source with
      | returned _ _ reply events following => exact ⟨reply, second :: rest, rfl, following⟩

structure ExportsExclusiveFrontier (uid : Nat) (stage : UInt64) (input : Input)
    (before : List (Request × Option Reply)) (request : Request) where
  made : Reply
  root : Directories.Opened
  opening : List (Request × Reply)
  opened : Returns (Directories.openAt uid stage "export".toUTF8) opening (.ok root)
  making : List (Request × Reply)
  madeDirectories : Returns (directories uid root.fd (input.validated.map (·.dirs) |>.getD [])) making (.ok ())
  inside : List (Request × Option Reply)
  current : RelativeLoopExclusiveFrontier uid root.fd input.outcome.files inside request
  trace : before = [({op := .mkdirAt, first := stage, second := 448, left := "export".toUTF8}, some made)] ++
    completed opening ++ completed making ++ inside

-- §FS-host-boundary.ownership: The selected export file retains the real
-- export directory open, actual earlier directory setup and file-loop
-- position; no later file result or export close is needed.
theorem exports_exclusive_frontier (uid : Nat) (stage : UInt64) (input : Input)
    {before : List (Request × Option Reply)} {request : Request}
    (source : Prefix (exports uid stage input) (before ++ [(request, none)]))
    (exclusive : ExclusiveFile request) : Nonempty (ExportsExclusiveFrontier uid stage input before request) := by
  unfold exports at source
  obtain ⟨made, rest, firstTrace, afterMkdir⟩ := call_after_other _ _ source (by
    rw [exclusive.1]
    change Op.openAt ≠ Op.mkdirAt
    decide)
  dsimp only [Filesystem.Program.bind] at afterMkdir
  split at afterMkdir
  · exact False.elim (pure_no_last _ afterMkdir)
  · rcases filesystem_last_bind_split _ _ afterMkdir with opening |
        ⟨opening, result, inside, opened, following, openTrace⟩
    · exact False.elim (request_prefix (readonly_no_exclusive (Retrieval.openAt_readOnly _ _ _)) opening
        (request, none) (by simp) exclusive)
    · cases result with
      | error error => exact False.elim (pure_no_last _ following)
      | ok root =>
        rcases filesystem_last_bind_split _ _ following with filling |
            ⟨filling, result, closing, filled, afterFill, closeTrace⟩
        · rcases filesystem_last_bind_split _ _ filling with making |
              ⟨making, result, writing, madeDirectories, afterDirectories, dirsTrace⟩
          · exact False.elim (request_prefix (directories_no_exclusive _ _ _) making (request, none) (by simp) exclusive)
          · cases result with
            | error error => exact False.elim (pure_no_last _ afterDirectories)
            | ok madeValue =>
              cases madeValue
              change Prefix (checkedActions (writeRelative uid root.fd) input.outcome.files (pure (.ok ())))
                (writing ++ [(request, none)]) at afterDirectories
              obtain ⟨cursor⟩ := relative_loop_exclusive_frontier uid root.fd input.outcome.files afterDirectories exclusive
              exact ⟨{
                made
                root
                opening
                opened
                making
                madeDirectories
                inside := writing
                current := cursor
                trace := by simp only [firstTrace, openTrace, dirsTrace, List.cons_append, List.nil_append, List.append_assoc] }⟩
        · exact False.elim (request_prefix (readonly_no_exclusive
            (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))) afterFill (request, none) (by simp) exclusive)

structure ActionFrontier {α : Type} (action : α → Filesystem.Program (Result Unit)) (items : List α)
    (before : List (Request × Option Reply)) (request : Request) where
  loop : LoopFrontier items (none, ()) (actionBody action) before request none
  active : Prefix (action loop.item) (loop.inside ++ [(request, none)])

inductive CheckedActionsFrontier {α : Type} (action : α → Filesystem.Program (Result Unit)) (items : List α)
    (next : Filesystem.Program (Result Unit)) (before : List (Request × Option Reply)) (request : Request) : Type where
  | current (source : ActionFrontier action items before request)
  | following (completed : List (Request × Reply))
      (returned : Returns (checkedActions action items (pure (.ok ()))) completed (.ok ()))
      (inside : List (Request × Option Reply)) (active : Prefix next (inside ++ [(request, none)]))
      (trace : before = Publication.completed completed ++ inside)

theorem checked_actions_frontier {α : Type} (action : α → Filesystem.Program (Result Unit)) (items : List α)
    (next : Filesystem.Program (Result Unit)) {before : List (Request × Option Reply)} {request : Request}
    (source : Prefix (checkedActions action items next) (before ++ [(request, none)])) :
    Nonempty (CheckedActionsFrontier action items next before request) := by
  unfold checkedActions at source
  rcases filesystem_last_bind_split _ _ source with looping |
      ⟨looping, result, inside, completed, following, trace⟩
  · obtain ⟨loop⟩ := loop_frontier _ _ _ looping
    have active : Prefix (actionBody action loop.item loop.state) (loop.inside ++ [(request, none)]) := loop.active
    unfold actionBody at active
    rcases filesystem_last_bind_split _ _ active with called |
        ⟨called, result, inside, completed, following, trace⟩
    · exact ⟨.current ⟨loop, called⟩⟩
    · cases result <;> exact False.elim (pure_no_last _ following)
  · rcases result with ⟨result, stateValue⟩
    cases result with
    | none =>
      have returned : Returns (checkedActions action items (pure (.ok ()))) (looping ++ []) (.ok ()) := by
        unfold checkedActions
        exact Snapshot.returns_bind_join completed (.pure _)
      exact ⟨.following looping (by simpa only [List.append_nil] using returned) inside following trace⟩
    | some result => exact False.elim (pure_no_last _ following)

inductive FillExclusiveFrontier (uid : Nat) (stage : UInt64) (input : Input) (json wire : ByteArray)
    (before : List (Request × Option Reply)) (request : Request) : Type where
  | file (files : List (String × ByteArray))
      (names : ∀ pair ∈ files, pair.1 ∈ cleanupNames)
      (source : ActionFrontier (fun pair : String × ByteArray => writeNew stage pair.1.toUTF8 pair.2) files before request)
      (empty : source.loop.inside = [])
      (operation : request = {
        op := .openAt
        first := stage
        second := newFileFlags
        third := 384
        left := source.loop.item.1.toUTF8 })
  | exports (files : List (String × ByteArray)) (writing : List (Request × Reply))
      (written : Returns (checkedActions (fun pair : String × ByteArray => writeNew stage pair.1.toUTF8 pair.2)
        files (pure (.ok ()))) writing (.ok ()))
      (inside : List (Request × Option Reply)) (current : ExportsExclusiveFrontier uid stage input inside request)
      (trace : before = completed writing ++ inside)

-- §FS-host-boundary.ownership: A pending new file is either one of the
-- actual canonical metadata files at the retained stage or an artifact
-- below its real export open. Prior source writes and replies are kept.
theorem fill_exclusive_frontier (uid : Nat) (stage : UInt64) (input : Input) (json wire : ByteArray)
    {before : List (Request × Option Reply)} {request : Request}
    (source : Prefix (fill uid stage input json wire) (before ++ [(request, none)]))
    (exclusive : ExclusiveFile request) : Nonempty (FillExclusiveFrontier uid stage input json wire before request) := by
  unfold fill at source
  cases report : input.rawReport <;>
    cases stored : input.validated.bind (·.stored) <;>
    cases manifest : input.validated.bind (·.manifest) <;>
    simp only [report, stored, manifest] at source
  all_goals
    repeat' first
      | exact False.elim (pure_no_last _ source)
      | split at source
      | (dsimp only at source; split at source)
  all_goals
    obtain ⟨frontier⟩ := checked_actions_frontier
      (fun pair : String × ByteArray => writeNew stage pair.1.toUTF8 pair.2) _ (exports uid stage input) source
    cases frontier with
    | current current =>
      obtain ⟨empty, operation⟩ := writeNew_exclusive_first _ _ _ _ current.active exclusive
      refine ⟨.file _ ?_ current empty operation⟩
      simp [cleanupNames]
    | following writing written inside active trace =>
      obtain ⟨exports⟩ := exports_exclusive_frontier uid stage input active exclusive
      exact ⟨.exports _ writing written inside exports trace⟩

private theorem no_exclusive_last {α : Type} {program : Filesystem.Program α}
    (profile : RequestProgram (fun query => ¬ ExclusiveFile query) program)
    {before : List (Request × Option Reply)} {request : Request}
    (source : Prefix program (before ++ [(request, none)])) (exclusive : ExclusiveFile request) : False :=
  request_prefix profile source (request, none) (by simp) exclusive

structure PreparingExclusiveFrontier (bundle : Validation.Bundle) (input : Input) (target stdoutHash stderrHash : ByteArray)
    (parent : Directories.Parent) (stage : Directories.Fresh)
    (before : List (Request × Option Reply)) (request : Request) where
  policyDigest : ByteArray
  json : ByteArray
  tag : ByteArray
  hashing : List (Request × Reply)
  hashed : Returns (Filesystem.hash input.policy.raw) hashing (.ok policyDigest)
  rendered : WireJson.render GatewayWire.valueDepthMax ((candidate input target).metadata stdoutHash stderrHash) = .ok json
  authenticating : List (Request × Reply)
  authenticated : Returns (authenticate bundle (GatewayWire.encodeResponse 0
    (envelope (stagedInput input target) ((candidate input target).metadata stdoutHash stderrHash)
      policyDigest parent stage))) authenticating (.ok tag)
  inside : List (Request × Option Reply)
  current : FillExclusiveFrontier parent.uid stage.directory.fd (stagedInput input target) (json ++ "\n".toUTF8)
    (GatewayWire.encodeResponse 0 (envelope (stagedInput input target)
      ((candidate input target).metadata stdoutHash stderrHash) policyDigest parent stage)) inside request
  trace : before = completed hashing ++ completed authenticating ++ inside

-- §FS-host-boundary.ownership: This selected real preparation exclusive is
-- source-produced after the same actual policy hash and authentication,
-- before the marker, rename or any future cleanup result.
theorem preparing_exclusive_frontier (bundle : Validation.Bundle) (input : Input) (target stdoutHash stderrHash : ByteArray)
    (parent : Directories.Parent) (stage : Directories.Fresh)
    {before : List (Request × Option Reply)} {request : Request}
    (source : Prefix (prepare bundle input target stdoutHash stderrHash parent stage) (before ++ [(request, none)]))
    (exclusive : ExclusiveFile request) :
    Nonempty (PreparingExclusiveFrontier bundle input target stdoutHash stderrHash parent stage before request) := by
  unfold prepare at source
  rcases filesystem_last_bind_split _ _ source with hashing |
      ⟨hashing, result, afterHashEvents, hashed, afterHash, hashTrace⟩
  · exact False.elim (no_exclusive_last (readonly_no_exclusive (Retrieval.readOnly_snapshot (Snapshot.hash_input _))) hashing exclusive)
  · cases result with
    | error error => exact False.elim (pure_no_last _ afterHash)
    | ok policyDigest =>
      dsimp only at afterHash
      split at afterHash
      · rename_i json rendered
        split at afterHash
        · exact False.elim (pure_no_last _ afterHash)
        · rcases filesystem_last_bind_split _ _ afterHash with authenticating |
              ⟨authenticating, result, afterAuthEvents, authenticated, afterAuth, authTrace⟩
          · exact False.elim (no_exclusive_last (readonly_no_exclusive (Retrieval.authenticate_readOnly _ _)) authenticating exclusive)
          · cases result with
            | error error => exact False.elim (pure_no_last _ afterAuth)
            | ok tag =>
              dsimp only at afterAuth
              rcases filesystem_last_bind_split _ _ afterAuth with filling |
                  ⟨filling, result, afterFillEvents, filled, afterFill, fillTrace⟩
              · obtain ⟨frontier⟩ := fill_exclusive_frontier parent.uid stage.directory.fd (stagedInput input target)
                  (json ++ "\n".toUTF8) _ filling exclusive
                exact ⟨⟨policyDigest, json, tag, hashing, hashed, rendered, authenticating, authenticated,
                  afterAuthEvents, frontier, by simp only [hashTrace, authTrace, List.append_assoc]⟩⟩
              · cases result with
                | error error => exact False.elim (pure_no_last _ afterFill)
                | ok finished =>
                  apply False.elim
                  apply no_exclusive_last (program := _) ?_ afterFill exclusive
                  apply RequestProgram.call (by intro impossible; cases impossible.1)
                  intro reply
                  dsimp only [Filesystem.Program.bind]
                  split <;> exact .pure _
      · exact False.elim (pure_no_last _ afterHash)

end LeanCage.Host.Publication
