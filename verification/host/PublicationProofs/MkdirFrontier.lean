import PublicationProofs.Frontier
import PublicationProofs.LoopFrontier
import FilesystemParentTraversal
import FilesystemPublicationContentProfile
import FilesystemPublicationCreation
import PublicationProofs.Prepare

namespace LeanCage.Host.Publication
open Filesystem Kernel

private theorem readonly_no_mkdir {α : Type} {program : Filesystem.Program α}
    (source : Retrieval.ReadOnly program) : RequestProgram (fun query => query.op ≠ .mkdirAt) program := by
  induction source with
  | pure => exact .pure _
  | call allowed following ih =>
    apply RequestProgram.call _ ih
    intro mkdir
    unfold Retrieval.Allowed at allowed
    rw [mkdir] at allowed
    exact allowed

private theorem no_mkdir_last {α : Type} {program : Filesystem.Program α}
    (profile : RequestProgram (fun query => query.op ≠ .mkdirAt) program)
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix program (before ++ [(request, observed)])) (mkdir : request.op = .mkdirAt) : False :=
  request_prefix profile source (request, observed) (by simp) mkdir

private theorem pure_no_last {α : Type} (value : α) {before : List (Request × Option Reply)}
    {request : Request} {observed : Option Reply}
    (source : Prefix (.pure value) (before ++ [(request, observed)])) : False := by
  have length := congrArg List.length (Snapshot.prefix_pure_empty source)
  simp only [List.length_append, List.length_singleton, List.length_nil] at length
  omega

private theorem call_frontier {α : Type} {head : Request} {next : Reply → Filesystem.Program α}
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix (.call head next) (before ++ [(request, observed)])) :
    (before = [] ∧ request = head) ∨ ∃ reply inside, before = (head, some reply) :: inside ∧
      Prefix (next reply) (inside ++ [(request, observed)]) := by
  cases before with
  | nil => cases observed <;> cases source <;> exact .inl ⟨rfl, rfl⟩
  | cons first rest =>
    cases rest with
    | nil =>
      cases source with
      | returned _ _ reply events following => exact .inr ⟨reply, [], rfl, following⟩
    | cons second rest =>
      cases source with
      | returned _ _ reply events following => exact .inr ⟨reply, second :: rest, rfl, following⟩

structure UnderMkdirFrontier (uid : Nat) (root : UInt64) (names : List String)
    (before : List (Request × Option Reply)) (request : Request) where
  parent : UInt64
  visited : List String
  name : String
  following : List String
  namesExact : names = visited ++ name :: following
  opening : List (Request × Reply)
  chain : DirectoryChain uid true root visited opening parent
  component : Snapshot.ValidComponent name
  operation : request = {op := .mkdirAt, first := parent, second := 448, left := name.toUTF8}
  trace : before = completed opening

-- §FS-host-boundary.ownership: This actual recursive mkdir has only real
-- acknowledged earlier children. The selected ensureAt call is still
-- pending; its return, descendant success or loop completion is not used.
theorem under_mkdir_frontier {α : Type} (uid : Nat) (root : UInt64) (names : List String)
    (action : UInt64 → Filesystem.Program (Result α))
    (quiet : ∀ parent, RequestProgram (fun query => query.op ≠ .mkdirAt) (action parent))
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix (under uid root names true action) (before ++ [(request, observed)]))
    (mkdir : request.op = .mkdirAt) : Nonempty (UnderMkdirFrontier uid root names before request) := by
  induction names generalizing root before with
  | nil => exact False.elim (no_mkdir_last (quiet root) source mkdir)
  | cons name names ih =>
    unfold under at source
    split at source
    · exact False.elim (pure_no_last _ source)
    · rename_i valid
      simp only [↓reduceIte] at source
      rcases filesystem_last_bind_split _ _ source with opening |
          ⟨opening, result, inside, opened, following, trace⟩
      · obtain ⟨empty, operation⟩ := ParentTraversal.ensure_mkdir_first uid root name.toUTF8 opening mkdir
        exact ⟨⟨root, [], name, names, rfl, [], .root root, by simpa using valid, operation, empty⟩⟩
      · cases result with
        | error error => exact False.elim (pure_no_last _ following)
        | ok child =>
          rcases filesystem_last_bind_split _ _ following with recursive |
              ⟨recursive, result, closing, called, afterCall, closingTrace⟩
          · obtain ⟨frontier⟩ := ih child.fd recursive
            exact ⟨{
              parent := frontier.parent
              visited := name :: frontier.visited
              name := frontier.name
              following := frontier.following
              namesExact := congrArg (name :: ·) frontier.namesExact
              opening := opening ++ frontier.opening
              chain := .child (by simpa using valid) opened frontier.chain
              component := frontier.component
              operation := frontier.operation
              trace := trace.trans ((congrArg (completed opening ++ ·) frontier.trace).trans (by
                simp only [completed, List.map_append])) }⟩
          · exact False.elim (no_mkdir_last
              (readonly_no_mkdir (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))) afterCall mkdir)

structure DirectoriesMkdirFrontier (uid : Nat) (root : UInt64) (paths : List Artifacts.ExportPath)
    (before : List (Request × Option Reply)) (request : Request) where
  loop : LoopFrontier (paths.mergeSort (fun left right => left.components.length ≤ right.components.length)) (none, ())
    (actionBody (fun path => under uid root path.components true (fun _ => pure (.ok ())))) before request none
  current : UnderMkdirFrontier uid root loop.item.components loop.inside request

-- §FS-host-boundary.ownership: The actual sorted directory loop selects
-- one original path and its earlier completed iterations. Loss in that
-- current mkdir does not require a future directory-loop acknowledgement.
theorem directories_mkdir_frontier (uid : Nat) (root : UInt64) (paths : List Artifacts.ExportPath)
    {before : List (Request × Option Reply)} {request : Request}
    (source : Prefix (directories uid root paths) (before ++ [(request, none)]))
    (mkdir : request.op = .mkdirAt) : Nonempty (DirectoriesMkdirFrontier uid root paths before request) := by
  change Prefix (checkedActions (fun path => under uid root path.components true (fun _ => pure (.ok ())))
    (paths.mergeSort (fun left right => left.components.length ≤ right.components.length)) (pure (.ok ())))
    (before ++ [(request, none)]) at source
  unfold checkedActions at source
  rcases filesystem_last_bind_split _ _ source with looping |
      ⟨looping, state, inside, completed, following, trace⟩
  · obtain ⟨loop⟩ := loop_frontier _ _ _ looping
    have active : Prefix (actionBody (fun path => under uid root path.components true (fun _ => pure (.ok ())))
        loop.item loop.state) (loop.inside ++ [(request, none)]) := loop.active
    unfold actionBody at active
    rcases filesystem_last_bind_split _ _ active with current |
        ⟨current, result, final, called, tail, shape⟩
    · obtain ⟨frontier⟩ := under_mkdir_frontier uid root loop.item.components (fun _ => pure (.ok ()))
        (fun _ => .pure _) current mkdir
      exact ⟨⟨loop, frontier⟩⟩
    · cases result <;> exact False.elim (pure_no_last _ tail)
  · rcases state with ⟨result, stateValue⟩
    cases result <;> exact False.elim (pure_no_last _ following)

private theorem writeNew_no_mkdir (parent : UInt64) (name bytes : ByteArray) (mode : UInt64) :
    RequestProgram (fun query => query.op ≠ .mkdirAt) (writeNew parent name bytes mode) := by
  unfold writeNew
  split
  · exact .pure _
  · apply RequestProgram.call (by intro impossible; cases impossible)
    intro reply
    split
    · exact .pure _
    · apply request_bind
      · apply request_weaken (Kernel.write_loop_namespace_passive _ _ _ _)
        intro query passive mkdir
        unfold Kernel.NamespacePassive at passive
        rw [mkdir] at passive
        exact passive
      · intro written
        exact readonly_no_mkdir (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))

private theorem writeRelative_no_mkdir (uid : Nat) (root : UInt64) (file : Artifacts.ValidatedFile) :
    RequestProgram (fun query => query.op ≠ .mkdirAt) (writeRelative uid root file) := by
  unfold writeRelative
  dsimp only
  split
  · exact PublicationCreation.under_no_mkdir _ _ _ _ (fun _ => writeNew_no_mkdir _ _ _ _)
  · exact .pure _

private theorem checkedActions_no_mkdir {α : Type} (action : α → Filesystem.Program (Result Unit))
    (items : List α) (next : Filesystem.Program (Result Unit))
    (quiet : ∀ item, RequestProgram (fun query => query.op ≠ .mkdirAt) (action item))
    (following : RequestProgram (fun query => query.op ≠ .mkdirAt) next) :
    RequestProgram (fun query => query.op ≠ .mkdirAt) (checkedActions action items next) := by
  unfold checkedActions
  apply request_bind
  · apply request_forIn
    intro item member state
    apply request_bind (quiet item)
    intro result
    cases result <;> exact .pure _
  · intro state
    rcases state with ⟨result, stateValue⟩
    cases result
    · exact following
    · exact .pure _

private theorem checkedActions_mkdir_after {α : Type} (action : α → Filesystem.Program (Result Unit))
    (items : List α) (next : Filesystem.Program (Result Unit))
    (quiet : ∀ item, RequestProgram (fun query => query.op ≠ .mkdirAt) (action item))
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix (checkedActions action items next) (before ++ [(request, observed)]))
    (mkdir : request.op = .mkdirAt) :
    ∃ completed inside, Returns (checkedActions action items (pure (.ok ()))) completed (.ok ()) ∧
      Prefix next (inside ++ [(request, observed)]) ∧ before = Publication.completed completed ++ inside := by
  unfold checkedActions at source
  rcases filesystem_last_bind_split _ _ source with looping |
      ⟨looping, state, inside, called, following, trace⟩
  · apply False.elim
    apply no_mkdir_last (program := _) ?_ looping mkdir
    apply request_forIn
    intro item member state
    apply request_bind (quiet item)
    intro result
    cases result <;> exact .pure _
  · rcases state with ⟨result, stateValue⟩
    cases result with
    | none =>
      have completed : Returns (checkedActions action items (pure (.ok ()))) (looping ++ []) (.ok ()) := by
        unfold checkedActions
        exact Snapshot.returns_bind_join called (.pure _)
      exact ⟨looping, inside, by simpa only [List.append_nil] using completed, following, trace⟩
    | some result => exact False.elim (pure_no_last _ following)

inductive ExportsMkdirFrontier (uid : Nat) (stage : UInt64) (input : Input)
    (before : List (Request × Option Reply)) (request : Request) : Type where
  | root (trace : before = [])
      (operation : request = {op := .mkdirAt, first := stage, second := 448, left := "export".toUTF8})
  | nested (made : Reply) (root : Directories.Opened) (opening : List (Request × Reply))
      (opened : Returns (Directories.openAt uid stage "export".toUTF8) opening (.ok root))
      (inside : List (Request × Option Reply))
      (current : DirectoriesMkdirFrontier uid root.fd (input.validated.map (·.dirs) |>.getD []) inside request)
      (trace : before = [({op := .mkdirAt, first := stage, second := 448, left := "export".toUTF8}, some made)] ++
        completed opening ++ inside)

-- §FS-host-boundary.ownership: Export creation is either the original
-- direct child mkdir or one checked nested directory cursor beneath the
-- real acknowledged export open. Future fill/close replies are irrelevant.
theorem exports_mkdir_frontier (uid : Nat) (stage : UInt64) (input : Input)
    {before : List (Request × Option Reply)} {request : Request}
    (source : Prefix (exports uid stage input) (before ++ [(request, none)]))
    (mkdir : request.op = .mkdirAt) : Nonempty (ExportsMkdirFrontier uid stage input before request) := by
  unfold exports at source
  rcases call_frontier source with ⟨trace, operation⟩ | ⟨made, rest, beforeTrace, afterMkdir⟩
  · exact ⟨.root trace operation⟩
  · dsimp only [Filesystem.Program.bind] at afterMkdir
    split at afterMkdir
    · exact False.elim (pure_no_last _ afterMkdir)
    · rcases filesystem_last_bind_split _ _ afterMkdir with opening |
            ⟨opening, result, inside, opened, following, trace⟩
      · exact False.elim (no_mkdir_last (readonly_no_mkdir (Retrieval.openAt_readOnly _ _ _)) opening mkdir)
      · cases result with
        | error error => exact False.elim (pure_no_last _ following)
        | ok root =>
          rcases filesystem_last_bind_split _ _ following with filling |
              ⟨filling, result, closing, filled, afterFill, closeTrace⟩
          · rcases filesystem_last_bind_split _ _ filling with making |
                ⟨making, result, writing, madeDirectories, afterDirectories, dirsTrace⟩
            · obtain ⟨cursor⟩ := directories_mkdir_frontier uid root.fd _ making mkdir
              exact ⟨.nested made root opening opened inside cursor (by
                exact beforeTrace.trans ((congrArg ((_ , some made) :: ·) trace).trans (by
                  simp only [List.cons_append, List.nil_append])))⟩
            · cases result with
              | error error => exact False.elim (pure_no_last _ afterDirectories)
              | ok madeUnit =>
                change Prefix (checkedActions (writeRelative uid root.fd) input.outcome.files (pure (.ok ())))
                  (writing ++ [(request, none)]) at afterDirectories
                exact False.elim (no_mkdir_last
                  (checkedActions_no_mkdir _ _ _ (fun _ => writeRelative_no_mkdir _ _ _) (.pure _)) afterDirectories mkdir)
          · exact False.elim (no_mkdir_last
              (readonly_no_mkdir (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))) afterFill mkdir)

structure FillMkdirFrontier (uid : Nat) (stage : UInt64) (input : Input) (json wire : ByteArray)
    (before : List (Request × Option Reply)) (request : Request) where
  files : List (String × ByteArray)
  writing : List (Request × Reply)
  written : Returns (checkedActions (fun pair : String × ByteArray => writeNew stage pair.1.toUTF8 pair.2)
    files (pure (.ok ()))) writing (.ok ())
  inside : List (Request × Option Reply)
  current : ExportsMkdirFrontier uid stage input inside request
  trace : before = completed writing ++ inside

-- §FS-host-boundary.ownership: Filling reaches this actual export mkdir
-- only after its earlier exclusive file writes returned; no selected
-- mkdir acknowledgement or future stage result is supplied.
theorem fill_mkdir_frontier (uid : Nat) (stage : UInt64) (input : Input) (json wire : ByteArray)
    {before : List (Request × Option Reply)} {request : Request}
    (source : Prefix (fill uid stage input json wire) (before ++ [(request, none)]))
    (mkdir : request.op = .mkdirAt) : Nonempty (FillMkdirFrontier uid stage input json wire before request) := by
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
    obtain ⟨writing, inside, written, active, trace⟩ := checkedActions_mkdir_after
      (fun pair : String × ByteArray => writeNew stage pair.1.toUTF8 pair.2) _ (exports uid stage input)
      (fun _ => writeNew_no_mkdir _ _ _ _) source mkdir
    obtain ⟨frontier⟩ := exports_mkdir_frontier uid stage input active mkdir
    exact ⟨⟨_, writing, written, inside, frontier, trace⟩⟩

structure PreparingMkdirFrontier (bundle : Validation.Bundle) (input : Input) (target stdoutHash stderrHash : ByteArray)
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
  current : FillMkdirFrontier parent.uid stage.directory.fd (stagedInput input target) (json ++ "\n".toUTF8)
    (GatewayWire.encodeResponse 0 (envelope (stagedInput input target)
      ((candidate input target).metadata stdoutHash stderrHash) policyDigest parent stage)) inside request
  trace : before = completed hashing ++ completed authenticating ++ inside

-- §FS-host-boundary.ownership: This selected real preparation mkdir is
-- source-produced after the same actual policy hash and authentication,
-- before the marker, rename or any future cleanup result.
theorem preparing_mkdir_frontier (bundle : Validation.Bundle) (input : Input) (target stdoutHash stderrHash : ByteArray)
    (parent : Directories.Parent) (stage : Directories.Fresh)
    {before : List (Request × Option Reply)} {request : Request}
    (source : Prefix (prepare bundle input target stdoutHash stderrHash parent stage) (before ++ [(request, none)]))
    (mkdir : request.op = .mkdirAt) :
    Nonempty (PreparingMkdirFrontier bundle input target stdoutHash stderrHash parent stage before request) := by
  unfold prepare at source
  rcases filesystem_last_bind_split _ _ source with hashing |
      ⟨hashing, result, afterHashEvents, hashed, afterHash, hashTrace⟩
  · exact False.elim (no_mkdir_last (readonly_no_mkdir (Retrieval.readOnly_snapshot (Snapshot.hash_input _))) hashing mkdir)
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
          · exact False.elim (no_mkdir_last (readonly_no_mkdir (Retrieval.authenticate_readOnly _ _)) authenticating mkdir)
          · cases result with
            | error error => exact False.elim (pure_no_last _ afterAuth)
            | ok tag =>
              dsimp only at afterAuth
              rcases filesystem_last_bind_split _ _ afterAuth with filling |
                  ⟨filling, result, afterFillEvents, filled, afterFill, fillTrace⟩
              · obtain ⟨frontier⟩ := fill_mkdir_frontier parent.uid stage.directory.fd (stagedInput input target)
                  (json ++ "\n".toUTF8) _ filling mkdir
                exact ⟨⟨policyDigest, json, tag, hashing, hashed, rendered, authenticating, authenticated,
                  afterAuthEvents, frontier, by simp only [hashTrace, authTrace, List.append_assoc]⟩⟩
              · cases result with
                | error error => exact False.elim (pure_no_last _ afterFill)
                | ok finished =>
                  apply False.elim
                  apply no_mkdir_last (program := _) ?_ afterFill mkdir
                  apply RequestProgram.call (by intro impossible; cases impossible)
                  intro reply
                  dsimp only [Filesystem.Program.bind]
                  split <;> exact .pure _
      · exact False.elim (pure_no_last _ afterHash)

end LeanCage.Host.Publication
