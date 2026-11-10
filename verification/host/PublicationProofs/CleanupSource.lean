import PublicationProofs.CleanupFrontier
import PublicationProofs.LoopFrontier
import FilesystemLoweringLaws

namespace LeanCage.Host.Publication
open Filesystem Kernel

def cleanupFiles (uid : Nat) (root : UInt64) (files : List Artifacts.ValidatedFile) : Filesystem.Program Unit := do
  for file in files do unlinkRelative uid root file.path.components false

def cleanupDirectories (uid : Nat) (root : UInt64) (paths : List Artifacts.ExportPath) : Filesystem.Program Unit := do
  for path in paths do unlinkRelative uid root path.components true

def cleanupExport (uid : Nat) (root : Directories.Opened) (input : Input) : Filesystem.Program Unit := do
  cleanupFiles uid root.fd input.outcome.files
  cleanupDirectories uid root.fd
    ((input.validated.map (·.dirs) |>.getD []).mergeSort (fun a b => b.components.length ≤ a.components.length))
  let _ ← Filesystem.Program.effect {op := .close, first := root.fd}
  pure ()

def cleanupNames : List String := ["policy.json", "boot.log", "vm-report.json", "stdout", "stderr",
  "stored-report.json", "export.manifest", "result.json", "publication.wire"]

def cleanupStageFiles (stage : Directories.Fresh) (names : List String) : Filesystem.Program Unit := do
  for name in names do
    let _ ← Filesystem.Program.effect {op := .unlinkAt, first := stage.directory.fd, left := name.toUTF8}
    pure ()

def cleanupFooter (stage : Directories.Fresh) : Filesystem.Program Unit := do
  cleanupStageFiles stage cleanupNames
  let _ ← Filesystem.Program.effect {
    op := .unlinkAt, first := stage.directory.fd, second := 512, left := "export".toUTF8 }
  let _ ← Filesystem.Program.effect {op := .close, first := stage.directory.fd}
  let _ ← Filesystem.Program.effect {
    op := .unlinkAt, first := stage.container.fd, second := 512, left := stage.name }
  let _ ← Filesystem.Program.effect {op := .close, first := stage.container.fd}
  pure ()

-- §FS-host-boundary.ownership: These definitions expose actual source phases;
-- they perform the same operations, with the same failures, ordering and ignored
-- replies as the maintained cleanup. They add no cleanup-success assumption.
theorem cleanup_source_shape (parent : Directories.Parent) (stage : Directories.Fresh) (input : Input) :
    cleanup parent stage input =
      (Directories.openAt parent.uid stage.directory.fd "export".toUTF8).bind
        (fun opened => match opened with
          | .error _ => cleanupFooter stage
          | .ok root => (cleanupExport parent.uid root input).bind (fun _ => cleanupFooter stage)) := by
  unfold cleanup
  apply congrArg (Filesystem.Program.bind (Directories.openAt parent.uid stage.directory.fd "export".toUTF8))
  funext opened
  cases opened with
  | error => rfl
  | ok root =>
    simp only [cleanupExport, cleanupFiles, cleanupDirectories, cleanupFooter, cleanupStageFiles, cleanupNames,
      Bind.bind, Pure.pure, Filesystem.Program.bind_assoc, Filesystem.Program.bind]

private theorem pure_no_last {α : Type} {value : α} {before : List (Request × Option Reply)}
    {event : Request × Option Reply} (source : Prefix (.pure value) (before ++ [event])) : False := by
  have length := congrArg List.length (Snapshot.prefix_pure_empty source)
  simp only [List.length_append, List.length_singleton, List.length_nil] at length
  omega

structure RelativeCleanup {α : Type} (uid : Nat) (root : UInt64) (items : List α)
    (path : α → Artifacts.ExportPath) (directory : Bool)
    (before : List (Request × Option Reply)) (request : Request) (observed : Option Reply) where
  item : α
  member : item ∈ items
  earlier : List α
  later : List α
  sequence : items = earlier ++ item :: later
  completed : List (Request × Reply)
  prepared : Returns (forIn earlier () (fun item _ => do
    unlinkRelative uid root (path item).components directory
    pure (.yield ()))) completed ()
  inside : List (Request × Option Reply)
  active : RelativeUnlinkFrontier uid root (path item).components directory inside request observed
  trace : before = Publication.completed completed ++ inside

-- §FS-host-boundary.ownership: The selected descendant removal comes from a
-- genuine typed export path in the actual loop. Earlier ignored errors remain
-- in its completed prefix, and the selected unlink may lose its reply.
theorem relative_cleanup_frontier {α : Type} (uid : Nat) (root : UInt64) (items : List α)
    (path : α → Artifacts.ExportPath) (directory : Bool)
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix (forIn items () (fun item _ => do
      unlinkRelative uid root (path item).components directory
      pure (.yield ()))) (before ++ [(request, observed)]))
    (removing : request.op = .unlinkAt) :
    Nonempty (RelativeCleanup uid root items path directory before request observed) := by
  obtain ⟨frontier⟩ := loop_frontier items () _ source
  rcases filesystem_last_bind_split _ _ frontier.active with unlinking |
      ⟨first, result, last, unlinked, following, trace⟩
  · exact ⟨{
      item := frontier.item
      member := (congrArg (fun members : List α => frontier.item ∈ members) frontier.sequence).mpr (by simp)
      earlier := frontier.earlier
      later := frontier.later
      sequence := frontier.sequence
      completed := frontier.completed
      prepared := frontier.prepared
      inside := frontier.inside
      active := Classical.choice (unlink_relative_frontier uid root (path frontier.item).components directory unlinking removing)
      trace := frontier.trace }⟩
  · exact False.elim (pure_no_last following)

theorem cleanup_files_frontier (uid : Nat) (root : UInt64) (files : List Artifacts.ValidatedFile)
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix (cleanupFiles uid root files) (before ++ [(request, observed)]))
    (removing : request.op = .unlinkAt) :
    Nonempty (RelativeCleanup uid root files (·.path) false before request observed) := by
  unfold cleanupFiles at source
  rcases filesystem_last_bind_split _ _ source with active |
      ⟨first, result, last, completed, following, trace⟩
  · exact relative_cleanup_frontier _ _ _ _ _ active removing
  · exact False.elim (pure_no_last following)

theorem cleanup_directories_frontier (uid : Nat) (root : UInt64) (paths : List Artifacts.ExportPath)
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix (cleanupDirectories uid root paths) (before ++ [(request, observed)]))
    (removing : request.op = .unlinkAt) :
    Nonempty (RelativeCleanup uid root paths id true before request observed) := by
  unfold cleanupDirectories at source
  rcases filesystem_last_bind_split _ _ source with active |
      ⟨first, result, last, completed, following, trace⟩
  · exact relative_cleanup_frontier _ _ _ _ _ active removing
  · exact False.elim (pure_no_last following)

inductive CleanupExportFrontier (uid : Nat) (root : Directories.Opened) (input : Input)
    (before : List (Request × Option Reply)) (request : Request) (observed : Option Reply) : Type where
  | files (source : RelativeCleanup uid root.fd input.outcome.files (·.path) false before request observed)
  | directories (files : List (Request × Reply)) (completed : Returns (cleanupFiles uid root.fd input.outcome.files) files ())
      (inside : List (Request × Option Reply))
      (source : RelativeCleanup uid root.fd
        ((input.validated.map (·.dirs) |>.getD []).mergeSort (fun a b => b.components.length ≤ a.components.length))
        id true inside request observed)
      (trace : before = Publication.completed files ++ inside)

-- §FS-host-boundary.ownership: Cleanup selects a typed file or planned directory
-- of this SAME export root. In particular, arbitrary VM bytes cannot contribute
-- a new path operand here through an ignored error or a lost acknowledgement.
theorem cleanup_export_frontier (uid : Nat) (root : Directories.Opened) (input : Input)
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix (cleanupExport uid root input) (before ++ [(request, observed)]))
    (removing : request.op = .unlinkAt) :
    Nonempty (CleanupExportFrontier uid root input before request observed) := by
  unfold cleanupExport at source
  rcases filesystem_last_bind_split _ _ source with files |
      ⟨files, result, inside, completed, following, trace⟩
  · obtain ⟨selected⟩ := cleanup_files_frontier _ _ _ files removing
    exact ⟨.files selected⟩
  · rcases filesystem_last_bind_split _ _ following with directories |
        ⟨directories, result, last, completedDirectories, closing, nextTrace⟩
    · obtain ⟨selected⟩ := cleanup_directories_frontier _ _ _ directories removing
      exact ⟨.directories files completed inside selected trace⟩
    · have profile : RequestProgram (fun operation => operation.op ≠ .unlinkAt)
          (do let _ ← Filesystem.Program.effect {op := .close, first := root.fd}; pure ()) := by
        apply RequestProgram.call (by intro impossible; cases impossible)
        intro reply
        exact .pure _
      exact False.elim (request_prefix profile closing (request, observed) (by simp) removing)

private theorem effect_frontier (operation : Request) {before : List (Request × Option Reply)}
    {request : Request} {observed : Option Reply}
    (source : Prefix (Filesystem.Program.effect operation) (before ++ [(request, observed)])) :
    before = [] ∧ request = operation := by
  have bounded : ∀ {events}, Prefix (Filesystem.Program.effect operation) events → events.length ≤ 1 := by
    intro events active
    cases active with
    | empty => simp
    | lost => simp
    | returned request next reply events following => rw [Snapshot.prefix_pure_empty following]; simp
  have length := bounded source
  simp only [List.length_append, List.length_singleton] at length
  have empty : before = [] := List.length_eq_zero_iff.mp (by omega)
  subst before
  cases observed <;> cases source <;> exact ⟨rfl, rfl⟩

private theorem effect_returns (operation : Request) {events : List (Request × Reply)} {reply : Reply}
    (source : Returns (Filesystem.Program.effect operation) events reply) : events = [(operation, reply)] := by
  obtain ⟨value, rest, trace, following⟩ := Snapshot.returns_call_split source
  obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq following
  rw [same, trace]

structure StageFileCleanup (stage : Directories.Fresh) (before : List (Request × Option Reply))
    (request : Request) (observed : Option Reply) where
  loop : LoopFrontier cleanupNames () (fun name _ => do
    let _ ← Filesystem.Program.effect {op := .unlinkAt, first := stage.directory.fd, left := name.toUTF8}
    pure (.yield ())) before request observed
  operation : request = {op := .unlinkAt, first := stage.directory.fd, left := loop.item.toUTF8}

theorem stage_files_frontier (stage : Directories.Fresh)
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix (cleanupStageFiles stage cleanupNames) (before ++ [(request, observed)])) :
    Nonempty (StageFileCleanup stage before request observed) := by
  unfold cleanupStageFiles at source
  rcases filesystem_last_bind_split _ _ source with active |
      ⟨first, result, last, completed, following, trace⟩
  · obtain ⟨frontier⟩ := loop_frontier cleanupNames () _ active
    have profile : RequestProgram (fun request => request = {
        op := .unlinkAt, first := stage.directory.fd, left := frontier.item.toUTF8 }) (do
      let _ ← Filesystem.Program.effect {op := .unlinkAt, first := stage.directory.fd, left := frontier.item.toUTF8}
      pure (ForInStep.yield ())) := by
      apply RequestProgram.call (allowed := fun request => request = _) rfl
      intro reply
      exact .pure _
    exact ⟨⟨frontier, request_prefix profile frontier.active (request, observed) (by simp)⟩⟩
  · exact False.elim (pure_no_last following)

inductive CleanupFooterFrontier (stage : Directories.Fresh) (before : List (Request × Option Reply))
    (request : Request) (observed : Option Reply) : Type where
  | files (source : StageFileCleanup stage before request observed)
  | export (files : List (Request × Reply)) (completed : Returns (cleanupStageFiles stage cleanupNames) files ())
      (trace : before = Publication.completed files)
      (operation : request = {op := .unlinkAt, first := stage.directory.fd, second := 512, left := "export".toUTF8})
  | root (files : List (Request × Reply)) (completed : Returns (cleanupStageFiles stage cleanupNames) files ())
      (exportReply closeReply : Reply)
      (trace : before = Publication.completed (files ++ [
        ({op := .unlinkAt, first := stage.directory.fd, second := 512, left := "export".toUTF8}, exportReply),
        ({op := .close, first := stage.directory.fd}, closeReply)]))
      (operation : request = {op := .unlinkAt, first := stage.container.fd, second := 512, left := stage.name})

-- §FS-host-boundary.ownership: The footer distinguishes actual own-stage child
-- removals from the one final own-root removal after its real close observation.
-- An error acknowledgement may still remove a binding; it never changes the operands.
theorem cleanup_footer_frontier (stage : Directories.Fresh)
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix (cleanupFooter stage) (before ++ [(request, observed)]))
    (removing : request.op = .unlinkAt) : Nonempty (CleanupFooterFrontier stage before request observed) := by
  unfold cleanupFooter at source
  rcases filesystem_last_bind_split _ _ source with files |
      ⟨files, result, inside, completed, following, trace⟩
  · obtain ⟨frontier⟩ := stage_files_frontier _ files
    exact ⟨.files frontier⟩
  · rcases filesystem_last_bind_split _ _ following with exporting |
        ⟨exporting, exportReply, afterExport, exported, following, exportTrace⟩
    · obtain ⟨rfl, operation⟩ := effect_frontier _ exporting
      exact ⟨.export files completed (by simpa only [List.append_nil] using trace) operation⟩
    · have exportTraceActual := effect_returns _ exported
      rcases filesystem_last_bind_split _ _ following with closing |
          ⟨closing, closeReply, afterClose, closed, following, closeTrace⟩
      · have operation := (effect_frontier _ closing).2
        rw [operation] at removing
        cases removing
      · have closeTraceActual := effect_returns _ closed
        rcases filesystem_last_bind_split _ _ following with unlinking |
            ⟨unlinking, unlinkReply, afterUnlink, unlinked, final, unlinkTrace⟩
        · obtain ⟨rfl, operation⟩ := effect_frontier _ unlinking
          exact ⟨.root files completed exportReply closeReply (by
            simp only [trace, exportTrace, closeTrace, exportTraceActual, closeTraceActual, Publication.completed,
              List.map_append, List.map_cons, List.map_nil, List.append_nil, List.cons_append,
              List.nil_append]) operation⟩
        · have profile : RequestProgram (fun operation => operation.op ≠ .unlinkAt)
              (do let _ ← Filesystem.Program.effect {op := .close, first := stage.container.fd}; pure ()) := by
            apply RequestProgram.call (by intro impossible; cases impossible)
            intro reply
            exact .pure _
          exact False.elim (request_prefix profile final (request, observed) (by simp) removing)

inductive CleanupFrontier (parent : Directories.Parent) (stage : Directories.Fresh) (input : Input)
    (before : List (Request × Option Reply)) (request : Request) (observed : Option Reply) : Type where
  | exports (root : Directories.Opened) (opening : List (Request × Reply))
      (opened : Returns (Directories.openAt parent.uid stage.directory.fd "export".toUTF8) opening (.ok root))
      (inside : List (Request × Option Reply))
      (source : CleanupExportFrontier parent.uid root input inside request observed)
      (trace : before = Publication.completed opening ++ inside)
  | footer (opened : Result Directories.Opened) (opening : List (Request × Reply))
      (openingSource : Returns (Directories.openAt parent.uid stage.directory.fd "export".toUTF8) opening opened)
      (earlier : List (Request × Reply))
      (prior : match opened with
        | .error _ => earlier = []
        | .ok root => Returns (cleanupExport parent.uid root input) earlier ())
      (inside : List (Request × Option Reply)) (source : CleanupFooterFrontier stage inside request observed)
      (trace : before = Publication.completed (opening ++ earlier) ++ inside)

theorem cleanup_frontier (parent : Directories.Parent) (stage : Directories.Fresh) (input : Input)
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix (cleanup parent stage input) (before ++ [(request, observed)]))
    (removing : request.op = .unlinkAt) : Nonempty (CleanupFrontier parent stage input before request observed) := by
  rw [cleanup_source_shape] at source
  rcases filesystem_last_bind_split _ _ source with opening |
      ⟨opening, result, inside, opened, following, trace⟩
  · have profile := read_only_namespace_passive (Retrieval.openAt_readOnly parent.uid stage.directory.fd "export".toUTF8)
    have passive := request_prefix profile opening (request, observed) (by simp)
    unfold NamespacePassive at passive
    rw [removing] at passive
    exact False.elim passive
  · cases result with
    | error error =>
      obtain ⟨footer⟩ := cleanup_footer_frontier stage following removing
      exact ⟨.footer (.error error) opening opened [] rfl inside footer (by simpa only [List.append_nil] using trace)⟩
    | ok root =>
      rcases filesystem_last_bind_split _ _ following with exporting |
          ⟨exporting, result, footerBefore, exported, following, exportTrace⟩
      · obtain ⟨relative⟩ := cleanup_export_frontier parent.uid root input exporting removing
        exact ⟨.exports root opening opened inside relative trace⟩
      · obtain ⟨footer⟩ := cleanup_footer_frontier stage following removing
        exact ⟨.footer (.ok root) opening opened exporting exported footerBefore footer (by
          simp only [trace, exportTrace, Publication.completed, List.map_append, List.append_assoc])⟩

end LeanCage.Host.Publication
