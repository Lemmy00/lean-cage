import FilesystemDirectorySources
import FilesystemLoweredParentObservations

namespace LeanCage.Host.Kernel.ParentTraversal
open Filesystem

private theorem readonly_no_mkdir {α : Type} {program : Filesystem.Program α}
    (source : Retrieval.ReadOnly program) : RequestProgram (fun request => request.op ≠ .mkdirAt) program := by
  induction source with
  | pure => exact .pure _
  | call allowed following ih =>
    apply RequestProgram.call _ ih
    intro mkdir
    unfold Retrieval.Allowed at allowed
    rw [mkdir] at allowed
    exact allowed

private theorem no_mkdir {α : Type} {program : Filesystem.Program α}
    (profile : RequestProgram (fun request => request.op ≠ .mkdirAt) program)
    {before : List (Request × Option Reply)} {event : Request × Option Reply}
    (source : Prefix program (before ++ [event])) (mkdir : event.1.op = .mkdirAt) : False :=
  request_prefix profile source event (by simp) mkdir

private theorem pure_no_last {α : Type} (value : α) {before : List (Request × Option Reply)}
    {event : Request × Option Reply} (source : Prefix (.pure value) (before ++ [event])) : False := by
  have empty := Snapshot.prefix_pure_empty source
  have length := congrArg List.length empty
  simp only [List.length_append, List.length_singleton, List.length_nil] at length
  omega

private theorem call_mkdir_first {α : Type} (request : Request) (next : Reply → Filesystem.Program α)
    (tail : ∀ reply, RequestProgram (fun request => request.op ≠ .mkdirAt) (next reply))
    {before : List (Request × Option Reply)} {event : Request × Option Reply}
    (source : Prefix (.call request next) (before ++ [event])) (mkdir : event.1.op = .mkdirAt) :
    before = [] ∧ event.1 = request := by
  cases before with
  | nil => rcases event with ⟨operation, observed⟩; cases observed <;> cases source <;> exact ⟨rfl, rfl⟩
  | cons first rest =>
    cases rest with
    | nil =>
      change Prefix (.call request next) [first, event] at source
      cases source with
      | returned _ _ reply events following => exact False.elim (no_mkdir (tail reply) (before := []) following mkdir)
    | cons second rest =>
      change Prefix (.call request next) (first :: second :: (rest ++ [event])) at source
      cases source with
      | returned _ _ reply events following =>
        exact False.elim (no_mkdir (tail reply) (before := second :: rest) following mkdir)

theorem ensure_mkdir_first (uid : Nat) (parent : UInt64) (name : ByteArray)
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix (Directories.ensureAt uid parent name) (before ++ [(request, observed)]))
    (mkdir : request.op = .mkdirAt) :
    before = [] ∧ request = {op := .mkdirAt, first := parent, second := 448, left := name} := by
  unfold Directories.ensureAt at source
  apply call_mkdir_first _ _ _ source mkdir
  intro reply
  dsimp only [Filesystem.Program.bind]
  split
  · exact readonly_no_mkdir (Retrieval.openAt_readOnly _ _ _)
  · split
    · exact readonly_no_mkdir (Retrieval.openAt_readOnly _ _ _)
    · exact .pure _

-- §FS-host-boundary.ownership: A public traversal mkdir is exactly ensureAt's first call.
-- Later open/stat/privacy checks and their errors cannot invent another creation.
theorem public_mkdir_first (uid : Nat) (parent : UInt64) (name : ByteArray) (create : Bool)
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix (Directories.publicAt uid parent name create) (before ++ [(request, observed)]))
    (mkdir : request.op = .mkdirAt) : create = true ∧ before = [] ∧
      request = {op := .mkdirAt, first := parent, second := 448, left := name} := by
  cases create with
  | false => exact False.elim (no_mkdir (readonly_no_mkdir (Retrieval.publicAt_readOnly _ _ _)) source mkdir)
  | true =>
    unfold Directories.publicAt at source
    simp only [↓reduceIte] at source
    rcases filesystem_last_bind_split _ _ source with opening |
        ⟨opening, result, inside, openingSource, following, shape⟩
    · obtain ⟨empty, operation⟩ := ensure_mkdir_first uid parent name opening mkdir
      exact ⟨rfl, empty, operation⟩
    · cases result with
      | error error => exact False.elim (pure_no_last _ following)
      | ok opened =>
        have profile : RequestProgram (fun request => request.op ≠ .mkdirAt)
            ((SourcePaths.publicHandle opened.fd).bind (fun allowed =>
              pure (allowed.map (fun fd => { opened with fd })))) :=
          request_bind (readonly_no_mkdir (Retrieval.readOnly_snapshot (Snapshot.publicHandle_input _)))
            (fun _ => .pure _)
        exact False.elim (no_mkdir profile following mkdir)

-- §FS-host-boundary.ownership: This chain retains actual successful preceding open/check/close
-- replies. It supplies no current inode role, which the raw physical projection derives.
inductive CompletedWalk (uid : Nat) (create : Bool) :
    Directories.Opened → List ByteArray → List (Request × Reply) → Directories.Opened → List ByteArray → Type where
  | here (directory : Directories.Opened) (names : List ByteArray) : CompletedWalk uid create directory names [] directory names
  | step {current next final : Directories.Opened} {name : ByteArray} {rest remaining : List ByteArray}
      {opening closing tail : List (Request × Reply)}
      (opened : Returns (Directories.publicAt uid current.fd name create) opening (.ok next))
      (closed : Returns (closeResult current.fd (.ok next)) closing (.ok next))
      (following : CompletedWalk uid create next rest tail final remaining) :
      CompletedWalk uid create current (name :: rest) (opening ++ closing ++ tail) final remaining

-- §FS-host-boundary.ownership: An in-progress path has a genuine completed source walk of
-- exactly the visited components, using the same opening and closing acknowledgements.
theorem CompletedWalk.source {uid : Nat} {create : Bool} {initial current : Directories.Opened}
    {names remaining : List ByteArray} {events : List (Request × Reply)}
    (walk : CompletedWalk uid create initial names events current remaining) :
    ∃ visited, names = visited ++ remaining ∧
      Returns (Directories.descend uid create initial visited) events (.ok current) := by
  induction walk with
  | here directory names => exact ⟨[], rfl, .pure _⟩
  | @step initial next final name rest remaining opening closing tail opened closed following ih =>
    obtain ⟨visited, shape, source⟩ := ih
    refine ⟨name :: visited, by simp only [List.cons_append, shape], ?_⟩
    unfold Directories.descend
    rw [List.append_assoc]
    apply Snapshot.returns_bind_join opened
    apply Snapshot.returns_bind_join closed
    exact source

structure WalkMkdir (uid : Nat) (create : Bool) (initial : Directories.Opened) (names : List ByteArray)
    (before : List (Request × Option Reply)) (request : Request) where
  current : Directories.Opened
  name : ByteArray
  rest : List ByteArray
  events : List (Request × Reply)
  walk : CompletedWalk uid create initial names events current (name :: rest)
  trace : before = Publication.completed events
  creating : create = true
  member : name ∈ names
  operation : request = {op := .mkdirAt, first := current.fd, second := 448, left := name}

theorem descend_mkdir_cursor (uid : Nat) (create : Bool) (initial : Directories.Opened) (names : List ByteArray)
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix (Directories.descend uid create initial names) (before ++ [(request, observed)]))
    (mkdir : request.op = .mkdirAt) : Nonempty (WalkMkdir uid create initial names before request) := by
  induction names generalizing initial before with
  | nil => exact False.elim (pure_no_last _ source)
  | cons name rest ih =>
    unfold Directories.descend at source
    rcases filesystem_last_bind_split _ _ source with opening |
        ⟨opening, result, afterOpen, opened, following, openShape⟩
    · obtain ⟨creating, empty, operation⟩ := public_mkdir_first uid initial.fd name create opening mkdir
      exact ⟨⟨initial, name, rest, [], .here _ _, empty, creating, by simp, operation⟩⟩
    · rcases filesystem_last_bind_split _ _ following with closing |
          ⟨closing, closed, afterClose, closeRun, ending, closeShape⟩
      · exact False.elim (no_mkdir
          (readonly_no_mkdir (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))) closing mkdir)
      · cases closed with
        | error error =>
          cases result with
          | error original => exact False.elim (pure_no_last _ ending)
          | ok next => exact False.elim (no_mkdir
              (readonly_no_mkdir (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))) ending mkdir)
        | ok next =>
          have same := (Snapshot.closeResult_provenance _ _ closeRun).1
          cases same
          obtain ⟨cursor⟩ := ih next ending
          refine ⟨⟨cursor.current, cursor.name, cursor.rest, opening ++ closing ++ cursor.events,
            .step opened closeRun cursor.walk, ?_, cursor.creating, by simp [cursor.member], cursor.operation⟩⟩
          simp only [openShape, closeShape, cursor.trace, Publication.completed, List.map_append, List.append_assoc]

private theorem after_other_call {α : Type} (head : Request) (next : Reply → Filesystem.Program α)
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix (.call head next) (before ++ [(request, observed)])) (different : request.op ≠ head.op) :
    ∃ reply inside, before = (head, some reply) :: inside ∧ Prefix (next reply) (inside ++ [(request, observed)]) := by
  cases before with
  | nil => cases observed <;> cases source <;> exact False.elim (different rfl)
  | cons first rest =>
    cases rest with
    | nil =>
      change Prefix (.call head next) [first, (request, observed)] at source
      cases source with
      | returned _ _ reply events following => exact ⟨reply, [], rfl, following⟩
    | cons second rest =>
      change Prefix (.call head next) (first :: second :: (rest ++ [(request, observed)])) at source
      cases source with
      | returned _ _ reply events following => exact ⟨reply, second :: rest, rfl, following⟩

structure ParentMkdir (path : ByteArray) (create : Bool)
    (before : List (Request × Option Reply)) (request : Request) where
  selected : SourcePaths.Started
  selecting : List (Request × Reply)
  started : Returns (SourcePaths.start path) selecting (.ok selected)
  finalName : ByteArray
  named : selected.parts.getLast? = some finalName
  notDot : finalName ≠ ".".toUTF8
  notUp : finalName ≠ "..".toUTF8
  identity : Reply
  successful : nativeError identity = false
  empty : identity.2 = .empty
  bounded : identity.1.toNat ≤ 2 ^ 32 - 1
  base : Directories.Opened
  inspecting : List (Request × Reply)
  inspected : Returns (Directories.inspect identity.1.toNat selected.base) inspecting (.ok base)
  walking : List (Request × Option Reply)
  cursor : WalkMkdir identity.1.toNat create base selected.parts.dropLast walking request
  trace : before = Publication.completed selecting ++ ({op := .euid}, some identity) ::
    (Publication.completed inspecting ++ walking)

-- §FS-host-boundary.ownership: Even an in-progress public path creation has the genuine
-- retained-CWD selection, checked UID, last completed fstat and exact preceding traversal.
theorem parent_mkdir_cursor (path : ByteArray) (create : Bool)
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix (Directories.parent path create) (before ++ [(request, observed)]))
    (mkdir : request.op = .mkdirAt) : Nonempty (ParentMkdir path create before request) := by
  unfold Directories.parent at source
  rcases filesystem_last_bind_split _ _ source with starting |
      ⟨selecting, result, afterSelect, started, following, selectShape⟩
  · exact False.elim (no_mkdir (readonly_no_mkdir
      (Retrieval.readOnly_snapshot (Snapshot.sourceStart_input _))) starting mkdir)
  · cases result with
    | error error => exact False.elim (pure_no_last _ following)
    | ok selected =>
      dsimp only at following
      split at following
      · rename_i finalName named
        split at following
        · exact False.elim (no_mkdir (readonly_no_mkdir
            (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))) following mkdir)
        · rename_i acceptedName
          obtain ⟨identity, afterIdentity, identityShape, afterUid⟩ := after_other_call _ _ following (by rw [mkdir]; decide)
          dsimp only [Filesystem.Program.bind] at afterUid
          split at afterUid
          · exact False.elim (no_mkdir (readonly_no_mkdir
              (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))) afterUid mkdir)
          · rename_i valid
            rcases filesystem_last_bind_split _ _ afterUid with inspecting |
                ⟨inspecting, result, afterInspect, inspected, descending, inspectShape⟩
            · exact False.elim (no_mkdir (readonly_no_mkdir (Retrieval.inspect_readOnly _ _)) inspecting mkdir)
            · cases result with
              | error error => exact False.elim (pure_no_last _ descending)
              | ok base =>
                rcases filesystem_last_bind_split _ _ descending with walking |
                    ⟨walking, result, ending, walked, final, walkShape⟩
                · obtain ⟨cursor⟩ := descend_mkdir_cursor identity.1.toNat create base selected.parts.dropLast walking mkdir
                  have nameFields : finalName ≠ ".".toUTF8 ∧ finalName ≠ "..".toUTF8 := by
                    simpa [Bool.or_eq_true] using acceptedName
                  have identityFields : nativeError identity = false ∧ identity.2.isEmpty = true ∧
                      identity.1.toNat ≤ 2 ^ 32 - 1 := by simpa [Bool.or_eq_true, and_assoc] using valid
                  refine ⟨⟨selected, selecting, started, finalName, named, nameFields.1, nameFields.2,
                    identity, identityFields.1, ?_, identityFields.2.2, base, inspecting, inspected,
                    afterInspect, cursor, ?_⟩⟩
                  · exact ByteArray.size_eq_zero_iff.mp (by simpa only [ByteArray.isEmpty, beq_iff_eq] using identityFields.2.1)
                  · simp only [selectShape, identityShape, inspectShape]
                · exact False.elim (pure_no_last _ final)
      · exact False.elim (no_mkdir (readonly_no_mkdir
          (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))) following mkdir)

end LeanCage.Host.Kernel.ParentTraversal
