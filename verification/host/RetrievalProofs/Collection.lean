import RetrievalProofs.Traversal

namespace LeanCage.Host.Retrieval

open Filesystem

def BlobSelection (before : List Transport.Blob) (digest bytes : ByteArray)
    (after : List Transport.Blob) : Prop :=
  ((∀ blob ∈ before, blob.digest ≠ digest) ∧ after = ⟨digest, bytes⟩ :: before) ∨
    ((∃ blob ∈ before, blob.digest = digest ∧ blob.content = bytes) ∧ after = before)

inductive Collection (uid : Nat) (root : UInt64) (limits : Transport.Limits) :
    List Artifacts.Node → Collected → List (Request × Reply) → Collected → Prop where
  | done (state : Collected) : Collection uid root limits [] state [] state
  | omitted (path : Artifacts.ExportPath) (rest : List Artifacts.Node) (before after : Collected)
      (events : List (Request × Reply)) (room : before.count < limits.inodesMax)
      (tail : Collection uid root limits rest { before with count := before.count + 1 } events after) :
      Collection uid root limits (.omitted path :: rest) before events after
  | directory (path : Artifacts.ExportPath) (rest : List Artifacts.Node) (before after : Collected)
      (opening following : List (Request × Reply)) (room : before.count < limits.inodesMax)
      (source : Traversal uid (fun _ => pure (.ok ())) root path.components opening ())
      (tail : Collection uid root limits rest { before with count := before.count + 1 } following after) :
      Collection uid root limits (.directory path :: rest) before (opening ++ following) after
  | file (path : Artifacts.ExportPath) (executable : Bool) (size : Nat) (digest : String)
      (rest : List Artifacts.Node) (before after : Collected) (name : String) (copied : CopiedFile)
      (hashed : ByteArray) (blobs : List Transport.Blob) (copies hashes following : List (Request × Reply))
      (room : before.count < limits.inodesMax) (fits : before.total + size ≤ limits.workspaceMax)
      (leaf : path.components.getLast? = some name)
      (source : Traversal uid (fun parent => copyAt parent name.toUTF8 size)
        root path.components.dropLast copies copied)
      (bytes : copied.bytes.size = size) (mode : (copied.stat.mode &&& 73 != 0) = executable)
      (hash : Artifacts.HashSeen hashes copied.bytes hashed) (identity : Snapshot.hex hashed = digest)
      (selection : BlobSelection before.blobs digest.toUTF8 copied.bytes blobs)
      (tail : Collection uid root limits rest ⟨blobs, before.total + size, before.count + 1⟩ following after) :
      Collection uid root limits (.file path executable size digest :: rest) before
        (copies ++ hashes ++ following) after

-- §FS-host-boundary.publication: Record every copied file before deduplication.
theorem collect_source (uid : Nat) (root : UInt64) (limits : Transport.Limits)
    (nodes : List Artifacts.Node) (before : Collected)
    {events : List (Request × Reply)} {after : Collected}
    (run : Returns (collect uid root limits nodes before).run events (.ok after)) :
    Collection uid root limits nodes before events after := by
  induction nodes generalizing before events after with
  | nil => cases run; exact .done _
  | cons node rest ih =>
    simp only [collect] at run
    split at run
    · cases run
    · rename_i room
      have countRoom : before.count < limits.inodesMax := by omega
      cases node with
      | omitted path => exact .omitted path rest before after events countRoom (ih _ run)
      | directory path =>
        dsimp only at run
        obtain ⟨opening, openedUnit, following, opened, tail, shape⟩ := checked_bind_split run
        cases openedUnit
        have observed := Collection.directory path rest before after opening following countRoom
          (under_source _ _ _ _ opened) (ih _ tail)
        simpa only [shape] using observed
      | file path executable size digest =>
        dsimp only at run
        split at run
        · cases run
        · rename_i fits
          split at run
          · rename_i name leaf
            obtain ⟨copies, copied, last, copiedRun, afterCopy, shape⟩ := checked_bind_split run
            split at afterCopy
            · cases afterCopy
            · rename_i copiedMatches
              obtain ⟨hashes, hashed, following, hashRun, final, hashShape⟩ := checked_bind_split afterCopy
              split at final
              · cases final
              · rename_i digestMatches
                have fields : copied.bytes.size = size ∧ (copied.stat.mode &&& 73 != 0) = executable := by
                  simpa [Bool.or_eq_true] using copiedMatches
                have hashIdentity : Snapshot.hex hashed = digest := by simpa using digestMatches
                have observedHash := Artifacts.hash_returned copied.bytes hashed hashes hashRun
                have traversal := under_source _ _ _ _ copiedRun
                split at final
                · rename_i absent
                  have fresh : ∀ blob ∈ before.blobs, blob.digest ≠ digest.toUTF8 := by
                    simpa only [List.find?_eq_none, Bool.not_eq_true, beq_eq_false_iff_ne] using absent
                  have tail := ih _ final
                  have observed := Collection.file path executable size digest rest before after name copied
                    hashed _ copies hashes following countRoom (by omega) leaf traversal fields.1 fields.2
                    observedHash hashIdentity (.inl ⟨fresh, rfl⟩) tail
                  simpa only [shape, hashShape, List.append_assoc] using observed
                · rename_i prior selected
                  split at final
                  · rename_i bytesSame
                    have priorMember := List.mem_of_find?_eq_some selected
                    have priorDigest : prior.digest = digest.toUTF8 := by
                      simpa only [beq_iff_eq] using List.find?_some selected
                    have sameBytes : prior.content = copied.bytes := by simpa only [beq_iff_eq] using bytesSame
                    have tail := ih _ final
                    have observed := Collection.file path executable size digest rest before after name copied
                      hashed _ copies hashes following countRoom (by omega) leaf traversal fields.1 fields.2
                      observedHash hashIdentity (.inr ⟨⟨prior, priorMember, priorDigest, sameBytes⟩, rfl⟩) tail
                    simpa only [shape, hashShape, List.append_assoc] using observed
                  · cases final
          · cases run

theorem collection_bounds {uid : Nat} {root : UInt64} {limits : Transport.Limits}
    {nodes : List Artifacts.Node} {before after : Collected} {events : List (Request × Reply)}
    (observed : Collection uid root limits nodes before events after)
    (count : before.count ≤ limits.inodesMax) (bytes : before.total ≤ limits.workspaceMax) :
    after.count ≤ limits.inodesMax ∧ after.total ≤ limits.workspaceMax := by
  induction observed with
  | done => exact ⟨count, bytes⟩
  | omitted path rest before after events room tail ih => exact ih (by dsimp; omega) bytes
  | directory path rest before after opening following room source tail ih => exact ih (by dsimp; omega) bytes
  | file path executable size digest rest before after name copied hashed blobs copies hashes following
      room fits leaf source copiedBytes mode hash identity selection tail ih =>
    exact ih (by dsimp; omega) fits

def blobBytes (blobs : List Transport.Blob) : Nat :=
  blobs.foldr (fun blob total => blob.content.size + total) 0

theorem blobSelection_budget {before after : List Transport.Blob} {digest bytes : ByteArray}
    (selected : BlobSelection before digest bytes after) :
    blobBytes after ≤ blobBytes before + bytes.size ∧ after.length ≤ before.length + 1 := by
  rcases selected with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · simp only [blobBytes, List.foldr_cons, List.length_cons]
    constructor <;> omega
  · constructor <;> omega

-- §FS-host-boundary.publication: Retained blobs and one current copy fit the charged file budget.
theorem collection_blob_budget {uid : Nat} {root : UInt64} {limits : Transport.Limits}
    {nodes : List Artifacts.Node} {before after : Collected} {events : List (Request × Reply)}
    (observed : Collection uid root limits nodes before events after) :
    blobBytes after.blobs + before.total ≤ blobBytes before.blobs + after.total ∧
      after.blobs.length + before.count ≤ before.blobs.length + after.count := by
  induction observed with
  | done => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | omitted path rest before after events room tail ih => dsimp only at ih; constructor <;> omega
  | directory path rest before after opening following room source tail ih =>
    dsimp only at ih
    constructor <;> omega
  | file path executable size digest rest before after name copied hashed blobs copies hashes following
      room fits leaf source copiedBytes mode hash identity selection tail ih =>
    have selected := blobSelection_budget selection
    dsimp only at ih
    rw [copiedBytes] at selected
    constructor <;> omega

theorem blobSelection_unique {before after : List Transport.Blob} {digest bytes : ByteArray}
    (selected : BlobSelection before digest bytes after) (unique : (before.map Transport.Blob.digest).Nodup) :
    (after.map Transport.Blob.digest).Nodup := by
  rcases selected with ⟨fresh, rfl⟩ | ⟨_, rfl⟩
  · apply List.nodup_cons.mpr
    constructor
    · intro member
      obtain ⟨blob, present, equal⟩ := List.mem_map.mp member
      exact fresh blob present equal
    · exact unique
  · exact unique

theorem collection_unique {uid : Nat} {root : UInt64} {limits : Transport.Limits}
    {nodes : List Artifacts.Node} {before after : Collected} {events : List (Request × Reply)}
    (observed : Collection uid root limits nodes before events after)
    (unique : (before.blobs.map Transport.Blob.digest).Nodup) :
    (after.blobs.map Transport.Blob.digest).Nodup := by
  induction observed with
  | done => exact unique
  | omitted path rest before after events room tail ih => exact ih unique
  | directory path rest before after opening following room source tail ih => exact ih unique
  | file path executable size digest rest before after name copied hashed blobs copies hashes following
      room fits leaf source copiedBytes mode hash identity selection tail ih =>
    exact ih (blobSelection_unique selection unique)

def ExportObservation (uid : Nat) (stage : UInt64) (limits : Transport.Limits) (raw : ByteArray)
    (events : List (Request × Reply)) (blobs : List Transport.Blob) : Prop :=
  ∃ manifest root opening copying closing collected,
    events = opening ++ copying ++ closing ∧ Artifacts.parseManifest limits raw = .ok manifest ∧
    DirectoryOpening uid stage "export".toUTF8 opening root ∧
    Collection uid root.fd limits manifest.entries.toList {} copying collected ∧
    Returns (closeResult root.fd (.ok collected)) closing (.ok collected) ∧ blobs = collected.blobs.reverse

-- §FS-host-boundary.publication: Manifest, retained export root and copies share one trace.
theorem exportBlobs_source (uid : Nat) (stage : UInt64) (limits : Transport.Limits) (raw : ByteArray)
    {events : List (Request × Reply)} {blobs : List Transport.Blob}
    (run : Returns (exportBlobs uid stage limits raw) events (.ok blobs)) :
    ExportObservation uid stage limits raw events blobs := by
  unfold exportBlobs at run
  split at run
  · cases run
  · rename_i manifest parsed
    obtain ⟨opening, result, rest, openedRun, afterOpen, shape⟩ := Snapshot.returns_bind_split _ _ run
    cases result with
    | error => cases afterOpen
    | ok root =>
      obtain ⟨copying, collected, last, copiedRun, afterCopy, copyShape⟩ :=
        Snapshot.returns_bind_split _ _ afterOpen
      obtain ⟨closing, closed, finalEvents, closedRun, final, closeShape⟩ :=
        Snapshot.returns_bind_split _ _ afterCopy
      cases closed with
      | error => cases final
      | ok closed =>
        obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq final
        cases same
        have collectedValue := (Snapshot.closeResult_provenance _ _ closedRun).1
        cases collectedValue
        exact ⟨manifest, root, opening, copying, closing, closed,
          by simpa only [copyShape, closeShape, List.append_nil, List.append_assoc] using shape,
          parsed, directoryOpening_source _ _ _ openedRun, collect_source _ _ _ _ _ copiedRun,
          closedRun, rfl⟩

def ManifestObservation (uid : Nat) (stage : UInt64) (limits : Transport.Limits)
    (manifest : Option ByteArray) (events : List (Request × Reply)) (blobs : List Transport.Blob) : Prop :=
  match manifest with
  | none => events = [] ∧ blobs = []
  | some raw => ExportObservation uid stage limits raw events blobs

theorem manifestBlobs_source (uid : Nat) (stage : UInt64) (limits : Transport.Limits)
    (manifest : Option ByteArray) {events : List (Request × Reply)} {blobs : List Transport.Blob}
    (run : Returns (manifestBlobs uid stage limits manifest) events (.ok blobs)) :
    ManifestObservation uid stage limits manifest events blobs := by
  cases manifest with
  | none => cases run; exact ⟨rfl, rfl⟩
  | some raw => exact exportBlobs_source _ _ _ _ run

end LeanCage.Host.Retrieval
