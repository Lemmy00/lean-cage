import SnapshotProofs.Budget

namespace LeanCage.Host.Snapshot

open Filesystem

def Backed (entries : Array Entry) (blobs : List Blob) : Prop :=
  ∀ path executable size digest, Entry.file path executable size digest ∈ entries.toList →
    ∃ blob ∈ blobs, blob.digest = digest ∧ blob.bytes.size = size

def Referenced (entries : Array Entry) (blob : Blob) : Prop :=
  ∃ path executable size, Entry.file path executable size blob.digest ∈ entries.toList ∧
    blob.bytes.size = size

structure Catalog (entries : Array Entry) (blobs : List Blob) : Prop where
  backed : Backed entries blobs
  referenced : ∀ blob ∈ blobs, Referenced entries blob
  unique : (blobs.map Blob.digest).Nodup

theorem initial_catalog : Catalog #[] [] := by
  constructor
  · intro path executable size digest member
    cases member
  · intro blob member
    cases member
  · simp

theorem catalog_directory (entries : Array Entry) (blobs : List Blob) (path : RelativePath)
    (before : Catalog entries blobs) : Catalog (entries.push (.directory path)) blobs := by
  constructor
  · intro file executable size digest member
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
    rcases member with old | impossible
    · exact before.backed _ _ _ _ old
    · cases impossible
  · intro blob member
    obtain ⟨file, executable, size, present, exactSize⟩ := before.referenced blob member
    exact ⟨file, executable, size, by simp only [Array.toList_push, List.mem_append]; exact .inl present, exactSize⟩
  · exact before.unique

-- §FS-host-boundary.snapshot: A new file retains every prior blob and exactly its copied data.
theorem catalog_file (entries : Array Entry) (before : List Blob) (path : RelativePath)
    (executable : Bool) (digest bytes : ByteArray) {after : List Blob}
    (valid : Catalog entries before) (added : addBlob before digest bytes = .ok after) :
    Catalog (entries.push (.file path executable bytes.size digest)) after := by
  constructor
  · intro file flag size key member
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
    rcases member with old | same
    · obtain ⟨blob, present, exactDigest, exactSize⟩ := valid.backed _ _ _ _ old
      exact ⟨blob, addBlob_keeps _ _ _ added blob present, exactDigest, exactSize⟩
    · cases same
      obtain ⟨blob, present, exactDigest, exactBytes⟩ := (addBlob_provenance _ _ _ added).2
      exact ⟨blob, present, exactDigest, by rw [exactBytes]⟩
  · intro blob member
    rcases (addBlob_provenance _ _ _ added).1 blob member with old | ⟨exactDigest, exactBytes⟩
    · obtain ⟨file, flag, size, present, exactSize⟩ := valid.referenced blob old
      exact ⟨file, flag, size, by simp only [Array.toList_push, List.mem_append]; exact .inl present, exactSize⟩
    · refine ⟨path, executable, bytes.size, ?_, by rw [exactBytes]⟩
      rw [exactDigest]
      simp
  · exact addBlob_unique _ _ _ valid.unique added

theorem acquired_catalog {limits : Limits} {before after : State} {events : List (Request × Reply)}
    (observed : Acquired limits before events after) (valid : Catalog before.entries before.blobs) :
    Catalog after.entries after.blobs := by
  induction observed with
  | unchanged => exact valid
  | sequence initial final first last => exact last (first valid)
  | directory parent child prefixName name component notPrivate path pathValue pathPublic opened information stat
      descriptorValue statValue directory appended =>
    obtain ⟨entries, _, _, _, blobs⟩ := appendEntry_update _ _ _ appended
    rw [entries, blobs]
    exact catalog_directory _ _ _ valid
  | file parent child prefixName name component notPrivate path pathValue pathPublic opened information stat
      descriptorValue statValue regular linked copied reads closed digest copyValue bounded
      closeValue closeBytes digestSize blobs blobValue appended =>
    obtain ⟨entries, _, _, _, exactBlobs⟩ := appendEntry_update _ _ _ appended
    rw [entries, exactBlobs]
    exact catalog_file _ _ _ _ _ _ valid blobValue

def FinalCatalog (entries : Array Entry) (blobs : List Blob) (input digest : Option ByteArray) : Prop :=
  Backed entries blobs ∧
    (∀ blob ∈ blobs, Referenced entries blob ∨ (input = some blob.bytes ∧ digest = some blob.digest)) ∧
    (blobs.map Blob.digest).Nodup ∧
    (∀ bytes key, input = some bytes → digest = some key →
      ∃ blob ∈ blobs, blob.digest = key ∧ blob.bytes = bytes)

theorem includeStdin_catalog (entries : Array Entry) (before : List Blob) (input digest : Option ByteArray)
    {after : List Blob} (valid : Catalog entries before)
    (added : includeStdin before input digest = .ok after) : FinalCatalog entries after input digest := by
  cases input with
  | none =>
    cases digest with
    | some => cases added
    | none =>
      cases added
      exact ⟨valid.backed, fun blob member => .inl (valid.referenced blob member), valid.unique,
        by intro bytes key impossible; cases impossible⟩
  | some bytes =>
    cases digest with
    | none => cases added
    | some key =>
      refine ⟨?_, ?_, addBlob_unique _ _ _ valid.unique added, ?_⟩
      · intro file executable size digest member
        obtain ⟨blob, present, exactDigest, exactSize⟩ := valid.backed _ _ _ _ member
        exact ⟨blob, addBlob_keeps _ _ _ added blob present, exactDigest, exactSize⟩
      · intro blob member
        rcases (addBlob_provenance _ _ _ added).1 blob member with old | ⟨exactDigest, exactBytes⟩
        · exact .inl (valid.referenced blob old)
        · exact .inr ⟨congrArg some exactBytes.symm, congrArg some exactDigest.symm⟩
      · intro provided digest exactInput exactDigest
        cases exactInput
        cases exactDigest
        exact (addBlob_provenance _ _ _ added).2

-- §FS-host-boundary.snapshot: The stored blob set is exactly the file/stdin reference set.
theorem freeze_catalog (workspace : Option ByteArray) (stdin : Stdin) (limits : Limits)
    {events : List (Request × Reply)} {frozen : Frozen}
    (run : Returns (freeze workspace stdin limits) events (.ok frozen)) :
    FinalCatalog frozen.entries frozen.blobs frozen.stdin frozen.stdinDigest := by
  obtain ⟨_, state, workspaceEvents, stdinEvents, treeEvents, inputEvents, _,
    workspaceRun, _, _, _, included, _, entries, _, _⟩ := freeze_witness _ _ _ run
  have original := acquired_catalog (copyWorkspace_acquired _ _ workspaceRun) initial_catalog
  simpa only [entries] using includeStdin_catalog _ _ _ _ original included

end LeanCage.Host.Snapshot
