import SnapshotProofs.Catalog

namespace LeanCage.Host.Snapshot

open Filesystem

-- §FS-host-boundary.snapshot: Every new blob is linked to the actual file-copy hash call.
theorem acquired_blob_hashes {limits : Limits} {before after : State} {events : List (Request × Reply)}
    (observed : Acquired limits before events after) : BlobEvidence before.blobs events after.blobs := by
  induction observed with
  | unchanged state events => exact fun _ member => .inl member
  | sequence initial final first last => exact blobEvidence_append first last
  | directory parent child prefixName name component notPrivate path pathValue pathPublic opened information stat
      descriptorValue statValue directory appended =>
    rw [appendEntry_blobs _ _ _ appended]
    exact fun _ member => .inl member
  | file parent child prefixName name component notPrivate path pathValue pathPublic opened information stat
      descriptorValue statValue regular linked copied reads closed digest copyValue bounded
      closeValue closeBytes digestSize blobs blobValue appended =>
    rw [appendEntry_blobs _ _ _ appended]
    intro blob member
    rcases (addBlob_provenance _ _ _ blobValue).1 blob member with old | ⟨exactDigest, exactBytes⟩
    · exact .inl old
    · exact .inr ⟨by simp [exactBytes, exactDigest], by simpa only [exactDigest] using digestSize⟩

theorem copyWorkspace_hashed_blobs (workspace : Option ByteArray) (limits : Limits)
    {events : List (Request × Reply)} {state : State}
    (run : Returns (copyWorkspace workspace limits) events (.ok state)) :
    ∀ blob ∈ state.blobs, BlobHashed events blob := by
  intro blob member
  rcases acquired_blob_hashes (copyWorkspace_acquired _ _ run) blob member with impossible | hashed
  · cases impossible
  · exact hashed

theorem hashReplies_subset (sha256 : ByteArray → ByteArray) (all : List (Request × Reply))
    (law : HashReplies sha256 all) (events : List (Request × Reply))
    (subset : ∀ event ∈ events, event ∈ all) : HashReplies sha256 events :=
  fun request reply member => law request reply (subset _ member)

def BlobsCorrect (sha256 : ByteArray → ByteArray) (blobs : List Blob) : Prop :=
  ∀ blob ∈ blobs, blob.digest = sha256 blob.bytes ∧ blob.digest.size = 32

theorem includeStdin_correct (sha256 : ByteArray → ByteArray) (before : List Blob)
    (input digest : Option ByteArray) (events : List (Request × Reply)) {after : List Blob}
    (valid : BlobsCorrect sha256 before) (observed : DigestObservation input digest events)
    (identity : digest = input.map sha256)
    (included : includeStdin before input digest = .ok after) : BlobsCorrect sha256 after := by
  cases input with
  | none =>
    cases digest with
    | none => cases included; exact valid
    | some => exact False.elim observed
  | some bytes =>
    cases digest with
    | none => exact False.elim observed
    | some digest =>
      obtain ⟨_, size⟩ := observed
      have correct : digest = sha256 bytes := Option.some.inj identity
      intro blob member
      rcases (addBlob_provenance _ _ _ included).1 blob member with old | ⟨exactDigest, exactBytes⟩
      · exact valid blob old
      · exact ⟨by simpa only [exactBytes] using exactDigest.trans correct,
          by simpa only [exactDigest] using size⟩

-- §FS-host-boundary.snapshot: A single-op SHA law justifies every returned stored blob digest.
theorem freeze_blobs_correct (workspace : Option ByteArray) (stdin : Stdin) (limits : Limits)
    (sha256 : ByteArray → ByteArray) {events : List (Request × Reply)} {frozen : Frozen}
    (run : Returns (freeze workspace stdin limits) events (.ok frozen))
    (law : HashReplies sha256 events) : BlobsCorrect sha256 frozen.blobs := by
  obtain ⟨_, state, workspaceEvents, stdinEvents, treeEvents, inputEvents, shape,
    workspaceRun, _, _, inputRun, included, _, _, _, _⟩ := freeze_witness _ _ _ run
  have sourceLaw := hashReplies_subset sha256 events law workspaceEvents (by
    intro event member
    rw [shape]
    simp [member])
  have original : BlobsCorrect sha256 state.blobs := by
    intro blob member
    obtain ⟨hashed, size⟩ := copyWorkspace_hashed_blobs _ _ workspaceRun blob member
    exact ⟨sourceLaw _ _ hashed rfl rfl size, size⟩
  exact includeStdin_correct sha256 state.blobs frozen.stdin frozen.stdinDigest inputEvents
    original (identify_provenance _ inputRun) (freeze_hashes _ _ _ _ run law).2 included

-- §FS-host-boundary.snapshot: The caller receives one same-trace source and identity package.
theorem freeze_sources (workspace : Option ByteArray) (stdin : Stdin) (limits : Limits)
    {events : List (Request × Reply)} {frozen : Frozen}
    (run : Returns (freeze workspace stdin limits) events (.ok frozen)) :
    ∃ state workspaceEvents stdinEvents treeEvents inputEvents,
      events = workspaceEvents ++ stdinEvents ++ treeEvents ++ inputEvents ∧
      WorkspaceOrigin workspace limits workspaceEvents state ∧
      Acquired limits {} workspaceEvents state ∧
      StdinObservation stdin limits.stdinBytes frozen.stdin stdinEvents ∧
      DigestObservation frozen.tree frozen.treeDigest treeEvents ∧
      DigestObservation frozen.stdin frozen.stdinDigest inputEvents ∧
      frozen.entries = state.entries ∧ includeStdin state.blobs frozen.stdin frozen.stdinDigest = .ok frozen.blobs := by
  obtain ⟨_, state, workspaceEvents, stdinEvents, treeEvents, inputEvents, shape,
    workspaceRun, stdinRun, treeRun, inputRun, included, tree, entries, _, _⟩ := freeze_witness _ _ _ run
  exact ⟨state, workspaceEvents, stdinEvents, treeEvents, inputEvents, shape,
    copyWorkspace_origin _ _ workspaceRun, copyWorkspace_acquired _ _ workspaceRun,
    copyStdin_provenance _ _ stdinRun, by simpa only [tree] using identify_provenance _ treeRun,
    identify_provenance _ inputRun, entries, included⟩

end LeanCage.Host.Snapshot
