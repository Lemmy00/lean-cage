import SnapshotProofs.Acquisition

namespace LeanCage.Host.Snapshot

open Filesystem

def blobBytes (blobs : List Blob) : Nat :=
  blobs.foldr (fun blob total => blob.bytes.size + total) 0

theorem addBlob_budget (before : List Blob) (digest bytes : ByteArray) {after : List Blob}
    (accepted : addBlob before digest bytes = .ok after) :
    blobBytes after ≤ blobBytes before + bytes.size ∧ after.length ≤ before.length + 1 := by
  unfold addBlob at accepted
  split at accepted
  · cases accepted
    simp only [blobBytes, List.foldr_cons, List.length_cons]
    omega
  · split at accepted
    · cases accepted
      constructor <;> omega
    · cases accepted

def BudgetDelta (before after : State) : Prop :=
  blobBytes after.blobs + before.total ≤ blobBytes before.blobs + after.total ∧
    after.blobs.length + before.entries.size ≤ before.blobs.length + after.entries.size

-- §FS-host-boundary.snapshot: Each retained blob is charged to the corresponding copied file.
theorem acquired_budget {limits : Limits} {before after : State} {events : List (Request × Reply)}
    (observed : Acquired limits before events after) : BudgetDelta before after := by
  induction observed with
  | unchanged state events => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | sequence initial final first last =>
    unfold BudgetDelta at *
    omega
  | directory parent child prefixName name component notPrivate path pathValue pathPublic opened information stat
      descriptorValue statValue directory appended =>
    obtain ⟨entries, _, _, total, blobs⟩ := appendEntry_update _ _ _ appended
    unfold BudgetDelta
    rw [entries, total, blobs]
    simp only [Entry.size, Nat.add_zero, Array.size_push]
    constructor <;> omega
  | file parent child prefixName name component notPrivate path pathValue pathPublic opened information stat
      descriptorValue statValue regular linked copied reads closed digest copyValue bounded
      closeValue closeBytes digestSize blobs blobValue appended =>
    obtain ⟨entries, _, _, total, exactBlobs⟩ := appendEntry_update _ _ _ appended
    have budget := addBlob_budget _ _ _ blobValue
    unfold BudgetDelta
    rw [entries, total, exactBlobs]
    simp only [Entry.size, Array.size_push]
    constructor <;> omega

theorem copyWorkspace_blob_budget (workspace : Option ByteArray) (limits : Limits)
    {events : List (Request × Reply)} {state : State}
    (run : Returns (copyWorkspace workspace limits) events (.ok state)) :
    blobBytes state.blobs ≤ state.total ∧ state.blobs.length ≤ state.entries.size := by
  have delta := acquired_budget (copyWorkspace_acquired _ _ run)
  simpa only [BudgetDelta, blobBytes, List.foldr_nil, Array.size_empty, List.length_nil, Nat.zero_add,
    Nat.add_zero] using delta

-- §FS-host-boundary.snapshot: The next copied file fits alongside already retained workspace blobs.
theorem workspace_candidate_budget (limits : Limits) (state : State) (fd : UInt64)
    (valid : StateValid limits state) (retained : blobBytes state.blobs ≤ state.total)
    {events : List (Request × Reply)} {copied : CopiedFile}
    (run : Returns (copyOpened fd (limits.workspaceBytes - state.total)) events (.ok copied)) :
    blobBytes state.blobs + copied.bytes.size ≤ limits.workspaceBytes := by
  have copiedBound := (copyOpened_provenance _ _ run).1
  have totalBound := valid.bytes_bound
  omega

theorem includeStdin_budget (before : List Blob) (input digest : Option ByteArray) {after : List Blob}
    (accepted : includeStdin before input digest = .ok after) :
    blobBytes after ≤ blobBytes before + (input.map ByteArray.size).getD 0 ∧
      after.length ≤ before.length + 1 := by
  cases input with
  | none =>
    cases digest with
    | none => cases accepted; constructor <;> simp
    | some => cases accepted
  | some bytes =>
    cases digest with
    | none => cases accepted
    | some digest => exact addBlob_budget _ _ _ accepted

-- §FS-host-boundary.snapshot: Charge stdin once in the retained blob byte/inode budget.
theorem freeze_blob_budget (workspace : Option ByteArray) (stdin : Stdin) (limits : Limits)
    {events : List (Request × Reply)} {frozen : Frozen}
    (run : Returns (freeze workspace stdin limits) events (.ok frozen)) :
    blobBytes frozen.blobs ≤ limits.workspaceBytes + limits.stdinBytes ∧
      frozen.blobs.length ≤ frozen.entries.size + 1 := by
  obtain ⟨supported, state, workspaceEvents, stdinEvents, treeEvents, inputEvents, _,
    workspaceRun, stdinRun, _, _, included, _, entries, _, total⟩ := freeze_witness _ _ _ run
  have original := copyWorkspace_blob_budget _ _ workspaceRun
  have added := includeStdin_budget _ _ _ included
  have inputBound := stdin_observation_bound _ _ _ _ (copyStdin_provenance _ _ stdinRun)
  have valid := post_returns (copyWorkspace_state_valid workspace limits
    (supported_properties limits supported).2.1) workspaceRun
  have sourceBound := valid.bytes_bound
  have stdinSize : (frozen.stdin.map ByteArray.size).getD 0 ≤ limits.stdinBytes := by
    cases value : frozen.stdin with
    | none => simp
    | some bytes => simpa only [value, Option.map_some, Option.getD_some] using inputBound bytes value
  constructor
  · omega
  · rw [entries]
    omega

end LeanCage.Host.Snapshot
