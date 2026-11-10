import SnapshotProofs.Preservation
import SnapshotProofs.SourcePaths
import SnapshotProofs.Enumeration

namespace LeanCage.Host.Snapshot

open Filesystem

def DigestObservation (input digest : Option ByteArray) (events : List (Request × Reply)) : Prop :=
  match input, digest with
  | none, none => events = []
  | some bytes, some digest =>
    events = [({ op := .sha256, left := bytes }, (0, digest))] ∧ digest.size = 32
  | _, _ => False

theorem identify_provenance (input : Option ByteArray) {events : List (Request × Reply)}
    {digest : Option ByteArray} (run : Returns (identify input) events (.ok digest)) :
    DigestObservation input digest events := by
  cases input with
  | none => cases run; rfl
  | some bytes =>
    simp only [identify] at run
    obtain ⟨first, result, last, hashed, final, shape⟩ := returns_bind_split _ _ run
    cases result with
    | error error => cases final
    | ok value =>
      obtain ⟨rfl, equal⟩ := returns_pure_eq final
      cases equal
      obtain ⟨reply, exactEvents, zero, exactBytes, size⟩ := hash_provenance _ hashed
      have replyExact : reply = (0, value) := Prod.ext zero exactBytes
      exact ⟨by simpa only [List.append_nil, exactEvents, replyExact] using shape, size⟩

def StdinObservation (input : Stdin) (limit : Nat) (bytes : Option ByteArray)
    (events : List (Request × Reply)) : Prop :=
  match input with
  | .absent => bytes = none ∧ events = []
  | .bytes provided => bytes = some provided ∧ events = [] ∧ provided.size ≤ limit
  | .file path => ∃ copied : CopiedFile,
      bytes = some copied.bytes ∧ copied.bytes.size ≤ limit ∧ SourceCopiedFile path limit events copied

theorem copyStdin_provenance (input : Stdin) (limit : Nat)
    {events : List (Request × Reply)} {bytes : Option ByteArray}
    (run : Returns (copyStdin input limit) events (.ok bytes)) :
    StdinObservation input limit bytes events := by
  cases input with
  | absent => cases run; exact ⟨rfl, rfl⟩
  | bytes provided =>
    simp only [copyStdin] at run
    split at run
    · rename_i within
      cases run
      exact ⟨rfl, rfl, within⟩
    · cases run
  | file path =>
    simp only [copyStdin] at run
    obtain ⟨first, result, last, copied, final, shape⟩ := returns_bind_split _ _ run
    cases result with
    | error error => cases final
    | ok value =>
      obtain ⟨rfl, equal⟩ := returns_pure_eq final
      cases equal
      have observed := sourceCopyFile_source _ _ copied
      have bounded : value.bytes.size ≤ limit := by
        obtain ⟨_, _, _, _, _, _, _, bound, _⟩ := observed
        exact bound
      exact ⟨value, rfl, bounded, by simpa only [shape, List.append_nil] using observed⟩

theorem stdin_observation_bound (input : Stdin) (limit : Nat) (bytes : Option ByteArray)
    (events : List (Request × Reply)) (observed : StdinObservation input limit bytes events) :
    ∀ value, bytes = some value → value.size ≤ limit := by
  cases input with
  | absent => simp only [StdinObservation] at observed; simp [observed.1]
  | bytes provided =>
    rcases observed with ⟨rfl, _, bounded⟩
    simpa using bounded
  | file path =>
    rcases observed with ⟨copied, rfl, bounded, _⟩
    simpa using bounded

def FreezeWitness (workspace : Option ByteArray) (stdin : Stdin) (limits : Limits)
    (events : List (Request × Reply)) (frozen : Frozen) : Prop :=
  limits.supported = true ∧ ∃ state : State,
    ∃ workspaceEvents stdinEvents treeEvents inputEvents,
      events = workspaceEvents ++ stdinEvents ++ treeEvents ++ inputEvents ∧
      Returns (copyWorkspace workspace limits) workspaceEvents (.ok state) ∧
      Returns (copyStdin stdin limits.stdinBytes) stdinEvents (.ok frozen.stdin) ∧
      Returns (identify (workspace.map (fun _ => state.tree))) treeEvents (.ok frozen.treeDigest) ∧
      Returns (identify frozen.stdin) inputEvents (.ok frozen.stdinDigest) ∧
      includeStdin state.blobs frozen.stdin frozen.stdinDigest = .ok frozen.blobs ∧
      frozen.tree = workspace.map (fun _ => state.tree) ∧ frozen.entries = state.entries ∧
      frozen.count = state.count ∧ frozen.workspaceBytes = state.total

-- §FS-host-boundary.snapshot: Returned bytes, metadata and hashes belong to this invocation.
theorem freeze_witness (workspace : Option ByteArray) (stdin : Stdin) (limits : Limits)
    {events : List (Request × Reply)} {frozen : Frozen}
    (run : Returns (freeze workspace stdin limits) events (.ok frozen)) :
    FreezeWitness workspace stdin limits events frozen := by
  unfold freeze at run
  split at run
  · cases run
  · rename_i supported
    have supportedTrue : limits.supported = true := by simpa using supported
    obtain ⟨workspaceEvents, copied, rest, workspaceRun, afterWorkspace, shapeWorkspace⟩ :=
      returns_bind_split _ _ run
    cases copied with
    | error error => cases afterWorkspace
    | ok state =>
      obtain ⟨stdinEvents, input, rest, stdinRun, afterStdin, shapeStdin⟩ :=
        returns_bind_split _ _ afterWorkspace
      cases input with
      | error error => cases afterStdin
      | ok input =>
        dsimp only at afterStdin
        obtain ⟨treeEvents, treeDigest, rest, treeRun, afterTree, shapeTree⟩ :=
          returns_bind_split _ _ afterStdin
        cases treeDigest with
        | error error => cases afterTree
        | ok treeDigest =>
          obtain ⟨inputEvents, inputDigest, last, inputRun, final, shapeInput⟩ :=
            returns_bind_split _ _ afterTree
          cases inputDigest with
          | error error => cases final
          | ok inputDigest =>
            obtain ⟨rfl, same⟩ := returns_pure_eq final
            cases linked : includeStdin state.blobs input inputDigest with
            | error error => simp only [linked, Except.map] at same; cases same
            | ok blobs =>
              simp only [linked, Except.map] at same
              cases same
              refine ⟨supportedTrue, state, workspaceEvents, stdinEvents, treeEvents, inputEvents,
                ?_, workspaceRun, stdinRun, treeRun, inputRun, linked, rfl, rfl, rfl, rfl⟩
              simp only [shapeWorkspace, shapeStdin, shapeTree, shapeInput,
                List.append_nil, List.append_assoc]

theorem supported_properties (limits : Limits) (supported : limits.supported = true) :
    limits.workspaceBytes ≤ workspaceMax ∧ 2 ≤ limits.workspaceInodes ∧
      limits.workspaceInodes ≤ inodeMax ∧ limits.stdinBytes ≤ stdinMax := by
  simpa [Limits.supported, and_assoc] using supported

-- §FS-host-boundary.snapshot: Byte/inode limits describe the exact canonical tree being hashed.
theorem freeze_bounds (workspace : Option ByteArray) (stdin : Stdin) (limits : Limits)
    {events : List (Request × Reply)} {frozen : Frozen}
    (run : Returns (freeze workspace stdin limits) events (.ok frozen)) :
    frozen.count = 2 + frozen.entries.size ∧ frozen.workspaceBytes = entriesBytes frozen.entries ∧
      frozen.count ≤ limits.workspaceInodes ∧ frozen.workspaceBytes ≤ limits.workspaceBytes ∧
      frozen.tree = workspace.map (fun _ => canonicalTree frozen.entries) ∧
      (∀ tree, frozen.tree = some tree → tree.size ≤ treeMax) ∧
      (∀ bytes, frozen.stdin = some bytes → bytes.size ≤ limits.stdinBytes) ∧
      (entryNames frozen.entries).Nodup := by
  obtain ⟨supported, state, workspaceEvents, stdinEvents, treeEvents, inputEvents, _,
    workspaceRun, stdinRun, _, _, _, tree, entries, count, total⟩ := freeze_witness _ _ _ run
  have valid := post_returns (copyWorkspace_state_valid workspace limits
    (supported_properties limits supported).2.1) workspaceRun
  have stdinBound := stdin_observation_bound _ _ _ _ (copyStdin_provenance _ _ stdinRun)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, stdinBound, ?_⟩
  · simpa only [entries, count] using valid.count_exact
  · simpa only [entries, total] using valid.bytes_exact
  · simpa only [count] using valid.inodes_bound
  · simpa only [total] using valid.bytes_bound
  · simpa only [entries, valid.tree_exact] using tree
  · intro bytes present
    rw [tree] at present
    cases workspace with
    | none => cases present
    | some path =>
      simp only [Option.map_some, Option.some.injEq] at present
      simpa only [← present] using valid.tree_bound
  · simpa only [entries] using valid.unique

-- §AR-host-boundary.interfaces: One successful primitive supplies the crypto law.
def HashReplies (sha256 : ByteArray → ByteArray) (events : List (Request × Reply)) : Prop :=
  ∀ request reply, (request, reply) ∈ events → request.op = .sha256 → reply.1 = 0 →
    reply.2.size = 32 → reply.2 = sha256 request.left

theorem observed_digest (sha256 : ByteArray → ByteArray)
    (all : List (Request × Reply)) (law : HashReplies sha256 all)
    (input digest : Option ByteArray) (events : List (Request × Reply))
    (observed : DigestObservation input digest events)
    (subset : ∀ event ∈ events, event ∈ all) : digest = input.map sha256 := by
  cases input with
  | none => cases digest <;> simp_all [DigestObservation]
  | some bytes =>
    cases digest with
    | none => exact False.elim observed
    | some digest =>
      obtain ⟨shape, size⟩ := observed
      have member : ({ op := .sha256, left := bytes }, (0, digest)) ∈ all :=
        subset _ (by simp [shape])
      exact congrArg some (law _ _ member rfl rfl size)

-- §FS-host-boundary.snapshot: Both identities hash the same returned tree/stdin bytes in one trace.
theorem freeze_hashes (workspace : Option ByteArray) (stdin : Stdin) (limits : Limits)
    (sha256 : ByteArray → ByteArray) {events : List (Request × Reply)} {frozen : Frozen}
    (run : Returns (freeze workspace stdin limits) events (.ok frozen))
    (law : HashReplies sha256 events) :
    frozen.treeDigest = frozen.tree.map sha256 ∧ frozen.stdinDigest = frozen.stdin.map sha256 := by
  obtain ⟨_, state, workspaceEvents, stdinEvents, treeEvents, inputEvents, shape,
    _, _, treeRun, inputRun, _, tree, _, _, _⟩ := freeze_witness _ _ _ run
  constructor
  · have observed := identify_provenance _ treeRun
    have same := observed_digest sha256 events law _ _ treeEvents observed (by
      intro event member
      rw [shape]
      simp only [List.mem_append]
      simp [member])
    simpa only [← tree] using same
  · apply observed_digest sha256 events law _ _ inputEvents (identify_provenance _ inputRun)
    intro event member
    rw [shape]
    simp only [List.mem_append]
    simp [member]

end LeanCage.Host.Snapshot
