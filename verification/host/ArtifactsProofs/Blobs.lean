import ArtifactsProofs.Effects
import Std.Data.TreeMap.Lemmas

namespace LeanCage.Host.Artifacts

open Filesystem

def BlobState.IndexSound (state : BlobState) : Prop :=
  ∀ key blob, state.index[key]? = some blob → blob ∈ state.values.toList ∧ blob.key = key

theorem blob_index_empty : BlobState.IndexSound {} := by
  intro key blob lookup
  simp at lookup

theorem blob_index_insert (state : BlobState) (sound : state.IndexSound) (blob : CheckedBlob) :
    (state.insert blob).IndexSound := by
  intro key value lookup
  change (state.index.insert blob.key blob)[key]? = some value at lookup
  rw [Std.TreeMap.getElem?_insert] at lookup
  split at lookup
  · rename_i same
    have keyEqual : blob.key = key := by simpa using same
    cases lookup
    exact ⟨by simp [BlobState.insert], keyEqual⟩
  · have previous := sound key value lookup
    exact ⟨by simpa only [BlobState.insert, Array.toList_push, List.mem_append, List.mem_singleton] using
      (Or.inl previous.1), previous.2⟩

private theorem error_cannot_return {α : Type} (error : Failure) (value : α)
    (events : List (Request × Reply)) (run : Returns (.pure (.error error : Result α)) events (.ok value)) : False := by
  have same := (Snapshot.returns_pure_eq run).2
  cases same

-- §FS-host-boundary.artifacts: New digest values come from actual hash calls on the source bytes.
theorem checkBlobs_provenance (limits : Transport.Limits) (sources : List Transport.Blob)
    (before after : BlobState) (events : List (Request × Reply))
    (run : Returns (checkBlobs limits sources before) events (.ok after)) :
    ∀ blob ∈ after.values.toList, blob ∈ before.values.toList ∨
      ∃ source ∈ sources, blob.source = source ∧ HashSeen events source.content blob.digest := by
  induction sources generalizing before after events with
  | nil =>
    obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq run
    cases same
    intro blob member
    exact Or.inl member
  | cons source rest ih =>
    unfold checkBlobs at run
    split at run
    · exact False.elim (error_cannot_return _ _ _ run)
    · split at run
      · exact False.elim (error_cannot_return _ _ _ run)
      · split at run
        · exact False.elim (error_cannot_return _ _ _ run)
        · obtain ⟨hashEvents, result, last, hashing, tail, eventShape⟩ :=
            Snapshot.returns_bind_split (Filesystem.hash source.content) _ run
          cases result with
          | error error => exact False.elim (error_cannot_return _ _ _ tail)
          | ok digest =>
            dsimp only at tail
            split at tail
            · rename_i checked
              split at tail
              · exact False.elim (error_cannot_return _ _ _ tail)
              · let checkedBlob : CheckedBlob := ⟨source, digest, checked.1, checked.2⟩
                have restProvenance := ih (before.insert checkedBlob) after last tail
                intro blob member
                rcases restProvenance blob member with previous | later
                · change blob ∈ (before.values.push checkedBlob).toList at previous
                  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at previous
                  rcases previous with old | same
                  · exact Or.inl old
                  · subst blob
                    refine Or.inr ⟨source, by simp, rfl, ?_⟩
                    rw [eventShape]
                    exact hashSeen_append_left _ _ _ _ (hash_returned _ _ _ hashing)
                · rcases later with ⟨actual, member, equal, seen⟩
                  refine Or.inr ⟨actual, by simp [member], equal, ?_⟩
                  rw [eventShape]
                  exact hashSeen_append_right _ _ _ _ seen
            · exact False.elim (error_cannot_return _ _ _ tail)

theorem checkBlobs_index_sound (limits : Transport.Limits) (sources : List Transport.Blob)
    (before after : BlobState) (events : List (Request × Reply)) (sound : before.IndexSound)
    (run : Returns (checkBlobs limits sources before) events (.ok after)) : after.IndexSound := by
  induction sources generalizing before after events with
  | nil =>
    have same := (Snapshot.returns_pure_eq run).2
    cases same
    exact sound
  | cons source rest ih =>
    unfold checkBlobs at run
    split at run
    · exact False.elim (error_cannot_return _ _ _ run)
    · split at run
      · exact False.elim (error_cannot_return _ _ _ run)
      · split at run
        · exact False.elim (error_cannot_return _ _ _ run)
        · obtain ⟨_, result, last, _, tail, _⟩ :=
            Snapshot.returns_bind_split (Filesystem.hash source.content) _ run
          cases result with
          | error error => exact False.elim (error_cannot_return _ _ _ tail)
          | ok digest =>
            dsimp only at tail
            split at tail
            · rename_i checked
              split at tail
              · exact False.elim (error_cannot_return _ _ _ tail)
              · exact ih _ after last (blob_index_insert before sound _) tail
            · exact False.elim (error_cannot_return _ _ _ tail)

def blobStateBytes (blobs : List CheckedBlob) : Nat := (blobs.map (fun blob => blob.bytes.size)).sum

structure BlobBounded (limits : Transport.Limits) (state : BlobState) : Prop where
  count : state.values.size ≤ limits.inodesMax
  bytes : state.total ≤ limits.workspaceMax
  measured : blobStateBytes state.values.toList = state.total
  keys : ∀ blob ∈ state.values.toList, blob.source.digest.size = 64 ∧ blob.key.toUTF8.size = 64

theorem blob_bounded_initial (limits : Transport.Limits) : BlobBounded limits {} := by
  refine ⟨Nat.zero_le _, Nat.zero_le _, rfl, ?_⟩
  simp

theorem blob_bounded_insert (limits : Transport.Limits) (state : BlobState) (blob : CheckedBlob)
    (bounded : BlobBounded limits state) (count : state.values.size < limits.inodesMax)
    (bytes : state.total + blob.bytes.size ≤ limits.workspaceMax) (key : blob.source.digest.size = 64) :
    BlobBounded limits (state.insert blob) := by
  refine ⟨?_, bytes, ?_, ?_⟩
  · change (state.values.push blob).size ≤ limits.inodesMax
    rw [Array.size_push]
    omega
  · change blobStateBytes (state.values.push blob).toList = state.total + blob.bytes.size
    rw [Array.toList_push]
    simp only [blobStateBytes, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    exact congrArg (· + blob.bytes.size) bounded.measured
  · intro value member
    change value ∈ (state.values.push blob).toList at member
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
    rcases member with previous | same
    · exact bounded.keys value previous
    · subst value
      exact ⟨key, (congrArg ByteArray.size blob.encoding).trans key⟩

-- §FS-host-boundary.artifacts: Actual hashed content and its retained lookup metadata stay bounded.
theorem checkBlobs_bounded (limits : Transport.Limits) (sources : List Transport.Blob)
    (before after : BlobState) (events : List (Request × Reply)) (bounded : BlobBounded limits before)
    (run : Returns (checkBlobs limits sources before) events (.ok after)) : BlobBounded limits after := by
  induction sources generalizing before after events with
  | nil =>
    have same := (Snapshot.returns_pure_eq run).2
    cases same
    exact bounded
  | cons source rest ih =>
    unfold checkBlobs at run
    split at run
    · exact False.elim (error_cannot_return _ _ _ run)
    · rename_i count
      split at run
      · exact False.elim (error_cannot_return _ _ _ run)
      · rename_i encoded
        split at run
        · exact False.elim (error_cannot_return _ _ _ run)
        · rename_i total
          obtain ⟨_, result, last, _, tail, _⟩ :=
            Snapshot.returns_bind_split (Filesystem.hash source.content) _ run
          cases result with
          | error error => exact False.elim (error_cannot_return _ _ _ tail)
          | ok digest =>
            dsimp only at tail
            split at tail
            · rename_i checked
              split at tail
              · exact False.elim (error_cannot_return _ _ _ tail)
              · apply ih _ after last (blob_bounded_insert limits before _ bounded ?_ ?_ ?_) tail
                · omega
                · change before.total + source.content.size ≤ limits.workspaceMax
                  omega
                · change source.digest.size = 64
                  have fields : source.digest.size = 64 ∧ Transport.lowerHex source.digest = true := by
                    simpa using encoded
                  exact fields.1
            · exact False.elim (error_cannot_return _ _ _ tail)

-- §FS-host-boundary.artifacts: Every source blob is retained once, in source order, after its hash.
theorem checkBlobs_sequence (limits : Transport.Limits) (sources : List Transport.Blob)
    (before after : BlobState) (events : List (Request × Reply))
    (run : Returns (checkBlobs limits sources before) events (.ok after)) :
    ∃ added, after.values.toList = before.values.toList ++ added ∧
      added.map CheckedBlob.source = sources ∧ ∀ blob ∈ added, HashSeen events blob.bytes blob.digest := by
  induction sources generalizing before after events with
  | nil =>
    have same := (Snapshot.returns_pure_eq run).2
    cases same
    exact ⟨[], by simp, rfl, by simp⟩
  | cons source rest ih =>
    unfold checkBlobs at run
    split at run
    · exact False.elim (error_cannot_return _ _ _ run)
    · split at run
      · exact False.elim (error_cannot_return _ _ _ run)
      · split at run
        · exact False.elim (error_cannot_return _ _ _ run)
        · obtain ⟨hashEvents, result, last, hashing, tail, eventShape⟩ :=
            Snapshot.returns_bind_split (Filesystem.hash source.content) _ run
          cases result with
          | error error => exact False.elim (error_cannot_return _ _ _ tail)
          | ok digest =>
            dsimp only at tail
            split at tail
            · rename_i checked
              split at tail
              · exact False.elim (error_cannot_return _ _ _ tail)
              · let blob : CheckedBlob := ⟨source, digest, checked.1, checked.2⟩
                obtain ⟨added, values, origins, seen⟩ := ih (before.insert blob) after last tail
                refine ⟨blob :: added, ?_, ?_, ?_⟩
                · rw [values]
                  simp only [BlobState.insert, Array.toList_push, List.append_assoc, List.singleton_append]
                · change source :: added.map CheckedBlob.source = source :: rest
                  rw [origins]
                · intro value member
                  simp only [List.mem_cons] at member
                  rcases member with same | old
                  · subst value
                    rw [eventShape]
                    exact hashSeen_append_left _ _ _ _ (hash_returned _ _ _ hashing)
                  · rw [eventShape]
                    exact hashSeen_append_right _ _ _ _ (seen value old)
            · exact False.elim (error_cannot_return _ _ _ tail)

end LeanCage.Host.Artifacts
