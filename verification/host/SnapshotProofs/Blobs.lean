import SnapshotProofs.Freeze

namespace LeanCage.Host.Snapshot

open Filesystem

-- §FS-host-boundary.snapshot: Reject digest collisions without assuming hash injectivity.
theorem addBlob_provenance (before : List Blob) (digest bytes : ByteArray) {after : List Blob}
    (accepted : addBlob before digest bytes = .ok after) :
    (∀ blob ∈ after, blob ∈ before ∨ (blob.digest = digest ∧ blob.bytes = bytes)) ∧
      ∃ blob ∈ after, blob.digest = digest ∧ blob.bytes = bytes := by
  unfold addBlob at accepted
  split at accepted
  · cases accepted
    constructor
    · intro blob present
      simp only [List.mem_cons] at present
      rcases present with rfl | old
      · exact .inr ⟨rfl, rfl⟩
      · exact .inl old
    · exact ⟨⟨digest, bytes⟩, by simp, rfl, rfl⟩
  · rename_i prior found
    split at accepted
    · rename_i sameBytes
      cases accepted
      refine ⟨by intro blob member; exact .inl member, prior, List.mem_of_find?_eq_some found, ?_, ?_⟩
      · exact eq_of_beq (List.find?_some (p := fun blob : Blob => blob.digest == digest)
          (a := prior) (l := before) found)
      · exact eq_of_beq sameBytes
    · cases accepted

theorem addBlob_keeps (before : List Blob) (digest bytes : ByteArray) {after : List Blob}
    (accepted : addBlob before digest bytes = .ok after) : ∀ blob ∈ before, blob ∈ after := by
  unfold addBlob at accepted
  split at accepted
  · cases accepted
    intro blob present
    exact .tail _ present
  · split at accepted
    · cases accepted
      exact fun _ present => present
    · cases accepted

theorem addBlob_unique (before : List Blob) (digest bytes : ByteArray) {after : List Blob}
    (unique : (before.map Blob.digest).Nodup)
    (accepted : addBlob before digest bytes = .ok after) : (after.map Blob.digest).Nodup := by
  unfold addBlob at accepted
  split at accepted
  · rename_i missing
    cases accepted
    apply List.nodup_cons.mpr
    refine ⟨?_, unique⟩
    intro member
    obtain ⟨blob, present, equal⟩ := List.mem_map.mp member
    have absent := List.find?_eq_none.mp missing blob present
    exact absent (beq_iff_eq.mpr equal)
  · split at accepted
    · cases accepted
      exact unique
    · cases accepted

def BlobHashed (events : List (Request × Reply)) (blob : Blob) : Prop :=
  ({ op := .sha256, left := blob.bytes }, (0, blob.digest)) ∈ events ∧ blob.digest.size = 32

def BlobEvidence (before : List Blob) (events : List (Request × Reply)) (after : List Blob) : Prop :=
  ∀ blob ∈ after, blob ∈ before ∨ BlobHashed events blob

theorem blobEvidence_refl (blobs : List Blob) : BlobEvidence blobs [] blobs :=
  fun _ member => .inl member

theorem blobEvidence_append {before middle after : List Blob} {first last : List (Request × Reply)}
    (initial : BlobEvidence before first middle) (final : BlobEvidence middle last after) :
    BlobEvidence before (first ++ last) after := by
  intro blob present
  rcases final blob present with old | ⟨hashed, size⟩
  · rcases initial blob old with earlier | ⟨hashed, size⟩
    · exact .inl earlier
    · exact .inr ⟨List.mem_append.mpr (.inl hashed), size⟩
  · exact .inr ⟨List.mem_append.mpr (.inr hashed), size⟩

theorem blobEvidence_monotone {before after : List Blob} {first all : List (Request × Reply)}
    (verified : BlobEvidence before first after) (subset : ∀ event ∈ first, event ∈ all) :
    BlobEvidence before all after := by
  intro blob present
  rcases verified blob present with old | ⟨hashed, size⟩
  · exact .inl old
  · exact .inr ⟨subset _ hashed, size⟩

theorem hash_addBlob (before : List Blob) (bytes : ByteArray)
    {events : List (Request × Reply)} {digest : ByteArray} {after : List Blob}
    (hashed : Returns (Filesystem.hash bytes) events (.ok digest))
    (added : addBlob before digest bytes = .ok after) : BlobEvidence before events after := by
  obtain ⟨reply, shape, zero, exactBytes, size⟩ := hash_provenance _ hashed
  have exactReply : reply = (0, digest) := Prod.ext zero exactBytes
  intro blob present
  rcases (addBlob_provenance _ _ _ added).1 blob present with old | ⟨digestEqual, bytesEqual⟩
  · exact .inl old
  · exact .inr ⟨by simp [shape, exactReply, bytesEqual, digestEqual], by simpa only [digestEqual] using size⟩

end LeanCage.Host.Snapshot
