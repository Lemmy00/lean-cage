import FilesystemCryptography
import FilesystemLoweredPhases
import SnapshotProofs.Hex

namespace LeanCage.Host.Kernel.Lowered
open Filesystem

structure KeyDigestUse (kernel : Contract) (origin : FilesystemOrigin) (ordinal : Nat)
    (bundle : Validation.Bundle) (key : ByteArray) (sha256 : ByteArray → ByteArray)
    (before : World) (events : List (Request × Reply)) (after : World) where
  files : List (String × Json.Value)
  name : String
  expected : String
  inventory : Validation.bundleFiles bundle.manifest = some files
  identified : files.find? (fun field => field.1 == Publication.keyName) = some (name, .string expected)
  keySize : key.size = 32
  leadingEvents : List (Request × Reply)
  reply : Reply
  actualBefore : World
  actualAfter : World
  leading : RecordedHistory kernel origin ordinal before leadingEvents actualBefore
  actual : kernel.step actualBefore {op := .sha256, left := key} (some reply) actualAfter
  sampled : origin (ordinal + leadingEvents.length) {op := .sha256, left := key} reply actualBefore actualAfter
  trailing : RecordedHistory kernel origin (ordinal + leadingEvents.length + 1) actualAfter [] after
  trace : events = leadingEvents ++ [({op := .sha256, left := key}, reply)]
  zero : reply.1 = 0
  size : reply.2.size = 32
  interpreted : reply.2 = sha256 key
  inventoryDigest : Snapshot.hex reply.2 = expected

-- §FS-host-boundary.publication: The digest uses the actual copied key bytes and
-- exact last raw hashing call of this same expanded key-loader transcript.
theorem key_digest_observation {kernel : Contract} {sha256 : ByteArray → ByteArray}
    {hmac : ByteArray → ByteArray → ByteArray} (crypto : CryptographicContract kernel sha256 hmac)
    {origin : FilesystemOrigin} {ordinal : Nat} {bundle : Validation.Bundle} {key : ByteArray}
    {logical raw : List (Request × Reply)} {before after : World}
    (source : Retrieval.KeyObservation bundle logical key)
    (chunks : PrimitiveFilesystem.Chunks (logical.map Program.filesystemEvent) (raw.map Program.filesystemEvent))
    (history : RecordedHistory kernel origin ordinal before raw after) :
    Nonempty (KeyDigestUse kernel origin ordinal bundle key sha256 before raw after) := by
  obtain ⟨files, name, expected, uid, opened, fd, privateReply, copies, closing, hashes,
    copied, digest, inventory, identified, logicalTrace, _, _, _, _, _, _, _, _,
    keySize, _, _, hashed, digestIdentity⟩ := source
  obtain ⟨reply, hashTrace, zero, digestBytes, digestSize⟩ := Snapshot.hash_provenance key hashed
  let front : List (Request × Reply) := [({op := .euid}, uid), ({
      op := .openAt, first := cwd, second := readFlags,
      left := (bundle.root ++ "/" ++ Publication.keyName).toUTF8}, opened),
      ({op := .getAttribute, first := fd, second := 1, left := PrivateNames.attributeName}, privateReply)] ++
    copies ++ closing
  have selectedHash : logical.map Program.filesystemEvent = front.map Program.filesystemEvent ++
      .returned (.filesystem {op := .sha256, left := key}) reply :: [] := by
    simp only [logicalTrace, hashTrace, front, List.map_append, List.map_cons, List.map_nil,
      Program.filesystemEvent, List.append_assoc]
  obtain ⟨first, last, leadingChunks, trailingChunks, rawTrace⟩ :=
    PrimitiveFilesystem.chunks_selected_identity chunks selectedHash rfl
  have lastEmpty : last = [] := by cases trailingChunks; rfl
  obtain ⟨leadingEvents, firstTrace⟩ := PrimitiveFilesystem.chunks_filesystem_raw front leadingChunks
  have actualTrace : raw = leadingEvents ++ [({op := .sha256, left := key}, reply)] := by
    apply PrimitiveFilesystem.filesystem_events_injective
    simpa only [firstTrace, lastEmpty, List.map_append, List.map_cons, List.map_nil,
      List.append_nil, Program.filesystemEvent] using rawTrace
  have recorded := history
  rw [actualTrace] at recorded
  obtain ⟨middle, leading, rest⟩ := recorded_history_split leadingEvents _ recorded
  obtain ⟨actualBefore, actualAfter, environment, actual, sampled, trailing⟩ := recorded_history_head rest
  refine ⟨{
    files, name, expected, inventory, identified, keySize, leadingEvents, reply,
    actualBefore, actualAfter,
    leading := by simpa only [List.append_nil] using recorded_history_append leading environment
    actual, sampled, trailing, trace := actualTrace, zero,
    size := by simpa only [digestBytes] using digestSize
    interpreted := crypto.hashing _ _ _ _ actual rfl zero (by simpa only [digestBytes] using digestSize)
    inventoryDigest := digestBytes ▸ digestIdentity }⟩

end LeanCage.Host.Kernel.Lowered
