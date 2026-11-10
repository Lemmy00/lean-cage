import FilesystemKeyDigest
import FilesystemPrimitiveObservations

namespace LeanCage.Host.Kernel
open Filesystem

structure PrimitiveKeyDigestAt {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    (initial : World) (ticks : List (ActorTick runtime)) (tick : ActorTick runtime)
    (actor : ActorId) (engine : EngineState) (bundle : Validation.Bundle) (key : ByteArray)
    (sha256 : ByteArray → ByteArray) where
  source : SelectedActorHistory runtime initial ticks tick actor engine
  rawBefore : List Program.Event
  events : List (Request × Reply)
  rawAfter : List Program.Event
  trace : engine.events = rawBefore ++ events.map Program.filesystemEvent ++ rawAfter
  before : World
  after : World
  digest : Lowered.KeyDigestUse kernel (fun index request reply =>
    SourceReturnAt runtime ticks actor index Reply (.filesystem request) reply) rawBefore.length
    bundle key sha256 before events after

-- §FS-host-boundary.publication: Locate the actual loader's hash before this
-- selected source call. Every preceding probe and each intervening actor row
-- remains in the same source history; the key is not independently sampled.
theorem primitive_key_digest_at {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {sha256 : ByteArray → ByteArray} {hmac : ByteArray → ByteArray → ByteArray}
    (crypto : CryptographicContract kernel sha256 hmac)
    {initial : World} {ticks : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial ticks tick actor engine request observed)
    {bundle : Validation.Bundle} {key : ByteArray} {events : List (Request × Reply)}
    (source : Retrieval.KeyObservation bundle events key) {context following : List Program.Event}
    (trace : adapter.occurrence.logicalBefore = context ++ events.map Program.filesystemEvent ++ following) :
    Nonempty (PrimitiveKeyDigestAt runtime initial ticks tick actor engine bundle key sha256) := by
  have chunks := PrimitiveFilesystem.reached_chunks adapter.occurrence.reached
  rw [trace, List.append_assoc] at chunks
  obtain ⟨first, rest, leadingChunks, remainingChunks, firstTrace⟩ := PrimitiveFilesystem.chunks_split context _ chunks
  obtain ⟨inside, last, phaseChunks, tailChunks, lastTrace⟩ :=
    PrimitiveFilesystem.chunks_split (events.map Program.filesystemEvent) following remainingChunks
  obtain ⟨raw, rawTrace⟩ := PrimitiveFilesystem.chunks_filesystem_raw events phaseChunks
  let final := last ++ adapter.occurrence.inside.map Program.filesystemPrefixEvent
  have full : engine.events = first ++ raw.map Program.filesystemEvent ++ final := by
    rw [adapter.occurrence.trace, firstTrace, lastTrace, rawTrace]
    simp only [final, List.append_assoc]
  have history := adapter.source.history
  rw [full, List.append_assoc] at history
  obtain ⟨before, initialHistory, active⟩ := actor_with_split first _ history
  obtain ⟨after, phase, tail⟩ := actor_with_split (raw.map Program.filesystemEvent) final active
  obtain ⟨digest⟩ := Lowered.key_digest_observation crypto source (by simpa only [rawTrace] using phaseChunks)
    (by simpa only [Nat.zero_add] using actor_recorded_filesystem phase)
  exact ⟨⟨adapter.source, first, raw, final, full, before, after, digest⟩⟩

end LeanCage.Host.Kernel
