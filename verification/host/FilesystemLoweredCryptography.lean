import FilesystemCommittedAuthentication
import FilesystemLoweredPhases
import FilesystemAuthenticity

namespace LeanCage.Host.Kernel.Lowered
open Filesystem

structure AuthenticationUse (kernel : Contract) (origin : FilesystemOrigin) (ordinal : Nat)
    (bundle : Validation.Bundle) (wire tag : ByteArray) (hmac : ByteArray → ByteArray → ByteArray)
    (before : World) (events : List (Request × Reply)) (after : World) where
  key : ByteArray
  keyLogical : List (Request × Reply)
  keyRaw : List (Request × Reply)
  loaded : Retrieval.KeyObservation bundle keyLogical key
  chunks : PrimitiveFilesystem.Chunks (keyLogical.map Program.filesystemEvent) (keyRaw.map Program.filesystemEvent)
  reply : Reply
  trace : events = keyRaw ++ [({op := .authenticate, left := wire, right := key}, reply)]
  actualBefore : World
  actualAfter : World
  leading : RecordedHistory kernel origin ordinal before keyRaw actualBefore
  actual : kernel.step actualBefore {op := .authenticate, left := wire, right := key} (some reply) actualAfter
  sampled : origin (ordinal + keyRaw.length) {op := .authenticate, left := wire, right := key} reply actualBefore actualAfter
  trailing : RecordedHistory kernel origin (ordinal + keyRaw.length + 1) actualAfter [] after
  zero : reply.1 = 0
  payload : reply.2 = tag
  size : tag.size = 32
  interpreted : tag = hmac key wire

-- §AR-host-boundary.primitives: Preserve actual key-opening probes and source values;
-- only this exact one raw MAC result is interpreted by the cryptographic primitive law.
theorem authentication_observation {kernel : Contract} {sha256 : ByteArray → ByteArray}
    {hmac : ByteArray → ByteArray → ByteArray} (crypto : CryptographicContract kernel sha256 hmac)
    {origin : FilesystemOrigin} {ordinal : Nat} {bundle : Validation.Bundle} {wire tag : ByteArray}
    {logical raw : List (Request × Reply)} {before after : World}
    (source : Retrieval.AuthenticationObservation bundle wire tag logical)
    (chunks : PrimitiveFilesystem.Chunks (logical.map Program.filesystemEvent) (raw.map Program.filesystemEvent))
    (history : RecordedHistory kernel origin ordinal before raw after) :
    Nonempty (AuthenticationUse kernel origin ordinal bundle wire tag hmac before raw after) := by
  obtain ⟨bound, key, keyEvents, reply, sourceTrace, loaded, zero, payload, size⟩ := source
  have chunks : PrimitiveFilesystem.Chunks (keyEvents.map Program.filesystemEvent ++
      [.returned (.filesystem {op := .authenticate, left := wire, right := key}) reply])
      (raw.map Program.filesystemEvent) := by
    simpa only [sourceTrace, List.map_append, List.map_cons, List.map_nil, Program.filesystemEvent] using chunks
  obtain ⟨rawKey, rawCall, keyChunks, callChunks, rawTrace⟩ := PrimitiveFilesystem.chunks_split _ _ chunks
  have callTrace : rawCall = [.returned (.filesystem {op := .authenticate, left := wire, right := key}) reply] :=
    PrimitiveFilesystem.chunks_identity callChunks (by intro event member; cases List.mem_singleton.mp member; rfl)
  obtain ⟨keyRaw, keyTrace⟩ := PrimitiveFilesystem.chunks_filesystem_raw keyEvents keyChunks
  have actualTrace : raw = keyRaw ++ [({op := .authenticate, left := wire, right := key}, reply)] := by
    apply PrimitiveFilesystem.filesystem_events_injective
    simpa only [keyTrace, callTrace, List.map_append, List.map_cons, List.map_nil, Program.filesystemEvent] using rawTrace
  have recorded := history
  rw [actualTrace] at recorded
  obtain ⟨middle, leading, remaining⟩ := recorded_history_split keyRaw _ recorded
  obtain ⟨actualBefore, actualAfter, interference, actual, sampled, trailing⟩ := recorded_history_head remaining
  have beforeKey := recorded_history_append leading interference
  refine ⟨{
    key
    keyLogical := keyEvents
    keyRaw
    loaded
    chunks := by simpa only [keyTrace] using keyChunks
    reply
    trace := actualTrace
    actualBefore
    actualAfter
    leading := by simpa only [List.append_nil] using beforeKey
    actual
    sampled
    trailing
    zero
    payload
    size
    interpreted := payload.symm.trans (crypto.authentication _ _ _ _ actual rfl zero
      (by simpa only [payload] using size)) }⟩

theorem recorded_authentication {kernel : Contract} {sha256 : ByteArray → ByteArray}
    {hmac : ByteArray → ByteArray → ByteArray} (crypto : CryptographicContract kernel sha256 hmac)
    {origin : FilesystemOrigin} {ordinal : Nat} {bundle : Validation.Bundle} {wire tag : ByteArray}
    {before after : World} {events : List (Request × Reply)}
    (actual : RecordedRun kernel origin ordinal (Publication.authenticate bundle wire).lower before events after (.ok tag)) :
    Nonempty (AuthenticationUse kernel origin ordinal bundle wire tag hmac before events after) := by
  obtain ⟨logical, source, chunks⟩ := PrimitiveFilesystem.lowered_filesystem_returns_chunks _ actual.1
  exact authentication_observation crypto (Retrieval.authenticate_source _ _ source) chunks actual.2

structure VerificationUse (kernel : Contract) (origin : FilesystemOrigin) (ordinal : Nat)
    (bundle : Validation.Bundle) (wire supplied : ByteArray) (hmac : ByteArray → ByteArray → ByteArray)
    (before : World) (events : List (Request × Reply)) (after : World) where
  tag : ByteArray
  authentication : List (Request × Reply)
  authenticationAfter : World
  use : AuthenticationUse kernel origin ordinal bundle wire tag hmac before authentication authenticationAfter
  reply : Reply
  actualBefore : World
  actualAfter : World
  leading : RecordedHistory kernel origin (ordinal + authentication.length) authenticationAfter [] actualBefore
  actual : kernel.step actualBefore {
    op := .equalSecret, left := Publication.marker tag, right := supplied } (some reply) actualAfter
  sampled : origin (ordinal + authentication.length) {
    op := .equalSecret, left := Publication.marker tag, right := supplied } reply actualBefore actualAfter
  trailing : RecordedHistory kernel origin (ordinal + authentication.length + 1) actualAfter [] after
  trace : events = authentication ++ [({op := .equalSecret, left := Publication.marker tag, right := supplied}, reply)]
  accepted : reply.1 = 1 ∧ reply.2 = .empty
  matching : supplied = Publication.marker (hmac use.key wire)

-- §FS-host-boundary.publication: The real lowered verifier supplies the actual key/MAC
-- and constant-time comparison. Guard probes are retained in its same raw transcript.
theorem verification_observation {kernel : Contract} {sha256 : ByteArray → ByteArray}
    {hmac : ByteArray → ByteArray → ByteArray} (crypto : CryptographicContract kernel sha256 hmac)
    {origin : FilesystemOrigin} {ordinal : Nat} {bundle : Validation.Bundle} {wire supplied : ByteArray}
    {before after : World} {logical events : List (Request × Reply)}
    (source : Retrieval.VerificationObservation bundle wire supplied logical)
    (chunks : PrimitiveFilesystem.Chunks (logical.map Program.filesystemEvent) (events.map Program.filesystemEvent))
    (recorded : RecordedHistory kernel origin ordinal before events after) :
    Nonempty (VerificationUse kernel origin ordinal bundle wire supplied hmac before events after) := by
  obtain ⟨size, tag, authentication, reply, sourceTrace, authenticated, one, empty⟩ := source
  have chunks : PrimitiveFilesystem.Chunks (authentication.map Program.filesystemEvent ++
      [.returned (.filesystem {op := .equalSecret, left := Publication.marker tag, right := supplied}) reply])
      (events.map Program.filesystemEvent) := by
    simpa only [sourceTrace, List.map_append, List.map_cons, List.map_nil, Program.filesystemEvent] using chunks
  obtain ⟨rawAuthentication, rawComparison, authenticationChunks, comparisonChunks, rawTrace⟩ :=
    PrimitiveFilesystem.chunks_split _ _ chunks
  have comparisonTrace : rawComparison =
      [.returned (.filesystem {op := .equalSecret, left := Publication.marker tag, right := supplied}) reply] :=
    PrimitiveFilesystem.chunks_identity comparisonChunks (by intro event member; cases List.mem_singleton.mp member; rfl)
  obtain ⟨authenticationRaw, authenticationTrace⟩ := PrimitiveFilesystem.chunks_filesystem_raw authentication authenticationChunks
  have actualTrace : events = authenticationRaw ++ [({
      op := .equalSecret, left := Publication.marker tag, right := supplied }, reply)] := by
    apply PrimitiveFilesystem.filesystem_events_injective
    simpa only [authenticationTrace, comparisonTrace, List.map_append, List.map_cons, List.map_nil,
      Program.filesystemEvent] using rawTrace
  have history := recorded
  rw [actualTrace] at history
  obtain ⟨middle, leading, remaining⟩ := recorded_history_split authenticationRaw _ history
  obtain ⟨use⟩ := authentication_observation crypto authenticated
    (by simpa only [authenticationTrace] using authenticationChunks) leading
  obtain ⟨actualBefore, actualAfter, interference, operation, sampled, trailing⟩ := recorded_history_head remaining
  have matched := crypto.comparison _ _ _ _ operation rfl one empty
  exact ⟨⟨tag, authenticationRaw, middle, use, reply, actualBefore, actualAfter, interference,
    operation, sampled, trailing, actualTrace, ⟨one, empty⟩,
    matched.symm.trans (congrArg Publication.marker use.interpreted)⟩⟩

theorem recorded_verification {kernel : Contract} {sha256 : ByteArray → ByteArray}
    {hmac : ByteArray → ByteArray → ByteArray} (crypto : CryptographicContract kernel sha256 hmac)
    {origin : FilesystemOrigin} {ordinal : Nat} {bundle : Validation.Bundle} {wire supplied : ByteArray}
    {before after : World} {events : List (Request × Reply)}
    (actual : RecordedRun kernel origin ordinal (Publication.verify bundle wire supplied).lower before events after (.ok ())) :
    Nonempty (VerificationUse kernel origin ordinal bundle wire supplied hmac before events after) := by
  obtain ⟨logical, source, chunks⟩ := PrimitiveFilesystem.lowered_filesystem_returns_chunks _ actual.1
  exact verification_observation crypto (Retrieval.verify_source _ _ _ source) chunks actual.2

theorem verification_use_exposure_or_forgery {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {hmac : ByteArray → ByteArray → ByteArray} (actor : ActorId) (initial : World)
    (all : List (ActorTick runtime)) {ordinal : Nat} {bundle : Validation.Bundle}
    {wire supplied : ByteArray} {before after : World} {events : List (Request × Reply)}
    (use : VerificationUse kernel (fun index request reply =>
      SourceReturnAt runtime all actor index Reply (.filesystem request) reply) ordinal
      bundle wire supplied hmac before events after) :
    ∃ secret position tick reply,
      all[position]? = some tick ∧ tick.action = .returned actor (.filesystem {
        op := .equalSecret, left := Publication.marker (hmac secret wire), right := supplied }) reply ∧
      (SourceExposed runtime initial all hmac secret position wire ∨
        MacForgery hmac secret (SourceExposed runtime initial all hmac secret position) wire (observedTag supplied)) := by
  classical
  obtain ⟨position, tick, input, output, selected, action, present, afterPresent, count, beforeShape, afterShape⟩ := use.sampled
  refine ⟨use.use.key, position, tick, use.reply, selected, ?_, ?_⟩
  · simpa only [use.use.interpreted] using action
  · by_cases exposed : SourceExposed runtime initial all hmac use.use.key position wire
    · exact .inl exposed
    · exact .inr ⟨(congrArg observedTag use.matching).trans (observed_marker_tag _), exposed⟩

-- §FS-host-boundary.publication: The game query set contains only actual earlier committed
-- exposures. A private precommit MAC or internal verification does not justify source origin.
theorem verification_exposure_or_forgery {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {sha256 : ByteArray → ByteArray} {hmac : ByteArray → ByteArray → ByteArray}
    (crypto : CryptographicContract kernel sha256 hmac) (actor : ActorId) (initial : World)
    (all : List (ActorTick runtime)) (ordinal : Nat) (bundle : Validation.Bundle)
    (wire supplied : ByteArray) {before after : World} {events : List (Request × Reply)}
    (actual : RecordedRun kernel (fun index request reply =>
      SourceReturnAt runtime all actor index Reply (.filesystem request) reply) ordinal
      (Publication.verify bundle wire supplied).lower before events after (.ok ())) :
    ∃ secret position tick reply,
      all[position]? = some tick ∧ tick.action = .returned actor (.filesystem {
        op := .equalSecret, left := Publication.marker (hmac secret wire), right := supplied }) reply ∧
      (SourceExposed runtime initial all hmac secret position wire ∨
        MacForgery hmac secret (SourceExposed runtime initial all hmac secret position) wire (observedTag supplied)) := by
  obtain ⟨use⟩ := recorded_verification crypto actual
  exact verification_use_exposure_or_forgery actor initial all use

end LeanCage.Host.Kernel.Lowered
