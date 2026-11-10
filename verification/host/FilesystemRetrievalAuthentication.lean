import FilesystemLoweredCryptography
import RetrievalProofs.Justification

namespace LeanCage.Host.Kernel.Lowered
open Filesystem

private theorem recorded_chunks_middle {kernel : Contract} {origin : FilesystemOrigin} {ordinal : Nat}
    {before after : World} {raw first middle last : List (Request × Reply)}
    (chunks : PrimitiveFilesystem.Chunks
      ((first ++ middle ++ last).map Program.filesystemEvent) (raw.map Program.filesystemEvent))
    (history : RecordedHistory kernel origin ordinal before raw after) :
    ∃ leading selected trailing initial final,
      raw = leading ++ selected ++ trailing ∧
      PrimitiveFilesystem.Chunks (middle.map Program.filesystemEvent) (selected.map Program.filesystemEvent) ∧
      RecordedHistory kernel origin (ordinal + leading.length) initial selected final := by
  have arranged := chunks
  rw [List.map_append, List.map_append, List.append_assoc] at arranged
  obtain ⟨rawLeading, rawRest, leadingChunks, restChunks, leadingTrace⟩ := PrimitiveFilesystem.chunks_split _ _ arranged
  obtain ⟨rawSelected, rawTrailing, selectedChunks, trailingChunks, selectedTrace⟩ :=
    PrimitiveFilesystem.chunks_split _ _ restChunks
  obtain ⟨leading, firstTrace⟩ := PrimitiveFilesystem.chunks_filesystem_raw first leadingChunks
  obtain ⟨selected, middleTrace⟩ := PrimitiveFilesystem.chunks_filesystem_raw middle selectedChunks
  obtain ⟨trailing, lastTrace⟩ := PrimitiveFilesystem.chunks_filesystem_raw last trailingChunks
  have rawTrace : raw = leading ++ selected ++ trailing := by
    apply PrimitiveFilesystem.filesystem_events_injective
    simpa only [selectedTrace, firstTrace, middleTrace, lastTrace, List.map_append, List.append_assoc] using leadingTrace
  have recorded := history
  rw [rawTrace, List.append_assoc] at recorded
  obtain ⟨initial, preceding, remaining⟩ := recorded_history_split leading _ recorded
  obtain ⟨final, selectedHistory, following⟩ := recorded_history_split selected _ remaining
  exact ⟨leading, selected, trailing, initial, final, rawTrace, by simpa only [middleTrace] using selectedChunks, selectedHistory⟩

structure ReportAuthentication (kernel : Contract) (origin : FilesystemOrigin) (ordinal : Nat)
    (request : GatewayWire.Request) (bundle : Validation.Bundle) (answer : GatewayWire.Value)
    (hmac : ByteArray → ByteArray → ByteArray) (events : List (Request × Reply)) where
  logical : List (Request × Reply)
  source : Returns (Retrieval.report request bundle) logical (.ok answer)
  chunks : PrimitiveFilesystem.Chunks (logical.map Program.filesystemEvent) (events.map Program.filesystemEvent)
  evidence : Retrieval.ReportEvidence request bundle logical answer
  wire : ByteArray
  supplied : ByteArray
  parent : Directories.Parent
  target : Directories.Opened
  envelope : Retrieval.Envelope
  binding : Retrieval.EnvelopeBinding wire bundle parent target envelope
  leading : List (Request × Reply)
  verification : List (Request × Reply)
  trailing : List (Request × Reply)
  trace : events = leading ++ verification ++ trailing
  before : World
  after : World
  actual : VerificationUse kernel origin (ordinal + leading.length) bundle wire supplied hmac before verification after

-- §FS-host-boundary.publication: The actual returned report, parsed envelope and verifier
-- share this one raw transcript, including every retained-directory lookup guard/probe.
theorem recorded_report_authentication {kernel : Contract} {sha256 : ByteArray → ByteArray}
    {hmac : ByteArray → ByteArray → ByteArray} (crypto : CryptographicContract kernel sha256 hmac)
    {origin : FilesystemOrigin} {ordinal : Nat} {request : GatewayWire.Request} {bundle : Validation.Bundle}
    {answer : GatewayWire.Value} {before after : World} {events : List (Request × Reply)}
    (actual : RecordedRun kernel origin ordinal (Retrieval.report request bundle).lower before events after (.ok answer)) :
    Nonempty (ReportAuthentication kernel origin ordinal request bundle answer hmac events) := by
  obtain ⟨logical, source, chunks⟩ := PrimitiveFilesystem.lowered_filesystem_returns_chunks _ actual.1
  have evidence := Retrieval.report_justified _ _ source
  obtain ⟨valid, command, path, identity, selection, selected, reportTrace, selectedRun,
    parent, target, ancestors, opening, content, targetClose, parentClose, destinationTrace,
    parentRun, targetRun, stored, targetClosed, parentClosed⟩ := Retrieval.report_source _ _ source
  obtain ⟨wire, supplied, envelope, policy, raw, wireEvents, markerEvents, verification,
    policyEvents, jsonEvents, rawEvents, last, storedTrace, wireRun, markerRun, verified,
    binding, identityMatches, policyRead, jsonRun, rawRead, metadata⟩ := stored
  let first := selection ++ ancestors ++ opening ++ wireEvents ++ markerEvents
  let following := policyEvents ++ jsonEvents ++ rawEvents ++ last ++ targetClose ++ parentClose
  have logicalTrace : logical = first ++ verification ++ following := by
    simp only [reportTrace, destinationTrace, storedTrace, first, following, List.append_assoc]
  have phaseChunks : PrimitiveFilesystem.Chunks
      ((first ++ verification ++ following).map Program.filesystemEvent) (events.map Program.filesystemEvent) :=
    logicalTrace ▸ chunks
  obtain ⟨leading, verificationRaw, trailing, initial, final, trace, selectedChunks, selectedHistory⟩ :=
    recorded_chunks_middle phaseChunks actual.2
  obtain ⟨use⟩ := verification_observation crypto verified selectedChunks selectedHistory
  exact ⟨⟨logical, source, chunks, evidence, wire, supplied, parent, target, envelope, binding,
    leading, verificationRaw, trailing, trace, initial, final, use⟩⟩

-- §FS-host-boundary.publication: This is the actual report caller's authentication result.
-- The alternative is a candidate forgery for the same observed key and committed-query scope.
theorem report_exposure_or_forgery {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {sha256 : ByteArray → ByteArray} {hmac : ByteArray → ByteArray → ByteArray}
    (crypto : CryptographicContract kernel sha256 hmac) (actor : ActorId) (initial : World)
    (all : List (ActorTick runtime)) (ordinal : Nat) (request : GatewayWire.Request) (bundle : Validation.Bundle)
    {answer : GatewayWire.Value} {before after : World} {events : List (Request × Reply)}
    (actual : RecordedRun kernel (fun index request reply =>
      SourceReturnAt runtime all actor index Reply (.filesystem request) reply) ordinal
      (Retrieval.report request bundle).lower before events after (.ok answer)) :
    ∃ receipt : ReportAuthentication kernel (fun index request reply =>
        SourceReturnAt runtime all actor index Reply (.filesystem request) reply) ordinal
        request bundle answer hmac events,
      ∃ secret position tick reply,
        all[position]? = some tick ∧ tick.action = .returned actor (.filesystem {
          op := .equalSecret, left := Publication.marker (hmac secret receipt.wire), right := receipt.supplied }) reply ∧
        (SourceExposed runtime initial all hmac secret position receipt.wire ∨
          MacForgery hmac secret (SourceExposed runtime initial all hmac secret position)
            receipt.wire (observedTag receipt.supplied)) := by
  obtain ⟨receipt⟩ := recorded_report_authentication crypto actual
  exact ⟨receipt, verification_use_exposure_or_forgery actor initial all receipt.actual⟩

end LeanCage.Host.Kernel.Lowered
