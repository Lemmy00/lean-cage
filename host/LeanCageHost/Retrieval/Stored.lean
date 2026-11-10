import LeanCageHost.Retrieval.Files

namespace LeanCage.Host.Retrieval

open Filesystem

-- §FS-host-boundary.publication: Authentication uses exactly this copied wire and retained marker.
def readMarker (target : UInt64) : Filesystem.Program (Result ByteArray) := do
  let size := Publication.markerMagic.size + 32
  let reply ← Filesystem.Program.effect {
    op := .getAttribute
    first := target
    second := size.toUInt64
    left := Publication.attributeName }
  if reply.1.toNat != size || reply.2.size != size then
    return .error (failure "publication marker retrieval" reply)
  return .ok reply.2

def storedPolicy (bundle : Validation.Bundle) (target : UInt64) (envelope : Envelope) :
    Checked Policy.Accepted := do
  let raw ← filesystem (readFile target "policy.json".toUTF8 reportMax)
  let digest ← filesystem (Filesystem.hash raw)
  if Snapshot.hex digest != envelope.policyDigest then reject "stored policy identity differs"
  else
    let value ← checked ((Json.parse raw reportMax).mapError (fun (error : String) => (error : Failure)))
    let policy ← checked ((Policy.budgets value raw).mapError (fun (error : String) => (error : Failure)))
    if Validation.stringField policy.value "profile" != Validation.stringField bundle.manifest "profile" ||
        Validation.stringField policy.value "runtime_manifest_digest" !=
          Validation.stringField bundle.manifest "runtime_manifest_digest" then
      reject "stored policy and current bundle profile differ"
    else pure policy

def incompleteMetadata (envelope : Envelope) (raw : Option ByteArray) : Result GatewayWire.Value := do
  if envelope.outcome.exitCode != 126 then Except.error ("incomplete stored exit differs" : Failure)
  let known := raw.bind (Artifacts.knownReport (envelope.outcome.command == "check"))
  let outcome := { envelope.outcome with report := known }
  let metadata := outcome.metadata .empty .empty
  if !sameValue metadata envelope.metadata then
    Except.error ("incomplete stored metadata differs from recognized report" : Failure)
  return metadata

-- §FS-host-boundary.publication: Regenerate public metadata from actually validated records.
def validateMetadata (bundle : Validation.Bundle) (envelope : Envelope) (policy : Policy.Accepted)
    (received : Transport.Result) : Checked GatewayWire.Value := do
  let expected ← checked (expected bundle (envelope.outcome.command == "check") policy.transport)
  let validated ← filesystem (Artifacts.validate expected received)
  if envelope.outcome.exitCode != received.terminal.controller then reject "stored controller exit differs"
  else
    let outcome := {
      envelope.outcome with
      report := some validated.report
      stdout := validated.stdout
      stderr := validated.stderr
      files := validated.files }
    let hashes ← filesystem outcome.identify
    let metadata := outcome.metadata hashes.1 hashes.2
    if !sameValue metadata envelope.metadata then reject "stored artifact metadata differs from copied contents"
    else pure metadata

-- §FS-host-boundary.publication: Reconstructed records authorize artifact validation.
-- Framing provenance comes from the original authenticated publication.
def completeMetadata (uid : Nat) (target : UInt64) (bundle : Validation.Bundle)
    (envelope : Envelope) (policy : Policy.Accepted) (raw : Option ByteArray) :
    Checked GatewayWire.Value := do
  let some report := raw | reject "complete stored report is absent"
  let some terminal := envelope.terminal | reject "complete stored terminal is absent"
  let stored ← filesystem (optionalFile target "stored-report.json".toUTF8 reportMax envelope.storedPresent)
  let stdout ← filesystem (readFile target "stdout".toUTF8 policy.transport.stdoutMax)
  let stderr ← filesystem (readFile target "stderr".toUTF8 policy.transport.stderrMax)
  if (!envelope.stdoutPresent && !stdout.isEmpty) || (!envelope.stderrPresent && !stderr.isEmpty) then
    reject "unreceived stored capture contains bytes"
  else
    let manifest ← filesystem (optionalFile target "export.manifest".toUTF8 manifestMax envelope.manifestPresent)
    let blobs ← filesystem (manifestBlobs uid target policy.transport manifest)
    let received : Transport.Result := {
      report
      stored
      stdout := if envelope.stdoutPresent then some stdout else none
      stderr := if envelope.stderrPresent then some stderr else none
      manifest
      blobs
      terminal
      frames := [] }
    validateMetadata bundle envelope policy received

def readStored (bundle : Validation.Bundle) (parent : Directories.Parent)
    (target : Directories.Opened) (identity : Option String) : Checked GatewayWire.Value := do
  let wire ← filesystem (readFile target.fd "publication.wire".toUTF8 Publication.metadataMax)
  let marker ← filesystem (readMarker target.fd)
  let _ ← filesystem (Publication.verify bundle wire marker)
  let envelope ← checked (decodeEnvelope wire bundle parent target)
  if identity.any (fun identity => identity != envelope.outcome.requestId) then
    reject "stored lookup request identity differs"
  else
    let policy ← storedPolicy bundle target.fd envelope
    let _ ← filesystem (resultJson target.fd envelope.metadata)
    let raw ← filesystem (optionalFile target.fd "vm-report.json".toUTF8 reportMax envelope.reportPresent)
    if envelope.outcome.status == "complete" then
      completeMetadata parent.uid target.fd bundle envelope policy raw
    else checked (incompleteMetadata envelope raw)

end LeanCage.Host.Retrieval
