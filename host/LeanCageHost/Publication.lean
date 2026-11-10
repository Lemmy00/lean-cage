import LeanCageHost.Publication.Files
import LeanCageHost.Publication.Authentication

namespace LeanCage.Host.Publication
open Filesystem

def absolute (path : ByteArray) : Filesystem.Program (Result ByteArray) := do
  if path.isEmpty || !rawPathValid path then return .error "invalid publication destination"
  if path[0]! == 47 then return .ok path
  let current ← Filesystem.Program.effect { op := .workingDirectory }
  if current.1 != 0 || current.2.isEmpty || !rawPathValid current.2 || current.2[0]! != 47 then
    return .error (failure "working directory" current)
  let path := current.2 ++ "/".toUTF8 ++ path
  if !rawPathValid path then return .error "absolute publication path exceeds its bound"
  return .ok path

def destination (request : GatewayWire.Request) (bundle : Validation.Bundle) (id : String) :
    Filesystem.Program (Result ByteArray) :=
  let output := request.field GatewayWire.outputSlot
  if output.kind == GatewayWire.pathKind then pure (.ok output.bytes)
  else
    let results := request.field GatewayWire.resultsSlot
    let path := if results.kind == GatewayWire.pathKind then results.bytes
      else (bundle.root ++ "/.tools/product/runs").toUTF8
    pure (.ok (path ++ "/".toUTF8 ++ id.toUTF8))

def closeOwned (parent : Directories.Parent) (stage : Directories.Fresh) :
    Filesystem.Program Unit := do
  let _ ← Filesystem.Program.effect { op := .close, first := stage.directory.fd }
  let _ ← Filesystem.Program.effect { op := .close, first := stage.container.fd }
  let _ ← Filesystem.Program.effect { op := .close, first := parent.directory.fd }
  pure ()

-- §FS-host-boundary.publication: Any acknowledgement can follow a committed namespace change.
def finishCommit (parent : Directories.Parent) (stage : Directories.Fresh) (outcome : Outcome)
    (renamed : Reply) : Filesystem.Program (Result Outcome) := do
  closeOwned parent stage
  if renamed.1 == 0 && renamed.2.isEmpty then return .ok outcome
  else if nativeError renamed then return .error (failure "atomic publication" renamed)
  else return .error "publication commit acknowledgement is invalid"

-- §FS-host-boundary.publication: Prepare all content and the identity marker before one commit.
def prepare (bundle : Validation.Bundle) (input : Input) (target : ByteArray)
    (stdoutHash stderrHash : ByteArray)
    (parent : Directories.Parent) (stage : Directories.Fresh) :
    Filesystem.Program (Result Outcome) := do
  let candidate := { input.outcome with
    output := some target
    publication := "stored"
    publicationError := none }
  let input := { input with outcome := candidate }
  let policyDigest ← Filesystem.hash input.policy.raw
  let .ok policyDigest := policyDigest | return .error "publication policy hash failed"
  let metadata := candidate.metadata stdoutHash stderrHash
  let .ok json := WireJson.render GatewayWire.valueDepthMax metadata
    | return .error "publication JSON projection failed"
  let wire := GatewayWire.encodeResponse 0 (envelope input metadata policyDigest parent stage)
  if json.size > metadataMax || wire.size > metadataMax then
    return .error "publication envelope exceeds its bound"
  let digest ← authenticate bundle wire
  let .ok digest := digest | return .error "publication envelope authentication failed"
  let filled ← fill parent.uid stage.directory.fd input (json ++ "\n".toUTF8) wire
  if let .error error := filled then return .error error
  let marked ← Filesystem.Program.effect {
    op := .setAttribute
    first := stage.directory.fd
    left := attributeName
    right := marker digest }
  if marked.1 != 0 || !marked.2.isEmpty then return .error (failure "publication marker" marked)
  return .ok candidate

def attempt (bundle : Validation.Bundle) (input : Input) (target : ByteArray)
    (stdoutHash stderrHash : ByteArray) :
    Filesystem.Program (Result Outcome) := do
  let display ← absolute target
  let .ok display := display | return .error "publication display path is unavailable"
  let parent ← Directories.parent target true
  match parent with
  | .error error => return .error error
  | .ok parent =>
    let fresh ← Directories.fresh parent
    match fresh with
    | .error error => closeResult parent.directory.fd (.error error)
    | .ok stage =>
      let prepared ← prepare bundle input display stdoutHash stderrHash parent stage
      match prepared with
      | .error error =>
        cleanup parent stage input
        closeResult parent.directory.fd (.error error)
      | .ok outcome =>
        let renamed ← Filesystem.Program.effect {
          op := .renameNew
          first := stage.container.fd
          second := parent.directory.fd
          left := stage.name
          right := parent.name }
        finishCommit parent stage outcome renamed

def invalidate (input : Input) (error : String) : Input :=
  { input with
    received := none
    validated := none
    outcome := { input.outcome with
      status := "incomplete"
      exitCode := 126
      error := input.outcome.error.or (some error)
      stdout := .empty
      stderr := .empty
      files := [] } }

-- §FS-host-boundary.publication: Every storage error preserves the same recognized inner report.
def publish (request : GatewayWire.Request) (bundle : Validation.Bundle) (input : Input) :
    Filesystem.Program Output := do
  let identified ← input.outcome.identify
  let (input, stdoutHash, stderrHash) := match identified with
    | .ok (stdout, stderr) => (input, stdout, stderr)
    | .error error => (invalidate input error.message, ByteArray.empty, ByteArray.empty)
  let target ← destination request bundle input.outcome.requestId
  let published ← match target with
    | .error error => pure (.error error)
    | .ok target => attempt bundle input target stdoutHash stderrHash
  let outcome := match published with
    | .ok outcome => outcome
    | .error error => input.outcome.storageFailure error.message
  return ⟨outcome, outcome.metadata stdoutHash stderrHash⟩

end LeanCage.Host.Publication
