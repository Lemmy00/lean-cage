import LeanCageHost.Json
import LeanCageHost.Transport
import LeanCageHost.Snapshot

namespace LeanCage.Host.Artifacts

open Filesystem

structure Expected where
  preflight : Bool
  profile : String
  runtimeDigest : String
  limits : Transport.Limits

-- §FS-host-boundary.artifacts: Split components by structural recursion over Unicode scalars.
def componentParts : List Char → List Char → List String
  | [], reversed => [String.ofList reversed.reverse]
  | '/' :: rest, reversed => String.ofList reversed.reverse :: componentParts rest []
  | scalar :: rest, reversed => componentParts rest (scalar :: reversed)

def pathComponents (path : String) : List String := componentParts path.toList []

-- §FS-host-boundary.artifacts: Exports retain supported UTF-8 paths, including root .tmp.
def ValidPath (path : String) : Prop :=
  let components := pathComponents path
  path.toUTF8.size ≤ 4095 ∧ 0 < components.length ∧ components.length ≤ 64 ∧
    ∀ component ∈ components, Snapshot.ValidComponent component

instance (path : String) : Decidable (ValidPath path) := by
  unfold ValidPath
  infer_instance

structure ExportPath where
  text : String
  valid : ValidPath text

def ExportPath.components (path : ExportPath) : List String := pathComponents path.text

def parentNames : String → List String → List String
  | _, [] | _, [_] => []
  | previous, component :: rest =>
    let current := if previous.isEmpty then component else previous ++ "/" ++ component
    current :: parentNames current rest

def ExportPath.parents (path : ExportPath) : List String := parentNames "" path.components

structure Report where
  runId : Nat
  stage : Nat
  detail : Nat
  uid : Nat
  cancellationBits : Nat
  exportErrno : Nat
  exportOmitted : Nat
  entry : String
  cleanup : String
  termination : String
  storage : String
  storageError : Option String
  exportState : String
  exportDigest : Option String
  stdoutCaptured : Option Nat
  stderrCaptured : Option Nat
  stdoutObserved : Option Nat
  stderrObserved : Option Nat
  stdoutTruncated : Option Bool
  stderrTruncated : Option Bool
  deriving DecidableEq, Repr

structure ValidatedFile where
  path : ExportPath
  executable : Bool
  bytes : ByteArray
  digest : ByteArray

structure Validated where
  rawReport : ByteArray
  report : Json.Value
  details : Report
  stored : Option ByteArray
  stdout : ByteArray
  stderr : ByteArray
  files : List ValidatedFile
  dirs : List ExportPath
  omitted : List ExportPath
  manifest : Option ByteArray
  manifestDigest : Option ByteArray

-- §FS-host-boundary.artifacts: The checked digest is the actual hash reply for these raw bytes.
structure CheckedBlob where
  source : Transport.Blob
  digest : ByteArray
  digestSize : digest.size = 32
  encoding : (Snapshot.hex digest).toUTF8 = source.digest

def CheckedBlob.key (blob : CheckedBlob) : String := Snapshot.hex blob.digest

def CheckedBlob.bytes (blob : CheckedBlob) : ByteArray := blob.source.content

end LeanCage.Host.Artifacts
