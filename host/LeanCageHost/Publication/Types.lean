import LeanCageHost.Outcome
import LeanCageHost.Directories
import LeanCageHost.Policy
import LeanCageHost.WireJson

namespace LeanCage.Host.Publication

def metadataMax : Nat := 64 * 1024 * 1024
def attributeName : ByteArray := "user.leancage.publication".toUTF8
def markerMagic : ByteArray := "LCPUB1\x00\x00".toUTF8

structure Input where
  outcome : Outcome
  policy : Policy.Accepted
  boot : ByteArray
  rawReport : Option ByteArray
  received : Option Transport.Result
  validated : Option Artifacts.Validated

structure Output where
  outcome : Outcome
  metadata : GatewayWire.Value

def natural (value : Nat) : GatewayWire.Value := .integer (Int.ofNat value)

def terminal (received : Option Transport.Result) : GatewayWire.Value :=
  match received with
  | none => .null
  | some received => .object [
    ("controller", natural received.terminal.controller),
    ("retrieved", natural received.terminal.retrieved),
    ("error", natural received.terminal.error), ("extinct", natural received.terminal.extinct)]

-- §FS-host-boundary.publication: Bind content, objects and the final name.
def envelope (input : Input) (metadata : GatewayWire.Value) (policyDigest : ByteArray)
    (parent : Directories.Parent) (stage : Directories.Fresh) : GatewayWire.Value :=
  .object [
    ("schema", .string "leancage-publication-v1"),
    ("policy_sha256", .string (Snapshot.hex policyDigest)),
    ("device", natural stage.directory.information.device),
    ("inode", natural stage.directory.information.inode),
    ("parent_device", natural parent.directory.information.device),
    ("parent_inode", natural parent.directory.information.inode), ("name", .path parent.name),
    ("report_present", .boolean input.rawReport.isSome),
    ("stored_present", .boolean (input.validated.bind (·.stored)).isSome),
    ("manifest_present", .boolean (input.validated.bind (·.manifest)).isSome),
    ("stdout_present", .boolean (input.received.bind (·.stdout)).isSome),
    ("stderr_present", .boolean (input.received.bind (·.stderr)).isSome),
    ("terminal", terminal input.received), ("public", metadata)]

def marker (digest : ByteArray) : ByteArray := markerMagic ++ digest

end LeanCage.Host.Publication
