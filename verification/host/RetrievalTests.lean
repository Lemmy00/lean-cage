import LeanCageHost.Retrieval

open LeanCage.Host LeanCage.Host.Filesystem

-- §FS-host-boundary.publication: Scripts exercise exact calls without host filesystem effects.
private def check (label : String) (good : Bool) : IO Unit :=
  unless good do throw <| IO.userError ("retrieval check failed: " ++ label)

private def runScript {α : Type} (program : Filesystem.Program α) (script : List (Filesystem.Request × Reply)) : IO α := do
  let pending ← IO.mkRef script
  let result ← program.interpret (fun request => do
    match ← pending.get with
    | [] => throw <| IO.userError "unexpected retrieval effect"
    | (expected, reply) :: rest =>
      unless request = expected do throw <| IO.userError s!"unexpected retrieval primitive {request.op.code}"
      pending.set rest
      return reply)
  check "all effects consumed" (← pending.get).isEmpty
  return result

private def key : ByteArray := ⟨#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]⟩
private def keyDigest : ByteArray := ⟨#[99, 13, 205, 41, 102, 196, 51, 102, 145, 18, 84, 72, 187, 178, 91, 79, 244, 18, 164, 156, 115, 45, 178, 200, 171, 193, 184, 88, 27, 215, 16, 221]⟩
private def signedTag : ByteArray := ⟨#[120, 104, 133, 170, 244, 164, 132, 215, 178, 175, 213, 11, 100, 21, 203, 217, 104, 109, 181, 43, 78, 120, 238, 85, 9, 3, 160, 200, 123, 170, 137, 28]⟩
private def tamperedTag : ByteArray := ⟨#[48, 68, 102, 117, 75, 119, 15, 241, 108, 250, 215, 105, 238, 7, 91, 83, 214, 198, 104, 227, 157, 87, 215, 47, 204, 139, 69, 94, 179, 158, 140, 17]⟩
private def stat : Reply :=
  (0, ([1, 20, 33024, 1, 1000, 1000, 32, 1, 0, 1, 0].map
    (littleEndian 8)).foldl (· ++ ·) .empty)
private def ok : Reply := (0, .empty)
private def bundle : Validation.Bundle := {
  root := "/bundle"
  manifest := .object [("files", .object [(Publication.keyName, .string (Snapshot.hex keyDigest))])]
  identity := String.ofList (List.replicate 64 '0')
  libraryDirectories := [] }

private def keyPrefix : List (Filesystem.Request × Reply) :=
  [({op := .euid}, (1000, .empty)),
   ({op := .openAt, first := cwd, second := readFlags,
     left := (bundle.root ++ "/" ++ Publication.keyName).toUTF8}, (9, .empty)),
   ({op := .getAttribute, first := 9, second := 1, left := PrivateNames.attributeName},
     (1, PrivateNames.attributeValue))]

private def keyCopy : List (Filesystem.Request × Reply) :=
  [({op := .stat, first := 9}, stat), ({op := .read, first := 9, second := 33, third := 1}, (32, key)),
   ({op := .read, first := 9, second := 1, third := 33}, ok), ({op := .stat, first := 9}, stat),
   ({op := .close, first := 9}, ok), ({op := .sha256, left := key}, (0, keyDigest))]

private def authentication (wire tag supplied : ByteArray) (equal : Bool) :
    List (Filesystem.Request × Reply) :=
  keyPrefix ++ keyCopy ++
    [({op := .authenticate, left := wire, right := key}, (0, tag)),
     ({op := .equalSecret, left := Publication.marker tag, right := supplied},
       (if equal then 1 else 0, .empty))]

private def isOk {α : Type} (result : Result α) : Bool :=
  match result with | .ok _ => true | .error _ => false

private def information (inode : Nat) : Stat := ⟨1, inode, 16832, 2, 1000, 1000, 0, 1, 0, 1, 0⟩
private def parent : Directories.Parent := ⟨⟨3, information 10⟩, "final".toUTF8, 1000⟩
private def target : Directories.Opened := ⟨4, information 20⟩
private def outcome : Outcome := {
  requestId := String.ofList (List.replicate 32 '0')
  bundleId := bundle.identity
  command := "run"
  status := "incomplete"
  report := none
  exitCode := 126
  vmCleanup := "unknown"
  error := some "channel lost"
  output := some "/results/final".toUTF8
  publication := "stored" }
private def metadata : GatewayWire.Value := outcome.metadata .empty .empty
private def envelope (value : GatewayWire.Value) (report : Bool := false) : GatewayWire.Value :=
  .object [("schema", .string "leancage-publication-v1"),
    ("policy_sha256", .string (Snapshot.hex keyDigest)),
    ("device", .integer 1), ("inode", .integer 20),
    ("parent_device", .integer 1), ("parent_inode", .integer 10), ("name", .path "final".toUTF8),
    ("report_present", .boolean report), ("stored_present", .boolean false),
    ("manifest_present", .boolean false), ("stdout_present", .boolean false),
    ("stderr_present", .boolean false), ("terminal", .null), ("public", value)]

private def decode (value : GatewayWire.Value) : Result Retrieval.Envelope :=
  Retrieval.decodeEnvelope (GatewayWire.encodeResponse 0 value) bundle parent target

def main : IO Unit := do
  let marker := Publication.marker signedTag
  check "useful authenticated bytes" (isOk (← runScript
    (Publication.verify bundle "signed".toUTF8 marker)
    (authentication "signed".toUTF8 signedTag marker true)))
  check "tampered message fails actual MAC comparison" (!(isOk (← runScript
    (Publication.verify bundle "tampered".toUTF8 marker)
    (authentication "tampered".toUTF8 tamperedTag marker false))))
  check "unmarked key fails before read/hash" (!(isOk (← runScript
    (Publication.verify bundle "signed".toUTF8 marker)
    (keyPrefix.take 2 ++
      [({op := .getAttribute, first := 9, second := 1, left := PrivateNames.attributeName}, (0 - 61, .empty)),
       ({op := .close, first := 9}, ok)]))))
  check "wrong marker width fails before all effects" (!(isOk (← runScript
    (Publication.verify bundle "signed".toUTF8 .empty) [])))
  check "useful typed envelope" (isOk (decode (envelope metadata)))
  check "copied envelope cannot name another inode" (!(isOk (Retrieval.decodeEnvelope
    (GatewayWire.encodeResponse 0 (envelope metadata)) bundle parent ⟨4, information 21⟩)))
  check "copied envelope cannot name another parent" (!(isOk (Retrieval.decodeEnvelope
    (GatewayWire.encodeResponse 0 (envelope metadata)) bundle { parent with directory := ⟨3, information 11⟩ } target)))
  check "copied envelope cannot name another final entry" (!(isOk (Retrieval.decodeEnvelope
    (GatewayWire.encodeResponse 0 (envelope metadata)) bundle { parent with name := "other".toUTF8 } target)))
  let wrongBundle := { outcome with bundleId := "other" }
  check "stored bundle differs" (!(isOk (decode (envelope (wrongBundle.metadata .empty .empty)))))
  let wrongStatus := { outcome with status := "complete" }
  check "complete without report/terminal rejects" (!(isOk (decode (envelope (wrongStatus.metadata .empty .empty)))))
  let .ok decoded := decode (envelope metadata) | throw <| IO.userError "useful envelope failed"
  check "incomplete typed metadata is rederived" (isOk (Retrieval.incompleteMetadata decoded none))
  let raw := "{\"schema\":\"leancage-result-v1\",\"run_id\":1,\"entry\":\"yes\",\"cleanup\":\"unknown\",\"extra\":1e999}".toUTF8
  let some known := Artifacts.knownReport false raw | throw <| IO.userError "known report fixture failed"
  let withReport := { outcome with report := some known }
  let .ok decoded := decode (envelope (withReport.metadata .empty .empty) true)
    | throw <| IO.userError "known report envelope failed"
  check "recognized report survives loss with original numeric tokens" (isOk (Retrieval.incompleteMetadata decoded (some raw)))
  check "recognized report cannot be erased" (!(isOk (Retrieval.incompleteMetadata decoded none)))
  let relative : GatewayWire.Request := ⟨GatewayWire.reportCommand, 0,
    (Array.replicate 8 {}).set! GatewayWire.lookupSlot ⟨GatewayWire.pathKind, "relative/report".toUTF8⟩⟩
  match ← runScript (Retrieval.destination relative bundle) [] with
  | .error error => throw <| IO.userError error.message
  | .ok selected =>
    check "relative report lookup remains raw until retained CWD selection"
      (selected.1 == "relative/report".toUTF8 && selected.2.isNone)
  IO.println "Retrieval checks passed: actual MAC/key calls, tampering, object/name/bundle binding and preserved incomplete reports."
