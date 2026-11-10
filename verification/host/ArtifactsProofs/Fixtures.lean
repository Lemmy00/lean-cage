import ArtifactsProofs.Bounds
import TransportProofs.Witnesses

namespace LeanCage.Host.Artifacts.Witness

open Filesystem

set_option cbv.maxSteps 20000000
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def limits : Transport.Limits := ⟨8, 8, 32, 8⟩
def expected : Expected := ⟨false, "offline_workspace", "fixture-runtime", limits⟩
def content : ByteArray := "abc".toUTF8
def contentKey : String := "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
def manifest : ByteArray :=
  ("LCEXPORT1\nD 2e746d70\nF 1 2e746d702f726573756c74 3 " ++ contentKey ++ "\nO 6f6d6974746564\n").toUTF8
def manifestKey : String := "b4e08594ebcc4938858898edc69a4ae29a6cc118416356b5e2b6750c1e739ebc"
def rawDigest (key : String) : ByteArray := (unhexLoop key.toUTF8.data.toList .empty).toOption.getD .empty

def field (key : String) (value : Json.Value) : String × Json.Value := (key, value)
def number (value : Nat) : Json.Value := .number value.repr.toUTF8.data.toList

def reportValue (allocated : Bool) : Json.Value := .object [
  field "schema" (.string "leancage-result-v1"),
  field "profile" (.string expected.profile), field "runtime_manifest_digest" (.string expected.runtimeDigest),
  field "run_id" (number (if allocated then 1 else 0)),
  field "uid" (number (if allocated then 100000 else 0)),
  field "stage" (number (if allocated then 0 else 1)), field "detail" (number (if allocated then 0 else 1)),
  field "entry" (.string (if allocated then "yes" else "no")), field "cleanup" (.string "complete"),
  field "termination" (.string (if allocated then "exited" else "setup_failed")),
  field "cancellation_bits" (number 0),
  field "report_storage" (.string (if allocated then "stored" else "not_applicable")),
  field "report_storage_error" .null, field "export" (.string (if allocated then "complete" else "discarded")),
  field "export_digest" (if allocated then .string manifestKey else .null),
  field "export_errno" (number 0), field "export_omitted" (number (if allocated then 1 else 0)),
  field "stdout_captured_bytes" (if allocated then number 3 else .null),
  field "stderr_captured_bytes" (if allocated then number 0 else .null),
  field "stdout_bytes" (if allocated then number 3 else .null),
  field "stderr_bytes" (if allocated then number 0 else .null),
  field "stdout_truncated" (if allocated then .bool false else .null),
  field "stderr_truncated" (if allocated then .bool false else .null),
  field "extra_number" (.number "-1.25e+2".toUTF8.data.toList)]

def report (allocated : Bool) : ByteArray :=
  if allocated then
    "{\"schema\":\"leancage-result-v1\",\"profile\":\"offline_workspace\",\"runtime_manifest_digest\":\"fixture-runtime\",\"run_id\":1,\"uid\":100000,\"stage\":0,\"detail\":0,\"entry\":\"yes\",\"cleanup\":\"complete\",\"termination\":\"exited\",\"cancellation_bits\":0,\"report_storage\":\"stored\",\"report_storage_error\":null,\"export\":\"complete\",\"export_digest\":\"b4e08594ebcc4938858898edc69a4ae29a6cc118416356b5e2b6750c1e739ebc\",\"export_errno\":0,\"export_omitted\":1,\"stdout_captured_bytes\":3,\"stderr_captured_bytes\":0,\"stdout_bytes\":3,\"stderr_bytes\":0,\"stdout_truncated\":false,\"stderr_truncated\":false,\"extra_number\":-1.25e+2}".toUTF8
  else
    "{\"schema\":\"leancage-result-v1\",\"profile\":\"offline_workspace\",\"runtime_manifest_digest\":\"fixture-runtime\",\"run_id\":0,\"uid\":0,\"stage\":1,\"detail\":1,\"entry\":\"no\",\"cleanup\":\"complete\",\"termination\":\"setup_failed\",\"cancellation_bits\":0,\"report_storage\":\"not_applicable\",\"report_storage_error\":null,\"export\":\"discarded\",\"export_digest\":null,\"export_errno\":0,\"export_omitted\":0,\"stdout_captured_bytes\":null,\"stderr_captured_bytes\":null,\"stdout_bytes\":null,\"stderr_bytes\":null,\"stdout_truncated\":null,\"stderr_truncated\":null,\"extra_number\":-1.25e+2}".toUTF8
def terminal (allocated : Bool) : Transport.Terminal := ⟨7, if allocated then 0 else 126, 0, 1⟩
def frames : List Transport.Frame := [Transport.Witness.frame .report (report true),
  Transport.Witness.frame .stored (report true), Transport.Witness.frame .stdout "ok\n".toUTF8,
  Transport.Witness.frame .stderr .empty, Transport.Witness.frame .export manifest,
  Transport.Witness.frame .blob (contentKey.toUTF8 ++ content),
  Transport.Witness.frame .terminal (Transport.Witness.terminalBytes 7 0 0 1)]

def received : Transport.Result := {
  report := report true, stored := some (report true), stdout := some "ok\n".toUTF8,
  stderr := some .empty, manifest := some manifest, blobs := [⟨contentKey.toUTF8, content⟩],
  terminal := terminal true, frames }

def runZero : Transport.Result := {
  report := report false, stored := none, stdout := none, stderr := none, manifest := none,
  blobs := [], terminal := terminal false, frames := [] }

-- §FS-host-boundary.acceptance: A finite reply interpreter constructs actual program executions.
def replay {α : Type} : List Reply → Program α → Option α
  | _, .pure value => some value
  | [], .call _ _ => none
  | reply :: rest, .call _ next => replay rest (next reply)

theorem replay_returns {α : Type} (replies : List Reply) (program : Program α) (answer : α)
    (finished : replay replies program = some answer) : ∃ events, Returns program events answer := by
  induction replies generalizing program with
  | nil =>
    cases program with
    | pure value => cases finished; exact ⟨[], .pure answer⟩
    | call => contradiction
  | cons reply rest ih =>
    cases program with
    | pure value => cases finished; exact ⟨[], .pure answer⟩
    | call request next =>
      obtain ⟨events, run⟩ := ih (next reply) finished
      exact ⟨(request, reply) :: events, .call request next reply events answer run⟩

def success {α : Type} : Option (Filesystem.Result α) → Bool
  | some (.ok _) => true
  | _ => false

def failure {α : Type} : Option (Filesystem.Result α) → Bool
  | some (.error _) => true
  | _ => false

def hashReplies : List Reply := [(0, rawDigest manifestKey), (0, rawDigest contentKey)]

def initial : Transport.State := {
  limits, expectedPrefix := Transport.identityPrefix Transport.Witness.request Transport.Witness.bundle,
  phase := .prefix 0 }
def wire : ByteArray := Transport.identityPrefix Transport.Witness.request Transport.Witness.bundle ++
  ⟨(Transport.frameWire frames).toArray⟩


end LeanCage.Host.Artifacts.Witness
