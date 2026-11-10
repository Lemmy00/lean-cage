import ArtifactsProofs.Fixtures

open LeanCage.Host LeanCage.Host.Filesystem LeanCage.Host.Artifacts LeanCage.Host.Artifacts.Witness

-- §FS-host-boundary.acceptance: Full framed reports and artifact bytes exercise shared host code.
private def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw <| IO.userError ("artifact check failed: " ++ label)

private def runScript {α : Type} (program : Program α) (script : List (Request × Reply)) : IO α := do
  let pending ← IO.mkRef script
  let result ← program.interpret (fun request => do
    match ← pending.get with
    | [] => throw <| IO.userError "unexpected additional artifact primitive"
    | (expectedRequest, reply) :: rest =>
      unless request = expectedRequest do
        throw <| IO.userError "artifact primitive or actual hash bytes differ"
      pending.set rest
      return reply)
  check "all expected actual hash operations consumed" (← pending.get).isEmpty
  return result

private def manifestHash : Request × Reply := ({op := .sha256, left := manifest}, (0, rawDigest manifestKey))
private def contentHash : Request × Reply := ({op := .sha256, left := content}, (0, rawDigest contentKey))
private def hashes : List (Request × Reply) := [manifestHash, contentHash]

private def rejected {α : Type} : Filesystem.Result α → Bool
  | .error _ => true
  | .ok _ => false

private def accepted {α : Type} : Filesystem.Result α → Bool
  | .ok _ => true
  | .error _ => false

def main : IO Unit := do
  let state ← match Transport.State.init Transport.Witness.request Transport.Witness.bundle limits with
    | .error error => throw <| IO.userError error
    | .ok state => pure state
  let framed ← match (state.run [.data (wire.extract 0 117), .data (wire.extract 117 wire.size), .eof]).finish with
    | .error error => throw <| IO.userError error
    | .ok result => pure result
  check "exact actual REPORT and STORED" (framed.report == report true && framed.stored == some (report true))
  check "same manifest and blob bytes" (framed.manifest == some manifest &&
    framed.blobs.map (·.content) == [content] && framed.blobs.map (·.digest) == [contentKey.toUTF8])
  match ← runScript (validate expected framed) hashes with
  | .error error => throw <| IO.userError error.message
  | .ok output =>
    check "file path and exact content" (output.files.map (fun file => (file.path.text, file.bytes)) == [(".tmp/result", content)])
    check "executable permission retained" (output.files.map (·.executable) == [true])
    check "actual file hash reply" (output.files.map (·.digest) == [rawDigest contentKey])
    check "directory and omitted entry retained" (output.dirs.map (·.text) == [".tmp"] &&
      output.omitted.map (·.text) == ["omitted"])
    check "raw/whole report preserved" (output.rawReport == report true && output.report == reportValue true)
    check "controller independent of reported workload exit" (framed.terminal.controller == 7 && output.details.detail == 0)
    check "committed manifest identity retained" (output.manifest == some manifest && output.manifestDigest == some (rawDigest manifestKey))
  match ← runScript (validate expected runZero) [] with
  | .error error => throw <| IO.userError error.message
  | .ok output =>
    check "run0 no entry and no artifacts" (output.details.runId == 0 && output.details.entry == "no" &&
      output.files.isEmpty && output.manifest.isNone && output.stdout.isEmpty)
    check "unknown counts remain unknown" (output.details.stdoutObserved.isNone &&
      output.details.stdoutCaptured.isNone && output.details.stdoutTruncated.isNone)
  check "preflight setup failure allowed" (accepted (← runScript
    (validate { expected with preflight := true } runZero) []))
  for forged in [{runZero with stdout := some "forged".toUTF8},
      {runZero with stderr := some .empty}, {runZero with manifest := some manifest},
      {runZero with stored := some (report false)}, {runZero with blobs := received.blobs}] do
    check "run0 rejects every artifact class" (rejected (← runScript (validate expected forged) []))
  check "wrong requested profile rejects" (rejected (← runScript (validate {expected with profile := "other"} received) []))
  check "wrong runtime identity rejects" (rejected (← runScript (validate {expected with runtimeDigest := "other"} received) []))
  check "stored byte mismatch rejects" (rejected (← runScript (validate expected {received with stored := some "forged".toUTF8}) []))
  check "stored retrieval status mismatch rejects" (rejected (← runScript
    (validate expected {received with terminal := {received.terminal with retrieved := 126}}) []))
  check "known capture count mismatch rejects" (rejected (← runScript
    (validate expected {received with stdout := some "ok".toUTF8}) []))
  check "capture policy cap rejects" (rejected (← runScript
    (validate expected {received with stdout := some "123456789".toUTF8}) []))
  check "complete export requires manifest" (rejected (← runScript
    (validate expected {received with manifest := none}) []))
  check "malformed hash reply rejects" (rejected (← runScript (validate expected received)
    [({op := .sha256, left := manifest}, (0, .empty))]))
  check "native hash failure retains errno" (match ← runScript (validate expected received)
      [({op := .sha256, left := manifest}, (0 - 5, .empty))] with
    | .error error => error.errno == some 5 | .ok _ => false)
  check "wrong blob content hash rejects" (rejected (← runScript (validate expected received)
    [manifestHash, ({op := .sha256, left := content}, (0, rawDigest manifestKey))]))
  check "missing referenced blob rejects" (rejected (← runScript
    (validateExport limits manifest manifestKey 1 []) [manifestHash]))
  check "omitted report count mismatch rejects" (rejected (← runScript
    (validateExport limits manifest manifestKey 0 received.blobs) [manifestHash]))
  let emptyKey := "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
  check "unreferenced hashed blob rejects" (rejected (← runScript
    (validateExport limits manifest manifestKey 1 (received.blobs ++ [⟨emptyKey.toUTF8, .empty⟩]))
    (hashes ++ [({op := .sha256, left := .empty}, (0, rawDigest emptyKey))])))
  check "duplicate hashed blob rejects" (rejected (← runScript
    (validateExport limits manifest manifestKey 1 (received.blobs ++ received.blobs)) (hashes ++ [contentHash])))
  for bad in ["LCEXPORT1\nD 61\nO 61\n", "LCEXPORT1\nO 612f62\n", "LCEXPORT1\nO 61\nD 612f62\n",
      "LCEXPORT1\nD ff\n", "LCEXPORT1\nD 2e2e2f61\n", "LCEXPORT1\nD 2E746d70\n",
      "LCEXPORT1\nD 61", "LCEXPORT1\nD 61 \n", "LCEXPORT1\nD 61\ntrailing"] do
    check "hostile manifest rejected" (rejected (parseManifest limits bad.toUTF8))
  check "noncanonical decimal rejects" (rejected (parseManifest limits
    ("LCEXPORT1\nF 0 61 03 " ++ contentKey ++ "\n").toUTF8))
  check "declared aggregate bytes reject before binding" (rejected (parseManifest limits
    ("LCEXPORT1\nF 0 61 33 " ++ contentKey ++ "\n").toUTF8))
  check "inode bound rejects before second node" (rejected (parseManifest {limits with inodesMax := 1}
    "LCEXPORT1\nD 61\nD 62\n".toUTF8))
  check "Unicode path preserved" (match decodePath "c3a9".toUTF8 with
    | .ok path => path.text == "é" | .error _ => false)
  check "extra numeric JSON lexeme retained" ((knownReport false (report true)).bind (Json.get? · "extra_number") ==
    some (.number "-1.25e+2".toUTF8.data.toList))
  let duplicate := "{\"profile\":\"other\",".toUTF8 ++ (report true).extract 1 (report true).size
  check "duplicate decoded report key rejects" (rejected (checkReport expected {received with report := duplicate}))
  IO.println "Artifact checks passed: exact framed report/captures/export, actual hash requests, run0/preflight, hostile paths/hierarchy/bounds/blobs and preserved unknown/extra observations."
