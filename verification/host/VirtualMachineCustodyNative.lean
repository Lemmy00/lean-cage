import VirtualMachineCustodyProofs

open LeanCage.Host
open LeanCage.Host.Filesystem

private def checked {α : Type} (result : Filesystem.Result α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error.message)

private def assertCase (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

-- §FS-host-boundary.acceptance: Only the fixture's spawn reply is synthetic; no child is started.
private def failSpawn {α : Type} : LeanCage.Host.Program α → IO α
  | .pure value => pure value
  | .call (.spawn _) next => failSpawn (next (.error "synthetic spawn acknowledgement error"))
  | .call _ _ => throw (IO.userError "spawn-error source unexpectedly continued into another operation")

private def policy : Policy.Accepted := {
  value := .object []
  raw := "{}".toUTF8
  transport := ⟨0, 0, 0, 2⟩
  snapshot := ⟨0, 2, 0⟩
  wallMilliseconds := 1 }

private def bundle : Validation.Bundle :=
  ⟨"/not-executed", .null, String.ofList (List.replicate 64 'a'), []⟩

private def exercise : IO Unit := do
  let run ← checked (← Filesystem.execute RunDirectory.create)
  IO.println s!"owned fixture directory: {run.path}"
  checked (← Filesystem.execute (writeNew run.directory.fd "policy.json".toUTF8 policy.raw))
  let retainedDirectory ← checked (← Filesystem.execute
    (Directories.openAt run.directory.information.uid run.directory.fd ".".toUTF8))
  let retainedContainer ← checked (← Filesystem.execute
    (Directories.openAt run.container.information.uid run.container.fd ".".toUTF8))
  let report := ("{\"schema\":\"leancage-result-v1\",\"run_id\":0," ++
    "\"entry\":\"unknown\",\"cleanup\":\"unknown\"}").toUTF8
  let wire := Transport.identityPrefix Transport.Witness.request Transport.Witness.bundle ++
    (Transport.Witness.frame .report report).wire
  let transport := Transport.Witness.initial.run [.data wire]
  let vm ← failSpawn (VirtualMachine.run bundle run.path 1000000 transport)
  assertCase (vm.cleanup == "unknown" && vm.error == some "VM process creation failed")
    "spawn failure fabricated a definite not-started observation"
  let input ← Filesystem.execute (receive "fixture" bundle false policy vm)
  assertCase (input.rawReport == transport.report?) "spawn error changed the recognized raw report"
  let before := (transport.report?.bind (Artifacts.knownReport false)).map Json.render
  let after := input.outcome.report.map Json.render
  assertCase (before == after && before.isSome) "spawn error changed the recognized report"
  LeanCage.Host.Program.interpret (cleanupRun run input)
  let reopened ← checked (← Filesystem.execute
    (Directories.openAt run.directory.information.uid retainedContainer.fd run.name))
  let copied ← checked (← Filesystem.execute (copyAt reopened.fd "policy.json".toUTF8 64))
  assertCase (copied.bytes == policy.raw) "unknown child lifetime released its backing files/name"
  let _ ← Filesystem.call { op := .close, first := reopened.fd }
  -- §FS-host-boundary.acceptance: The test starts no child and cleans only its own fresh fixture.
  Filesystem.execute (RunDirectory.cleanup {
    run with directory := retainedDirectory, container := retainedContainer })
  IO.println "actual run directory + synthetic spawn error: name/files and known report retained"

def main : IO UInt32 := do
  exercise
  return 0
