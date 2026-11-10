import PublicationProofs

open LeanCage.Host LeanCage.Host.Filesystem

-- §FS-host-boundary.publication: Scripted replies exercise progress and uncertain commit handling.
private def check (label : String) (good : Bool) : IO Unit :=
  unless good do throw <| IO.userError ("publication check failed: " ++ label)

private def runScript {α : Type} (program : Filesystem.Program α) (script : List (Request × Reply)) : IO α := do
  let pending ← IO.mkRef script
  let result ← program.interpret (fun request => do
    match ← pending.get with
    | [] => throw <| IO.userError "unexpected publication effect"
    | (expected, reply) :: rest =>
      unless request = expected do throw <| IO.userError s!"unexpected publication primitive {request.op.code}"
      pending.set rest
      return reply)
  check "all effects consumed" (← pending.get).isEmpty
  return result

private def okay {α : Type} (result : Result α) : Bool :=
  match result with | .ok _ => true | .error _ => false
private def ok : Reply := (0, .empty)
private def opened : Request × Reply :=
  ({op := .openAt, first := 7, second := newFileFlags, third := 384, left := "file".toUTF8}, (8, .empty))
private def information : Stat := ⟨1, 2, 16832, 2, 1000, 1000, 0, 1, 0, 1, 0⟩
private def parent : Directories.Parent := ⟨⟨7, information⟩, "final".toUTF8, 1000⟩
private def stage : Directories.Fresh := ⟨⟨⟨8, information⟩, ".leancage-private-fresh".toUTF8⟩, ⟨9, information⟩⟩
private def policy : Policy.Accepted := {
  raw := .empty
  value := .null
  snapshot := ⟨0, 2, 0⟩
  transport := ⟨0, 0, 0, 2⟩
  wallMilliseconds := 1 }
private def outcome : Outcome := {
  requestId := "test"
  bundleId := "test"
  command := "check"
  status := "incomplete"
  report := some .null
  exitCode := 126
  vmCleanup := "unknown"
  error := some "channel lost" }
private def input : Publication.Input := {
  outcome := outcome
  policy := policy
  boot := .empty
  rawReport := none
  received := none
  validated := none }
private def closes : List (Request × Reply) :=
  [({op := .close, first := 8}, (0 - 5, .empty)),
   ({op := .close, first := 9}, ok), ({op := .close, first := 7}, ok)]

def main : IO Unit := do
  check "partial write resumes at acknowledged offset" (okay (← runScript
    (writeNew 7 "file".toUTF8 "abc".toUTF8)
    [opened, ({op := .write, first := 8, left := "abc".toUTF8}, (1, .empty)),
     ({op := .write, first := 8, left := "bc".toUTF8}, (2, .empty)), ({op := .close, first := 8}, ok)]))
  check "zero progress rejects and releases new file" (!(okay (← runScript
    (writeNew 7 "file".toUTF8 "abc".toUTF8)
    [opened, ({op := .write, first := 8, left := "abc".toUTF8}, ok), ({op := .close, first := 8}, ok)])))
  check "oversized acknowledgement rejects" (!(okay (← runScript
    (writeNew 7 "file".toUTF8 "abc".toUTF8)
    [opened, ({op := .write, first := 8, left := "abc".toUTF8}, (4, .empty)), ({op := .close, first := 8}, ok)])))
  let bytes := ByteArray.mk (Array.replicate 65537 97)
  check "write requests are bounded before crossing chunk boundary" (okay (← runScript
    (writeNew 7 "file".toUTF8 bytes)
    [opened, ({op := .write, first := 8, left := bytes.extract 0 65536}, (65536, .empty)),
     ({op := .write, first := 8, left := bytes.extract 65536 65537}, (1, .empty)),
     ({op := .close, first := 8}, ok)]))
  check "invalid commit ACK only closes; it never deletes possible publication" (!(okay (← runScript
    (Publication.commitTail parent stage input outcome (1, .empty)) closes)))
  check "successful rename remains stored despite separately observed close failure" (okay (← runScript
    (Publication.commitTail parent stage input outcome ok) closes))
  IO.println "Publication checks passed: exclusive file writes, partial ACK progress, bounded chunks and uncertain commit handling."
