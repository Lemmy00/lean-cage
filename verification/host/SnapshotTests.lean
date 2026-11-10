import LeanCageHost.Snapshot

open LeanCage.Host LeanCage.Host.Filesystem LeanCage.Host.Snapshot

-- §FS-host-boundary.snapshot: Scripted replies exercise decisions without host OS experiments.
private def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw <| IO.userError ("snapshot check failed: " ++ label)

private def runScript {α : Type} (program : Program α) (script : List (Request × Reply)) : IO α := do
  let pending ← IO.mkRef script
  let result ← program.interpret (fun request => do
    match ← pending.get with
    | [] => throw <| IO.userError "unexpected extra snapshot primitive"
    | (expected, reply) :: rest =>
      unless request = expected do throw <| IO.userError s!"unexpected snapshot operation {request.op.code}"
      pending.set rest
      return reply)
  check "all scripted effects consumed" (← pending.get).isEmpty
  return result

private def statReply (inode mode links size : Nat) : Reply :=
  (0, ([1, inode, mode, links, 1000, 1000, size, 1, 0, 1, 0].map
    (littleEndian 8)).foldl (· ++ ·) .empty)

private def directory : Reply := statReply 1 16877 2 0
private def regular (size : Nat) : Reply := statReply 2 33188 1 size
private def ok : Reply := (0, .empty)
private def name (text : String) : Reply := (1, text.toUTF8)
private def shaABC : ByteArray := ⟨#[186, 120, 22, 191, 143, 1, 207, 234, 65, 65, 64, 222, 93, 174, 34, 35, 176, 3, 97, 163, 150, 23, 122, 156, 180, 16, 255, 97, 242, 0, 21, 173]⟩
private def shaZ : ByteArray := ⟨#[89, 78, 81, 154, 228, 153, 49, 43, 41, 67, 59, 125, 216, 169, 127, 240, 104, 222, 252, 186, 151, 85, 182, 213, 208, 14, 132, 197, 36, 214, 123, 6]⟩
private def tree : ByteArray := "LCTREE1\nF 0 66696c652e747874 3 ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad\n".toUTF8
private def shaTree : ByteArray := ⟨#[174, 188, 232, 196, 206, 222, 72, 55, 224, 214, 129, 20, 159, 155, 13, 245, 143, 177, 0, 181, 255, 247, 147, 106, 154, 182, 200, 160, 153, 54, 44, 244]⟩
private def limits : LeanCage.Host.Snapshot.Limits := ⟨16, 8, 4⟩
private def cursor : UInt64 := 256

private def publicAttribute (fd : UInt64) : Request × Reply :=
  ({op := .getAttribute, first := fd, second := 1, left := PrivateNames.attributeName}, (0 - 61, .empty))

private def directoryId (inode : Nat) : ByteArray :=
  littleEndian 8 1 ++ littleEndian 8 inode ++ littleEndian 8 1

private def selectedCwd (spelling : String := "/") : List (Request × Reply) :=
  [({op := .openAt, first := cwd, second := directoryFlags, left := ".".toUTF8}, (2, .empty)),
   publicAttribute 2, ({op := .workingDirectory}, (0, spelling.toUTF8))]

private def ancestryRoot : List (Request × Reply) :=
  [({op := .openAt, first := cwd, second := directoryFlags, left := "/".toUTF8}, (3, .empty)),
   publicAttribute 3, ({op := .directoryIdentity, first := 3}, (0, directoryId 1)),
   ({op := .close, first := 3}, ok),
   ({op := .openAt, first := 2, second := directoryFlags, left := ".".toUTF8}, (4, .empty)),
   publicAttribute 4]

private def sourceRoot : List (Request × Reply) :=
  selectedCwd ++ ancestryRoot ++
    [({op := .directoryIdentity, first := 4}, (0, directoryId 1)),
     ({op := .close, first := 4}, ok)]

private def sourceFile (name : String) : List (Request × Reply) :=
  sourceRoot ++
    [({op := .openAt, first := 2, second := readFlags, left := name.toUTF8}, (3, .empty)),
     publicAttribute 3, ({op := .close, first := 2}, ok)]

private def initial : List (Request × Reply) :=
  sourceRoot ++
    [({op := .openAt, first := 2, second := directoryFlags, left := "workspace".toUTF8}, (3, .empty)),
     publicAttribute 3, ({op := .close, first := 2}, ok),
     ({op := .stat, first := 3}, directory),
     ({op := .dirOpen, first := 3}, (0, littleEndian 8 256))]

private def listing : List (Request × Reply) :=
  [({op := .dirNext, first := cursor}, name "."),
   ({op := .dirNext, first := cursor}, name ".."),
   ({op := .dirNext, first := cursor}, name "file.txt"),
   ({op := .dirNext, first := cursor}, ok)]

private def fileStart : List (Request × Reply) :=
  [({op := .openAt, first := 3, second := readFlags, left := "file.txt".toUTF8}, (4, .empty)),
   publicAttribute 4,
   ({op := .stat, first := 4}, regular 3),
   ({op := .stat, first := 4}, regular 3)]

private def closed : List (Request × Reply) :=
  [({op := .close, first := 4}, ok), ({op := .dirClose, first := cursor, second := 3}, ok)]

private def denied {α : Type} (result : Result α) : Bool :=
  match result with
  | .error error => error.errno.isNone
  | .ok _ => false

def main : IO Unit := do
  let script := initial ++ listing ++ fileStart ++
    [({op := .read, first := 4, second := 17, third := 1}, (3, "abc".toUTF8)),
     ({op := .read, first := 4, second := 14, third := 4}, ok),
     ({op := .stat, first := 4}, regular 3), ({op := .close, first := 4}, ok),
     ({op := .sha256, left := "abc".toUTF8}, (0, shaABC)),
     ({op := .stat, first := 3}, directory), ({op := .dirClose, first := cursor, second := 3}, ok),
     ({op := .sha256, left := tree}, (0, shaTree)),
     ({op := .sha256, left := "z".toUTF8}, (0, shaZ))]
  match ← runScript (freeze (some "workspace".toUTF8) (.bytes "z".toUTF8) limits) script with
  | .error error => throw <| IO.userError error.message
  | .ok result =>
    check "canonical LCTREE1 actual bytes" (result.tree == some tree)
    check "exact tree hash" (result.treeDigest == some shaTree)
    check "exact stdin bytes/hash" (result.stdin == some "z".toUTF8 && result.stdinDigest == some shaZ)
    check "root and tmp charged initially" (result.count == 3 && result.entries.size == 1)
    check "workspace aggregate" (result.workspaceBytes == 3)
    check "file and stdin blobs retained" (result.blobs.length == 2)
  check "oversized in-memory stdin has no effects" (denied (← runScript
    (freeze none (.bytes "12345".toUTF8) limits) []))
  check "unsupported limits have no effects" (denied (← runScript
    (freeze none .absent ⟨16, 1, 4⟩) []))
  check "directory close keeps the retained expected FD in its request" (denied (← runScript
    (closeDirectory 3 cursor (.ok ()))
    [({op := .dirClose, first := cursor, second := 3}, (0, "invalid".toUTF8))]))
  check "repeated cursor entry rejects" (denied (← runScript
    (freeze (some "workspace".toUTF8) .absent limits)
    (initial ++ [({op := .dirNext, first := cursor}, name "."),
      ({op := .dirNext, first := cursor}, name "."), ({op := .dirClose, first := cursor, second := 3}, ok)])))
  check "reserved tmp rejected before child open" (denied (← runScript
    (freeze (some "workspace".toUTF8) .absent limits)
    (initial ++ [({op := .dirNext, first := cursor}, name ".tmp"),
      ({op := .dirNext, first := cursor}, ok), ({op := .dirClose, first := cursor, second := 3}, ok)])))
  check "invalid UTF8 rejected before child open" (denied (← runScript
    (freeze (some "workspace".toUTF8) .absent limits)
    (initial ++ [({op := .dirNext, first := cursor}, (1, ⟨#[255]⟩)),
      ({op := .dirClose, first := cursor, second := 3}, ok)])))
  check "inode enumeration bound precedes opening" (denied (← runScript
    (freeze (some "workspace".toUTF8) .absent ⟨16, 2, 4⟩)
    (initial ++ [({op := .dirNext, first := cursor}, name "file.txt"),
      ({op := .dirClose, first := cursor, second := 3}, ok)])))
  check "hard links rejected on retained descriptor" (denied (← runScript
    (freeze (some "workspace".toUTF8) .absent limits)
    (initial ++ listing ++
      [({op := .openAt, first := 3, second := readFlags, left := "file.txt".toUTF8}, (4, .empty)),
   publicAttribute 4,
       ({op := .stat, first := 4}, statReply 2 33188 2 3)] ++ closed)))
  check "special files rejected on retained descriptor" (denied (← runScript
    (freeze (some "workspace".toUTF8) .absent limits)
    (initial ++ listing ++
      [({op := .openAt, first := 3, second := readFlags, left := "file.txt".toUTF8}, (4, .empty)),
   publicAttribute 4,
       ({op := .stat, first := 4}, statReply 2 4516 1 0)] ++ closed)))
  check "malformed read acknowledgement rejects" (denied (← runScript
    (freeze (some "workspace".toUTF8) .absent limits)
    (initial ++ listing ++ fileStart ++
      [({op := .read, first := 4, second := 17, third := 1}, (4, "abc".toUTF8))] ++ closed)))
  let changed := statReply 2 33188 1 4
  check "observed source changes reject" (denied (← runScript
    (freeze (some "workspace".toUTF8) .absent limits)
    (initial ++ listing ++ fileStart ++
      [({op := .read, first := 4, second := 17, third := 1}, (3, "abc".toUTF8)),
       ({op := .read, first := 4, second := 14, third := 4}, ok), ({op := .stat, first := 4}, changed)] ++ closed)))
  match ← runScript (freeze none (.file "stdin".toUTF8) limits)
      (sourceFile "stdin" ++ [({op := .stat, first := 3}, regular 1), ({op := .read, first := 3, second := 5, third := 1}, (1, "z".toUTF8)),
       ({op := .read, first := 3, second := 4, third := 2}, ok), ({op := .stat, first := 3}, regular 1),
       ({op := .close, first := 3}, ok), ({op := .sha256, left := "z".toUTF8}, (0, shaZ))]) with
  | .error error => throw <| IO.userError error.message
  | .ok result => check "file stdin same copied bytes" (result.tree.isNone && result.stdin == some "z".toUTF8)
  match ← runScript (freeze none (.file "denied".toUTF8) limits)
      (sourceRoot ++ [({op := .openAt, first := 2, second := readFlags, left := "denied".toUTF8}, (0 - 13, .empty)),
        ({op := .close, first := 2}, ok)]) with
  | .ok _ => throw <| IO.userError "native failure was accepted"
  | .error error => check "native errno preserved" (error.errno == some 13)
  check "reserved caller ancestor denied before opening" (denied (← runScript
    (freeze (some "/.leancage-private-1000/key".toUTF8) .absent limits) []))
  check "reserved nested component denied before opening" (denied (← runScript
    (freeze (some "workspace".toUTF8) .absent limits)
    (initial ++ [({op := .dirNext, first := cursor}, name ".leancage-private-stage"),
      ({op := .dirNext, first := cursor}, ok), ({op := .dirClose, first := cursor, second := 3}, ok)])))
  let marked (fd : UInt64) : Request × Reply :=
    ({op := .getAttribute, first := fd, second := 1, left := PrivateNames.attributeName},
      (1, PrivateNames.attributeValue))
  check "private root alias denied on actual opened FD" (denied (← runScript
    (freeze (some "workspace".toUTF8) .absent limits)
    (sourceRoot ++
      [({op := .openAt, first := 2, second := directoryFlags, left := "workspace".toUTF8}, (3, .empty)),
       marked 3, ({op := .close, first := 3}, ok), ({op := .close, first := 2}, ok)])))
  check "private nested alias denied before read/stat" (denied (← runScript
    (freeze (some "workspace".toUTF8) .absent limits)
    (initial ++ listing ++
      [({op := .openAt, first := 3, second := readFlags, left := "file.txt".toUTF8}, (4, .empty)),
       marked 4, ({op := .close, first := 4}, ok), ({op := .dirClose, first := cursor, second := 3}, ok)])))
  let renamedCwd := selectedCwd "/renamed/parent" ++ ancestryRoot ++
    [({op := .directoryIdentity, first := 4}, (0, directoryId 9)),
     ({op := .openAt, first := 4, second := directoryFlags, left := "..".toUTF8}, (5, .empty)),
     publicAttribute 5, ({op := .close, first := 4}, ok),
     ({op := .directoryIdentity, first := 5}, (0, directoryId 1)),
     ({op := .close, first := 5}, ok)]
  match ← runScript (SourcePaths.start "input".toUTF8) renamedCwd with
  | .error error => throw <| IO.userError error.message
  | .ok selected =>
    check "relative selection retains original CWD, not getcwd spelling"
      (selected.base == 2 && selected.parts == ["input".toUTF8])
  let ancestryDenied := selectedCwd ++ ancestryRoot ++
    [({op := .directoryIdentity, first := 4}, (0, directoryId 9)),
     ({op := .openAt, first := 4, second := directoryFlags, left := "..".toUTF8}, (5, .empty)),
     marked 5, ({op := .close, first := 5}, ok), ({op := .close, first := 4}, ok),
     ({op := .close, first := 2}, ok)]
  check "private CWD ancestor alias rejects before input open"
    (match ← runScript (SourcePaths.start "input".toUTF8) ancestryDenied with
    | .error _ => true | .ok _ => false)
  check "reserved CWD spelling rejects before ancestry or input open"
    (match ← runScript (SourcePaths.start "input".toUTF8)
      (selectedCwd "/tmp/.leancage-private-new/sub" ++ [({op := .close, first := 2}, ok)]) with
    | .error _ => true | .ok _ => false)
  check "ancestry exhaustion closes current duplicate and fails"
    (match ← runScript (SourcePaths.ancestry 1 4 (directoryId 1))
      [({op := .directoryIdentity, first := 4}, (0, directoryId 9)),
       ({op := .openAt, first := 4, second := directoryFlags, left := "..".toUTF8}, (5, .empty)),
       publicAttribute 5, ({op := .close, first := 4}, ok), ({op := .close, first := 5}, ok)] with
    | .error _ => true | .ok _ => false)
  check "directory identity requires exact supported payload"
    (match ← runScript (SourcePaths.identity 4)
      [({op := .directoryIdentity, first := 4}, (0, littleEndian 8 1))] with
    | .error _ => true | .ok _ => false)
  check "unsupported private attribute lookup denies before input read"
    (match ← runScript (SourcePaths.openAt 2 "input".toUTF8 false)
      [({op := .openAt, first := 2, second := readFlags, left := "input".toUTF8}, (3, .empty)),
       ({op := .getAttribute, first := 3, second := 1, left := PrivateNames.attributeName}, (0 - 95, .empty)),
       ({op := .close, first := 3}, ok)] with
    | .error _ => true | .ok _ => false)
  IO.println "Snapshot checks passed: exact tree/stdin/blob bytes, bounds, failures, cleanup requests and source observations."
