import LeanCageHost.Program
import LeanCageHost.Json
import LeanCageHost.GatewayWire
import LeanCageHost.Snapshot
import LeanCageHost.SourcePaths
import LeanCageHost.RunDirectory

namespace LeanCage.Host.Validation
open Filesystem

structure Bundle where
  root : String
  manifest : Json.Value
  identity : String
  libraryDirectories : List String
  deriving Inhabited

def canonicalName (name : String) : Bool :=
  !name.isEmpty && name.utf8ByteSize ≤ 4095 && !name.contains '\x00' &&
    !name.contains ':' && (name.splitOn "/").all (fun part =>
      !part.isEmpty && part != "." && part != "..")

def stringField (value : Json.Value) (key : String) : Option String :=
  match Json.get? value key with
  | some (.string text) => some text
  | _ => none

def bundleFiles (manifest : Json.Value) : Option (List (String × Json.Value)) :=
  match Json.get? manifest "files" with
  | some (.object fields) => some fields
  | _ => none

def rootString (bytes : ByteArray) : Filesystem.Result String :=
  match String.fromUTF8? bytes with
  | none => .error "the selected bundle location requires supported UTF-8 loader paths"
  | some path =>
    if path.isEmpty || path.contains ':' || path.contains '\x00' then
      .error "unsupported bundle loader path"
    else .ok path

-- §FS-host-boundary.caller: Bundle values are read from the actual selected immutable bootstrap.
def loadBundle (rootBytes : ByteArray) : Filesystem.Program (Filesystem.Result Bundle) := do
  let .ok root := rootString rootBytes | return .error "unsupported bundle loader path"
  let raw ← readBounded (root ++ "/manifest.json").toUTF8 treeMax
  let .ok raw := raw | return raw.map (fun _ => default)
  let digest ← hash raw
  let .ok digest := digest | return digest.map (fun _ => default)
  let manifest ← pure (Json.parse raw treeMax)
  let .ok manifest := manifest | return .error "invalid bundle manifest JSON"
  if stringField manifest "schema" != some "leancage-bundle-v1" then
    return .error "unsupported bundle manifest schema"
  let some files := bundleFiles manifest | return .error "missing bundle file inventory"
  let mut directories : List String := []
  for (name, value) in files do
    if !canonicalName name then return .error "noncanonical bundle component path"
    let .string digest := value | return .error "invalid bundle component digest"
    if digest.utf8ByteSize != 64 || !digest.toList.all (fun c =>
        ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')) then
      return .error "invalid bundle component digest"
    if name.startsWith "lib/" then
      let parent := String.intercalate "/" (name.splitOn "/").dropLast
      let directory := root ++ "/" ++ parent
      if !directories.contains directory then directories := directory :: directories
  return .ok ⟨root, manifest, Snapshot.hex digest, directories.mergeSort (· ≤ ·)⟩

def copyIdentified (bundle : Bundle) (name : String) (limit : Nat) :
    Filesystem.Program (Filesystem.Result ByteArray) := do
  let some files := bundleFiles bundle.manifest | return .error "missing bundle file inventory"
  let some (_, .string expected) := files.find? (fun field => field.1 == name)
    | return .error "required bundle component is not identified"
  let content ← readBounded (bundle.root ++ "/" ++ name).toUTF8 limit
  match content with
  | .error error => return .error error
  | .ok bytes =>
    let digest ← hash bytes
    match digest with
    | .error error => return .error error
    | .ok value =>
      if Snapshot.hex value == expected then return .ok bytes
      else return .error "bundle component identity differs"

def checkFile (bundle : Bundle) (name : String) (limit : Nat) :
    Filesystem.Program (Filesystem.Result Unit) := do
  let copied ← copyIdentified bundle name limit
  return copied.map (fun _ => ())

-- §FS-host-boundary.caller: A selected bundle must identify this actual running engine.
def checkEngineIdentity (bundle : Bundle) : Filesystem.Program (Filesystem.Result Unit) := do
  let some files := bundleFiles bundle.manifest | return .error "missing bundle file inventory"
  let some (_, .string expected) := files.find? (fun field => field.1 == "bin/leancage-host")
    | return .error "the selected bundle does not identify its host engine"
  let opened ← Filesystem.Program.effect { op := .selfExecutable }
  let some fd := descriptor opened | return .error (failure "host executable open" opened)
  let copied ← (copyOpened fd workspaceMax).bind (closeResult fd)
  match copied with
  | .error error => return .error error
  | .ok copied =>
    let digest ← hash copied.bytes
    match digest with
    | .error error => return .error error
    | .ok digest =>
      if Snapshot.hex digest == expected then return .ok ()
      else return .error "the running host engine differs from the selected bundle"

-- §FS-host-boundary.caller: Every identified component is checked before VM use.
def checkBundle (bundle : Bundle) : Filesystem.Program (Filesystem.Result Unit) := do
  let some files := bundleFiles bundle.manifest | return .error "missing bundle file inventory"
  for (name, _) in files do
    let checked ← checkFile bundle name workspaceMax
    if let .error error := checked then return .error error
  return .ok ()

def environment (bundle : Bundle) : Array (String × Option String) :=
  #[("PATH", some "/usr/bin:/bin"), ("LC_ALL", some "C"),
    ("LD_LIBRARY_PATH", some (String.intercalate ":" bundle.libraryDirectories))]

-- §FS-host-boundary.publication: Total projection retains every parsed JSON field and number token.
def jsonToWire (value : Json.Value) : GatewayWire.Value :=
  match value with
  | .null => .null
  | .bool boolean => .boolean boolean
  | .string text => .string text
  | .number bytes => .number (ByteArray.mk bytes.toArray)
  | .array values => .array (values.toList.attach.map (fun child => jsonToWire child.val))
  | .object fields => .object (fields.attach.map (fun child =>
      (child.val.1, jsonToWire child.val.2)))
termination_by value
decreasing_by
  · have member := Array.sizeOf_lt_of_mem (by simpa using child.property)
    simp_all
    omega
  · have member := List.sizeOf_lt_of_mem child.property
    have second : sizeOf child.val.2 < sizeOf child.val := by
      cases child.val
      simp
      omega
    simp_all
    omega

def loadPolicy (request : GatewayWire.Request) :
    Filesystem.Program (Filesystem.Result ByteArray) :=
  let field := request.field GatewayWire.policySlot
  if field.kind == GatewayWire.rawKind then
    if field.bytes.size ≤ reportMax then pure (.ok field.bytes)
    else pure (.error "policy exceeds 65536 bytes")
  else if field.kind == GatewayWire.pathKind then do
    let copied ← SourcePaths.copyFile field.bytes reportMax
    return copied.map (·.bytes)
  else pure (.error "missing policy input")

def validatorArguments (bundle : Bundle) (policy : String) : IO.Process.SpawnArgs := {
  cmd := bundle.root ++ "/bin/controller"
  args := #["validate-policy", policy]
  inheritEnv := false
  env := environment bundle
  stdin := .null
  stdout := .piped
  stderr := .null }

abbrev ValidatorChild := IO.Process.Child {
  stdin := .null, stdout := .piped, stderr := .null }

structure ChildObservation where
  result : Filesystem.Result Json.Value
  reaped : Bool

def validationResult (raw : ByteArray) (code : Except String UInt32) (output : Except String ByteArray) :
    ChildObservation :=
  let result := match code, output with
    | .ok 0, .ok _ =>
      match Json.parse raw reportMax with
      | .ok value => .ok value
      | .error _ => .error ("policy JSON interpretation failed" : Failure)
    | .ok _, .ok bytes =>
      let diagnostic := (String.fromUTF8? bytes).getD "policy rejected"
      .error (diagnostic : Failure)
    | _, _ => .error (⟨"policy validator transport failed", some 5⟩ : Failure)
  ⟨result, match code with | .ok _ => true | .error _ => false⟩

-- §FS-host-boundary.ownership: Only a genuine wait status establishes that lookup can stop.
def observeChild (raw : ByteArray) (child : Except String ValidatorChild) :
    LeanCage.Host.Program ChildObservation :=
  match child with
  | .error error => pure ⟨.error (⟨error, some 5⟩ : Failure), false⟩
  | .ok child => do
    let output ← readStream (reportMax + 1) child.stdout reportMax .empty
    let code ← LeanCage.Host.Program.effect (.wait child)
    return validationResult raw code output

-- §FS-host-boundary.caller: Keep the existing result projection separate from reaping evidence.
def validationChild (raw : ByteArray) (child : Except String ValidatorChild) :
    LeanCage.Host.Program (Filesystem.Result Json.Value) := do
  let observed ← observeChild raw child
  return observed.result

def releaseDirectory (directory : RunDirectory.Owned) : Filesystem.Program Unit := do
  let _ ← Filesystem.Program.effect {op := .close, first := directory.directory.fd}
  let _ ← Filesystem.Program.effect {op := .close, first := directory.container.fd}
  pure ()

-- §FS-host-boundary.ownership: Unknown child lifetime keeps backing names unavailable to peers.
def finishValidation (directory : RunDirectory.Owned) (observed : ChildObservation) :
    LeanCage.Host.Program (Filesystem.Result Json.Value) := do
  let _ ← LeanCage.Host.Program.liftFilesystem <|
    if observed.reaped then RunDirectory.cleanup directory else releaseDirectory directory
  return observed.result

-- §FS-host-boundary.caller: The exact copied policy is the validator's private input.
def validateCopied (bundle : Bundle) (raw : ByteArray) :
    LeanCage.Host.Program (Filesystem.Result Json.Value) := do
  let temporary ← LeanCage.Host.Program.liftFilesystem RunDirectory.create
  let .ok directory := temporary | return .error "private validator directory creation failed"
  let policyPath := directory.path ++ "/policy.json"
  let written ← LeanCage.Host.Program.liftFilesystem
    (writeNew directory.directory.fd "policy.json".toUTF8 raw)
  match written with
  | .error error =>
    let _ ← LeanCage.Host.Program.liftFilesystem (RunDirectory.cleanup directory)
    return .error error
  | .ok _ =>
    let child ← LeanCage.Host.Program.effect (.spawn (validatorArguments bundle policyPath))
    let observed ← observeChild raw child
    finishValidation directory observed

def validate (request : GatewayWire.Request) :
    LeanCage.Host.Program (Filesystem.Result Json.Value) := do
  let loaded ← LeanCage.Host.Program.liftFilesystem <| loadBundle (request.field GatewayWire.bundleSlot).bytes
  match loaded with
  | .error error => return .error error
  | .ok bundle =>
    let checked ← LeanCage.Host.Program.liftFilesystem (checkFile bundle "bin/controller" workspaceMax)
    match checked with
    | .error error => return .error error
    | .ok _ =>
      let raw ← LeanCage.Host.Program.liftFilesystem (loadPolicy request)
      match raw with
      | .error error => return .error error
      | .ok bytes => validateCopied bundle bytes

end LeanCage.Host.Validation
