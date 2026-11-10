import LeanCageHost.Artifacts.Report
import LeanCageHost.Artifacts.Manifest

namespace LeanCage.Host.Artifacts

open Filesystem

structure BlobState where
  values : Array CheckedBlob := #[]
  index : Std.TreeMap String CheckedBlob compare := ∅
  total : Nat := 0

def BlobState.insert (state : BlobState) (blob : CheckedBlob) : BlobState := {
  values := state.values.push blob
  index := state.index.insert blob.key blob
  total := state.total + blob.bytes.size }

-- §FS-host-boundary.artifacts: Each accepted blob is hashed through the actual byte primitive.
def checkBlobs (limits : Transport.Limits) : List Transport.Blob → BlobState → Program (Result BlobState)
  | [], state => pure (.ok state)
  | source :: rest, state =>
    if state.values.size ≥ limits.inodesMax then pure (.error "export blob inode limit exceeded")
    else if source.digest.size != 64 || !Transport.lowerHex source.digest then
      pure (.error "invalid export blob digest encoding")
    else if state.total + source.content.size > limits.workspaceMax then
      pure (.error "export blob aggregate limit exceeded")
    else (Filesystem.hash source.content).bind fun result =>
      match result with
      | .error error => pure (.error error)
      | .ok digest =>
        if checked : digest.size = 32 ∧ (Snapshot.hex digest).toUTF8 = source.digest then
          let blob : CheckedBlob := ⟨source, digest, checked.1, checked.2⟩
          if state.index.contains blob.key then pure (.error "duplicate export blob identity")
          else checkBlobs limits rest (state.insert blob)
        else pure (.error "export blob content identity differs")

structure BoundFiles where
  reversed : List ValidatedFile := []
  required : Std.TreeSet String compare := ∅

-- §FS-host-boundary.artifacts: A manifest file selects those exact hashed bytes and their size.
def bindFiles (blobs : BlobState) : List Node → BoundFiles → Result BoundFiles
  | [], state => .ok state
  | node :: rest, state =>
    match node with
    | .directory _ | .omitted _ => bindFiles blobs rest state
    | .file path executable size digest =>
      match blobs.index[digest]? with
      | none => .error "missing referenced export blob"
      | some blob =>
        if blob.key != digest || blob.bytes.size != size then .error "export file identity or size differs"
        else bindFiles blobs rest {
          reversed := ⟨path, executable, blob.bytes, blob.digest⟩ :: state.reversed
          required := state.required.insert digest }

def allReferenced (blobs : BlobState) (files : BoundFiles) : Bool :=
  blobs.values.toList.all (fun blob => files.required.contains blob.key)

structure Export where
  files : List ValidatedFile
  dirs : List ExportPath
  omitted : List ExportPath
  manifest : ByteArray
  digest : ByteArray

-- §FS-host-boundary.artifacts: Complete validation precedes any publication; only hashes occur.
def validateExport (limits : Transport.Limits) (raw : ByteArray) (expectedDigest : String)
    (omitted : Nat) (sources : List Transport.Blob) : Program (Result Export) :=
  if raw.size > manifestMax || !digestText expectedDigest then
    pure (.error "invalid export manifest identity or size")
  else (Filesystem.hash raw).bind fun hashed =>
    match hashed with
    | .error error => pure (.error error)
    | .ok digest =>
      if digest.size != 32 || Snapshot.hex digest != expectedDigest then
        pure (.error "export manifest content identity differs")
      else match parseManifest limits raw with
      | .error error => pure (.error error)
      | .ok manifest =>
        if manifest.omitted != omitted then pure (.error "export omitted count differs from report")
        else (checkBlobs limits sources {}).bind fun checked =>
          match checked with
          | .error error => pure (.error error)
          | .ok blobs =>
            match bindFiles blobs manifest.entries.toList {} with
            | .error error => pure (.error error)
            | .ok files =>
              if !allReferenced blobs files then pure (.error "unreferenced export blob")
              else pure (.ok ⟨files.reversed.reverse, manifest.dirs, manifest.omittedPaths, raw, digest⟩)

def assemble (received : Transport.Result) (value : Json.Value) (report : Report)
    (exported : Option Export) : Validated := {
  rawReport := received.report
  report := value
  details := report
  stored := received.stored
  stdout := received.stdout.getD .empty
  stderr := received.stderr.getD .empty
  files := exported.map (·.files) |>.getD []
  dirs := exported.map (·.dirs) |>.getD []
  omitted := exported.map (·.omitted) |>.getD []
  manifest := exported.map (·.manifest)
  manifestDigest := exported.map (·.digest)
}

-- §FS-host-boundary.artifacts: No failure returns partially validated complete artifacts.
def validate (expected : Expected) (received : Transport.Result) : Program (Result Validated) :=
  match checkReport expected received with
  | .error error => pure (.error error)
  | .ok (value, report) =>
    if report.exportState = "complete" then
      match received.manifest, report.exportDigest with
      | some raw, some digest =>
        (validateExport expected.limits raw digest report.exportOmitted received.blobs).bind fun exported =>
          pure (exported.map (fun valueExport => assemble received value report (some valueExport)))
      | _, _ => pure (.error "missing committed export identity")
    else pure (.ok (assemble received value report none))

end LeanCage.Host.Artifacts
