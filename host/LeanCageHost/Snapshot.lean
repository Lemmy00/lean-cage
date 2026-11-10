import Std
import LeanCageHost.SourcePaths

namespace LeanCage.Host.Snapshot

open Filesystem

structure Limits where
  workspaceBytes : Nat
  workspaceInodes : Nat
  stdinBytes : Nat

def Limits.supported (limits : Limits) : Bool :=
  limits.workspaceBytes ≤ workspaceMax && 2 ≤ limits.workspaceInodes &&
    limits.workspaceInodes ≤ inodeMax && limits.stdinBytes ≤ stdinMax

inductive Stdin where
  | absent
  | bytes (value : ByteArray)
  | file (path : ByteArray)

-- §FS-host-boundary.snapshot: Only strict UTF-8, single-component names enter retained traversal.
def ValidComponent (name : String) : Prop :=
  0 < name.toUTF8.size ∧ name.toUTF8.size ≤ 255 ∧ name ≠ "." ∧ name ≠ ".." ∧
    (0 : UInt8) ∉ name.toUTF8.data.toList ∧ (47 : UInt8) ∉ name.toUTF8.data.toList

instance (name : String) : Decidable (ValidComponent name) := by
  unfold ValidComponent
  infer_instance

def ValidPath (path : String) : Prop :=
  let components := path.splitOn "/"
  path.toUTF8.size ≤ 4095 ∧ 0 < components.length ∧ components.length ≤ 64 ∧
    components.head? ≠ some ".tmp" ∧ ∀ component ∈ components, ValidComponent component

instance (path : String) : Decidable (ValidPath path) := by
  unfold ValidPath
  infer_instance

structure RelativePath where
  text : String
  valid : ValidPath text

inductive Entry where
  | directory (path : RelativePath)
  | file (path : RelativePath) (executable : Bool) (size : Nat) (digest : ByteArray)

def Entry.path : Entry → RelativePath
  | .directory path => path
  | .file path _ _ _ => path

def Entry.size : Entry → Nat
  | .directory _ => 0
  | .file _ _ size _ => size

def hexChar (digit : Nat) : Char :=
  Char.ofNat (if digit < 10 then 48 + digit else 87 + digit)

def hex (bytes : ByteArray) : String :=
  String.ofList (bytes.data.toList.flatMap (fun byte =>
    [hexChar (byte.toNat / 16), hexChar (byte.toNat % 16)]))

-- §FS-workspace.filesystem: The actual producer preserves the version-1 tree byte format.
def Entry.line : Entry → ByteArray
  | .directory path => ("D " ++ hex path.text.toUTF8 ++ "\n").toUTF8
  | .file path executable size digest =>
    ("F " ++ (if executable then "1" else "0") ++ " " ++ hex path.text.toUTF8 ++ " " ++
      toString size ++ " " ++ hex digest ++ "\n").toUTF8

structure Blob where
  digest : ByteArray
  bytes : ByteArray

structure State where
  entries : Array Entry := #[]
  blobs : List Blob := []
  tree : ByteArray := "LCTREE1\n".toUTF8
  count : Nat := 2
  total : Nat := 0

structure Frozen where
  tree : Option ByteArray
  stdin : Option ByteArray
  treeDigest : Option ByteArray
  stdinDigest : Option ByteArray
  entries : Array Entry
  blobs : List Blob
  count : Nat
  workspaceBytes : Nat

def Frozen.workspaceIdentity (frozen : Frozen) : Option String :=
  frozen.treeDigest.map (fun digest => "sha256:" ++ hex digest)

def Frozen.stdinIdentity (frozen : Frozen) : Option String :=
  frozen.stdinDigest.map (fun digest => "sha256:" ++ hex digest)

def addBlob (blobs : List Blob) (digest bytes : ByteArray) : Result (List Blob) :=
  match blobs.find? (fun blob => blob.digest == digest) with
  | none => .ok (⟨digest, bytes⟩ :: blobs)
  | some prior =>
    if prior.bytes == bytes then .ok blobs else .error "snapshot digest collision"

def appendEntry (limits : Limits) (state : State) (entry : Entry) : Result State :=
  let line := entry.line
  if state.count + 1 > limits.workspaceInodes then .error "snapshot inode limit exceeded"
  else if state.total + entry.size > limits.workspaceBytes then .error "snapshot byte limit exceeded"
  else if state.tree.size + line.size > treeMax then .error "snapshot tree exceeds 4 MiB"
  else if state.entries.any (fun earlier => earlier.path.text == entry.path.text) then
    .error "duplicate snapshot path"
  else .ok {
    entries := state.entries.push entry
    blobs := state.blobs
    tree := state.tree ++ line
    count := state.count + 1
    total := state.total + entry.size
  }

def nameOfBytes (bytes : ByteArray) : Result String :=
  if bytes.size > 255 then .error "snapshot component exceeds 255 bytes"
  else match String.fromUTF8? bytes with
  | none => .error "snapshot name is not UTF-8"
  | some name =>
    if name = "." ∨ name = ".." ∨ ValidComponent name then .ok name
    else .error "unsupported snapshot component"

-- §FS-host-boundary.snapshot: Each cursor reply, including repeated dot entries, consumes fuel.
def enumerate : Nat → UInt64 → Nat → List String → List String → Program (Result (List String))
  | 0, _, _, _, _ => pure (.error "snapshot directory enumeration made no bounded progress")
  | fuel + 1, cursor, remaining, seen, names =>
    .call { op := .dirNext, first := cursor } fun reply =>
      if reply.1 == 0 && reply.2.isEmpty then pure (.ok names.reverse)
      else if reply.1 != 1 then pure (.error (failure "readdir" reply))
      else match nameOfBytes reply.2 with
      | .error error => pure (.error error)
      | .ok name =>
        if name ∈ seen then pure (.error "repeated snapshot directory entry")
        else if name = "." ∨ name = ".." then enumerate fuel cursor remaining (name :: seen) names
        else if names.length ≥ remaining then pure (.error "snapshot inode limit exceeded during enumeration")
        else enumerate fuel cursor remaining (name :: seen) (name :: names)

def bytesLE : List UInt8 → List UInt8 → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: rest, b :: more => if a = b then bytesLE rest more else a.toNat < b.toNat

def sortNames (names : List String) : List String :=
  names.mergeSort (fun a b => bytesLE a.toUTF8.data.toList b.toUTF8.data.toList)

-- §AR-host-boundary.primitives: The adapter checks the cursor still owns this exact retained FD.
def closeDirectory {α : Type} (fd cursor : UInt64) (result : Result α) : Program (Result α) :=
  .call { op := .dirClose, first := cursor, second := fd } fun reply =>
    match result with
    | .error error => pure (.error error)
    | .ok value =>
      if reply.1 == 0 && reply.2.isEmpty then pure (.ok value)
      else pure (.error (failure "closedir" reply))

-- §FS-host-boundary.snapshot: Keep the cursor's directory descriptor until all child opens finish.
mutual
  def walk : Nat → Limits → UInt64 → String → State → Program (Result State)
    | 0, _, fd, _, _ => closeResult fd (.error "snapshot traversal made no bounded progress")
    | fuel + 1, limits, fd, prefixName, state =>
      .call { op := .stat, first := fd } fun initialReply =>
        match parseStat initialReply with
        | none => closeResult fd (.error (failure "directory fstat" initialReply))
        | some before =>
          if !before.directory then closeResult fd (.error "snapshot directory changed type")
          else .call { op := .dirOpen, first := fd } fun opened =>
            if nativeError opened then closeResult fd (.error (failure "fdopendir" opened))
            else if opened.1 != 0 || opened.2.size != 8 then
              pure (.error "invalid snapshot directory ownership reply")
            else
              let pointer := fromLittleEndian opened.2
              if pointer = 0 then pure (.error "invalid snapshot directory cursor")
              else
                let cursor := pointer.toUInt64
                (enumerate (limits.workspaceInodes - state.count + 3) cursor
                  (limits.workspaceInodes - state.count) [] []).bind fun listing =>
                  match listing with
                  | .error error => closeDirectory fd cursor (.error error)
                  | .ok names =>
                    (walkChildren fuel limits fd prefixName (sortNames names) state).bind fun copied =>
                      match copied with
                      | .error error => closeDirectory fd cursor (.error error)
                      | .ok after =>
                        .call { op := .stat, first := fd } fun finalReply =>
                          match parseStat finalReply with
                          | none => closeDirectory fd cursor (.error (failure "directory fstat" finalReply))
                          | some final =>
                            closeDirectory fd cursor (if final == before then .ok after
                              else .error "directory changed during bounded snapshot")

  def walkChildren : Nat → Limits → UInt64 → String → List String → State → Program (Result State)
    | _, _, _, _, [], state => pure (.ok state)
    | 0, _, _, _, _ :: _, _ => pure (.error "snapshot traversal made no bounded progress")
    | fuel + 1, limits, parent, prefixName, name :: rest, state =>
      let path := prefixName ++ name
      if PrivateNames.reservedBytes name.toUTF8 then pure (.error "snapshot enters reserved private state")
      else if ¬ ValidComponent name then pure (.error "unsupported snapshot component")
      else if state.count ≥ limits.workspaceInodes then pure (.error "snapshot inode limit exceeded")
      else if valid : ValidPath path then
        (SourcePaths.openAt parent name.toUTF8 false).bind fun opened =>
          match opened with
          | .error error => pure (.error error)
          | .ok child =>
            .call { op := .stat, first := child } fun information =>
              match parseStat information with
              | none => closeResult child (.error (failure "snapshot fstat" information))
              | some stat =>
                if stat.directory then
                  match appendEntry limits state (.directory ⟨path, valid⟩) with
                  | .error error => closeResult child (.error error)
                  | .ok next =>
                    (walk fuel limits child (path ++ "/") next).bind fun result =>
                      match result with
                      | .error error => pure (.error error)
                      | .ok after => walkChildren fuel limits parent prefixName rest after
                else if stat.regular && stat.links == 1 then
                  ((copyOpened child (limits.workspaceBytes - state.total)).bind
                    (closeResult child)).bind fun result =>
                    match result with
                    | .error error => pure (.error error)
                    | .ok copied => (Filesystem.hash copied.bytes).bind fun hashed =>
                      match hashed with
                      | .error error => pure (.error error)
                      | .ok digest =>
                        match addBlob state.blobs digest copied.bytes with
                        | .error error => pure (.error error)
                        | .ok blobs =>
                          let entry := Entry.file ⟨path, valid⟩ (copied.stat.mode &&& 73 != 0)
                            copied.bytes.size digest
                          match appendEntry limits { state with blobs := blobs } entry with
                          | .error error => pure (.error error)
                          | .ok after => walkChildren fuel limits parent prefixName rest after
                else closeResult child (.error "input links and special files are unsupported")
      else pure (.error "unsupported snapshot path")
end

def copyWorkspace (workspace : Option ByteArray) (limits : Limits) : Program (Result State) :=
  match workspace with
  | none => pure (.ok {})
  | some path =>
    (SourcePaths.open path true).bind fun opened =>
      match opened with
      | .error error => pure (.error error)
      | .ok fd => walk (2 * limits.workspaceInodes + 1) limits fd "" {}

def copyStdin (stdin : Stdin) (limit : Nat) : Program (Result (Option ByteArray)) :=
  match stdin with
  | .absent => pure (.ok none)
  | .bytes bytes =>
    if bytes.size ≤ limit then pure (.ok (some bytes)) else pure (.error "stdin exceeds policy limit")
  | .file path => (SourcePaths.copyFile path limit).bind fun result =>
    pure (result.map (fun copied => some copied.bytes))

def identify (input : Option ByteArray) : Program (Result (Option ByteArray)) :=
  match input with
  | none => pure (.ok none)
  | some bytes => (Filesystem.hash bytes).bind fun result => pure (result.map some)

def includeStdin (blobs : List Blob) (input digest : Option ByteArray) : Result (List Blob) :=
  match input, digest with
  | some bytes, some digest => addBlob blobs digest bytes
  | none, none => .ok blobs
  | _, _ => .error "snapshot stdin identity differs"

-- §FS-host-boundary.snapshot: Hash only the acknowledged frozen bytes after all bounded copying.
def freeze (workspace : Option ByteArray) (stdin : Stdin) (limits : Limits) :
    Program (Result Frozen) :=
  if !limits.supported then pure (.error "snapshot limits exceed supported bounds")
  else (copyWorkspace workspace limits).bind fun copied =>
    match copied with
    | .error error => pure (.error error)
    | .ok state => (copyStdin stdin limits.stdinBytes).bind fun input =>
      match input with
      | .error error => pure (.error error)
      | .ok input =>
        let tree := workspace.map (fun _ => state.tree)
        (identify tree).bind fun treeHash =>
          match treeHash with
          | .error error => pure (.error error)
          | .ok treeDigest =>
            (identify input).bind fun inputHash =>
              match inputHash with
              | .error error => pure (.error error)
              | .ok stdinDigest =>
                let blobs := includeStdin state.blobs input stdinDigest
                pure (blobs.map (fun blobs => ⟨tree, input, treeDigest, stdinDigest,
                  state.entries, blobs, state.count, state.total⟩))

end LeanCage.Host.Snapshot
