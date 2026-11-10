import LeanCageHost.Policy

namespace LeanCage.Host.Image
open Filesystem

structure Entry where
  name : String
  mode : Nat
  bytes : ByteArray

def requestConfig (request bundle : String) (preflight : Bool)
    (limits : Transport.Limits) (fault : Nat) : ByteArray :=
  "LCREQ1\x00\x00".toUTF8 ++ request.toUTF8 ++ bundle.toUTF8 ++
    littleEndian 4 (if preflight then 1 else 2) ++
    littleEndian 8 limits.stdoutMax ++ littleEndian 8 limits.stderrMax ++
    littleEndian 8 limits.workspaceMax ++ littleEndian 8 limits.inodesMax ++
    littleEndian 4 fault ++ littleEndian 8 0

-- §FS-host-boundary.snapshot: The per-request overlay uses only bound fields and frozen bytes.
def entries (request bundle : String) (preflight : Bool) (fault : Nat)
    (policy : Policy.Accepted) (frozen : Snapshot.Frozen) : List Entry :=
  [⟨"request", 16832, .empty⟩, ⟨"m3-inputs/trees", 16832, .empty⟩,
    ⟨"m3-inputs/blobs", 16832, .empty⟩, ⟨"request/policy.json", 33024, policy.raw⟩,
    ⟨"request/config", 33024, requestConfig request bundle preflight policy.transport fault⟩] ++
    (match frozen.tree, frozen.treeDigest with
    | some tree, some digest => [⟨"m3-inputs/trees/" ++ Snapshot.hex digest, 33024, tree⟩]
    | _, _ => []) ++
    ((frozen.blobs.mergeSort (fun a b => Snapshot.hex a.digest ≤ Snapshot.hex b.digest)).map
      (fun blob => ⟨"m3-inputs/blobs/" ++ Snapshot.hex blob.digest, 33024, blob.bytes⟩))

def hex8 (value : Nat) : String :=
  String.ofList ((List.range 8).reverse.map (fun position =>
    Snapshot.hexChar ((value / 16 ^ position) % 16)))

def zeros (count : Nat) : ByteArray := ByteArray.mk (Array.replicate count 0)

def pad4 (count : Nat) : ByteArray := zeros ((4 - count % 4) % 4)

def header (inode : Nat) (entry : Entry) : ByteArray :=
  let fields := [inode, entry.mode, 0, 0, 1, 0, entry.bytes.size, 0, 0, 0, 0,
    entry.name.toUTF8.size + 1, 0]
  "070701".toUTF8 ++ (String.join (fields.map hex8)).toUTF8 ++ entry.name.toUTF8 ++
    zeros 1 ++ pad4 (110 + entry.name.toUTF8.size + 1)

def Entry.valid (entry : Entry) : Bool :=
  Validation.canonicalName entry.name && entry.name.toUTF8.size ≤ 4095 &&
    entry.bytes.size ≤ workspaceMax && (entry.mode == 16832 || entry.mode == 33024)

def overlayValid (entries : List Entry) : Bool :=
  entries.length ≤ inodeMax + 8 && entries.all Entry.valid &&
    entries.foldl (fun total entry => total + entry.bytes.size) 0 ≤
      workspaceMax + stdinMax + treeMax + reportMax + 256 &&
    (entries.foldl (fun (state : Bool × Std.TreeSet String compare) entry =>
      (state.1 && !state.2.contains entry.name, state.2.insert entry.name)) (true, ∅)).1

def writeEntries : Nat → UInt64 → List Entry → Filesystem.Program (Result Unit)
  | _, _, [] => pure (.ok ())
  | inode, fd, entry :: rest => do
    let encodedHeader := header inode entry
    let written ← writeLoop (encodedHeader.size + 1) fd encodedHeader 0
    if let .error error := written then return .error error
    let written ← writeLoop (entry.bytes.size + 1) fd entry.bytes 0
    if let .error error := written then return .error error
    let padding := pad4 entry.bytes.size
    let written ← writeLoop (padding.size + 1) fd padding 0
    if let .error error := written then return .error error
    writeEntries (inode + 1) fd rest

def content (fd : UInt64) (base : ByteArray) (overlay : List Entry) :
    Filesystem.Program (Result Unit) := do
  let written ← writeLoop (base.size + 1) fd base 0
  if let .error error := written then return .error error
  let padding := pad4 base.size
  let written ← writeLoop (padding.size + 1) fd padding 0
  if let .error error := written then return .error error
  writeEntries 1 fd (overlay ++ [⟨"TRAILER!!!", 0, .empty⟩])

-- §FS-host-boundary.ownership: The only output open is exclusive and relative to the fresh run.
def create (run : UInt64) (bundle : Validation.Bundle) (overlay : List Entry) :
    Filesystem.Program (Result Unit) := do
  if !overlayValid overlay then return .error "request archive exceeds supported bounds"
  let base ← Validation.copyIdentified bundle "profile/runtime.cpio.gz" workspaceMax
  match base with
  | .error error => return .error error
  | .ok base =>
    let opened ← Filesystem.Program.effect {
      op := .openAt
      first := run
      second := newFileFlags
      third := 384
      left := "request.cpio".toUTF8 }
    match descriptor opened with
    | none => return .error (failure "request archive openat" opened)
    | some fd => (content fd base overlay).bind (closeResult fd)

end LeanCage.Host.Image
