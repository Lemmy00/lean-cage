import LeanCageHost.Publication.Types

namespace LeanCage.Host.Publication
open Filesystem

def keyName : String := ".leancage-private-host/publication.key"

-- §FS-host-boundary.publication: The host-only bootstrap key never enters the request image.
def authenticationKey (bundle : Validation.Bundle) : Filesystem.Program (Result ByteArray) := do
  let some files := Validation.bundleFiles bundle.manifest
    | return .error "missing host authentication inventory"
  let some (_, .string expected) := files.find? (fun field => field.1 == keyName)
    | return .error "host publication key is not identified"
  let uid ← Filesystem.Program.effect { op := .euid }
  if nativeError uid || !uid.2.isEmpty then return .error (failure "host key identity" uid)
  let opened ← Filesystem.Program.effect {
    op := .openAt, first := cwd, second := readFlags, left := (bundle.root ++ "/" ++ keyName).toUTF8 }
  let some fd := descriptor opened | return .error (failure "publication key openat" opened)
  let privateReply ← Filesystem.Program.effect {
    op := .getAttribute, first := fd, second := 1, left := PrivateNames.attributeName }
  if privateReply.1 != 1 || privateReply.2 != PrivateNames.attributeValue then
    return ← closeResult fd (.error "publication key is not marked private")
  let copied ← (copyOpened fd 32).bind (closeResult fd)
  match copied with
  | .error error => return .error error
  | .ok copied =>
    if copied.bytes.size != 32 || copied.stat.uid != uid.1.toNat ||
        (copied.stat.mode &&& 511) != 256 then return .error "host publication key is not private"
    let identified ← Filesystem.hash copied.bytes
    match identified with
    | .error error => return .error error
    | .ok digest =>
      if Snapshot.hex digest != expected then return .error "host publication key identity differs"
      return .ok copied.bytes

def authenticate (bundle : Validation.Bundle) (wire : ByteArray) :
    Filesystem.Program (Result ByteArray) := do
  if wire.size > metadataMax then return .error "authentication input exceeds its bound"
  let key ← authenticationKey bundle
  match key with
  | .error error => return .error error
  | .ok key =>
    let reply ← Filesystem.Program.effect { op := .authenticate, left := wire, right := key }
    if reply.1 == 0 && reply.2.size == 32 then return .ok reply.2
    return .error (failure "publication authentication" reply)

-- §FS-host-boundary.publication: Compare tags through the fixed runtime crypto operation.
def verify (bundle : Validation.Bundle) (wire supplied : ByteArray) :
    Filesystem.Program (Result Unit) := do
  if supplied.size != markerMagic.size + 32 then return .error "invalid publication marker size"
  let expected ← authenticate bundle wire
  match expected with
  | .error error => return .error error
  | .ok expected =>
    let compared ← Filesystem.Program.effect {
      op := .equalSecret, left := marker expected, right := supplied }
    if compared.1 == 1 && compared.2.isEmpty then return .ok ()
    if nativeError compared then return .error (failure "publication tag comparison" compared)
    return .error "publication authentication differs"

end LeanCage.Host.Publication
