import LeanCageHost.Files
import LeanCageHost.Snapshot
import LeanCageHost.SourcePaths

namespace LeanCage.Host.Directories
open Filesystem

structure Opened where
  fd : UInt64
  information : Stat

def component (bytes : ByteArray) : Bool :=
  !bytes.isEmpty && bytes.size ≤ 255 && !bytes.data.contains 0 && !bytes.data.contains 47

def components (path : ByteArray) : Except String (Bool × List ByteArray) := do
  if path.isEmpty || !rawPathValid path then throw "invalid host destination path"
  let absolute := path[0]! == 47
  let parts := path.data.toList.splitOn 47
  let parts := parts.filter (fun part => !part.isEmpty)
  if parts.isEmpty then throw "host destination requires a final component"
  let parts := parts.map (fun part => ByteArray.mk part.toArray)
  if !parts.all (fun part => component part && !PrivateNames.reservedBytes part) then
    throw "unsupported or reserved host path component"
  return (absolute, parts)

-- §FS-host-boundary.ownership: Check shared-parent access before using it.
def trusted (uid : Nat) (information : Stat) : Bool :=
  information.directory && (information.uid == uid || information.uid == 0) &&
    ((information.mode &&& 18) == 0 ||
      (information.uid == 0 && (information.mode &&& 512) != 0))

def inspect (uid : Nat) (fd : UInt64) : Program (Result Opened) :=
  .call { op := .stat, first := fd } fun reply =>
    match parseStat reply with
    | none => closeResult fd (.error (failure "directory fstat" reply))
    | some information =>
      if trusted uid information then pure (.ok ⟨fd, information⟩)
      else closeResult fd (.error "host directory does not satisfy the supported parent authority")

def openAt (uid : Nat) (parent : UInt64) (name : ByteArray) : Program (Result Opened) :=
  .call { op := .openAt, first := parent, second := directoryFlags, left := name } fun reply =>
    match descriptor reply with
    | none => pure (.error (failure "directory openat" reply))
    | some fd => inspect uid fd

def ensureAt (uid : Nat) (parent : UInt64) (name : ByteArray) : Program (Result Opened) := do
  let made ← Program.effect { op := .mkdirAt, first := parent, second := 448, left := name }
  if made.1 == 0 && made.2.isEmpty then openAt uid parent name
  else if nativeError made && errorNumber made == 17 then openAt uid parent name
  else pure (.error (failure "parent mkdirat" made))

def publicAt (uid : Nat) (parent : UInt64) (name : ByteArray) (create : Bool) :
    Program (Result Opened) := do
  let opened ← if create then ensureAt uid parent name else openAt uid parent name
  match opened with
  | .error error => return .error error
  | .ok opened =>
    let allowed ← SourcePaths.publicHandle opened.fd
    return allowed.map (fun fd => { opened with fd })

-- §FS-host-boundary.ownership: Retain each next directory before releasing the actual previous one.
def descend : Nat → Bool → Opened → List ByteArray → Program (Result Opened)
  | _, _, current, [] => pure (.ok current)
  | uid, create, current, name :: rest => do
    let next ← publicAt uid current.fd name create
    let closed ← closeResult current.fd next
    match closed with
    | .error error =>
      match next with
      | .ok next => closeResult next.fd (.error error)
      | .error _ => pure (.error error)
    | .ok next => descend uid create next rest

structure Parent where
  directory : Opened
  name : ByteArray
  uid : Nat

def parent (path : ByteArray) (create : Bool) : Program (Result Parent) := do
  let selected ← SourcePaths.start path
  match selected with
  | .error error => return .error error
  | .ok selected =>
    let some name := selected.parts.getLast?
      | closeResult selected.base (.error "missing host destination name")
    if name == ".".toUTF8 || name == "..".toUTF8 then
      return ← closeResult selected.base (.error "host destination requires a fresh final name")
    let identity ← Program.effect { op := .euid }
    if nativeError identity || !identity.2.isEmpty || identity.1.toNat > 2 ^ 32 - 1 then
      return ← closeResult selected.base (.error (failure "host identity" identity))
    let uid := identity.1.toNat
    let base ← inspect uid selected.base
    match base with
    | .error error => return .error error
    | .ok base =>
      let result ← descend uid create base selected.parts.dropLast
      return result.map (fun directory => ⟨directory, name, uid⟩)

def randomBytes : Nat → Nat → ByteArray → Program (Result ByteArray)
  | 0, _, _ => pure (.error "host randomness made no bounded progress")
  | fuel + 1, count, bytes =>
    if bytes.size > count then pure (.error "invalid host random prefix")
    else if bytes.size == count then pure (.ok bytes)
    else .call { op := .random, first := (count - bytes.size).toUInt64 } fun reply =>
      if nativeError reply then pure (.error (failure "getrandom" reply))
      else if reply.1.toNat != reply.2.size || reply.2.isEmpty || reply.2.size > count - bytes.size then
        pure (.error "host randomness returned invalid progress")
      else randomBytes fuel count (bytes ++ reply.2)

structure NewDirectory where
  directory : Opened
  name : ByteArray

-- §FS-host-boundary.ownership: A successful exclusive creation establishes actual freshness.
def newChild (uid : Nat) (parent : UInt64) (prefixName : String) : Program (Result NewDirectory) := do
  let random ← randomBytes 17 16 .empty
  match random with
  | .error error => return .error error
  | .ok bytes =>
    let name := (prefixName ++ Snapshot.hex bytes).toUTF8
    if !component name then return .error "invalid private child component"
    let made ← Program.effect {
      op := .mkdirAt, first := parent, second := 448, left := name }
    if made.1 != 0 || !made.2.isEmpty then return .error (failure "fresh stage mkdirat" made)
    let opened ← openAt uid parent name
    match opened with
    | .error error => return .error error
    | .ok directory =>
      if directory.information.uid != uid || (directory.information.mode &&& 511) != 448 then
        closeResult directory.fd (.error "fresh stage authority differs")
      else return .ok ⟨directory, name⟩

structure Fresh extends NewDirectory where
  container : Opened

def fresh (parent : Parent) : Program (Result Fresh) := do
  let container ← openAt parent.uid parent.directory.fd ".".toUTF8
  match container with
  | .error error => return .error error
  | .ok container =>
    let child ← newChild parent.uid container.fd PrivateNames.prefixText
    match child with
    | .error error => closeResult container.fd (.error error)
    | .ok child => return .ok ⟨child, container⟩

def temporaryParent : Program (Result (Opened × String × Nat)) := do
  let uid ← Program.effect { op := .euid }
  if nativeError uid || !uid.2.isEmpty || uid.1.toNat > 2 ^ 32 - 1 then
    return .error (failure "temporary anchor identity" uid)
  let root ← openAt uid.1.toNat cwd "/tmp".toUTF8
  match root with
  | .error error => return .error error
  | .ok root => return .ok (root, "/tmp", uid.1.toNat)

end LeanCage.Host.Directories
