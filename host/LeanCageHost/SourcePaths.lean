import LeanCageHost.Files
import LeanCageHost.PrivateNames

namespace LeanCage.Host.SourcePaths
open Filesystem

def absolute (path : ByteArray) : Program (Result ByteArray) := do
  if path.isEmpty || !rawPathValid path then return .error "invalid caller path"
  if path[0]! == 47 then return .ok path
  let current ← Program.effect { op := .workingDirectory }
  if current.1 != 0 || current.2.isEmpty || !rawPathValid current.2 || current.2[0]! != 47 then
    return .error (failure "working directory" current)
  let path := current.2 ++ "/".toUTF8 ++ path
  if !rawPathValid path then return .error "absolute caller path exceeds its bound"
  return .ok path

def components (path : ByteArray) : Result (List ByteArray) := do
  if path.isEmpty || !rawPathValid path then
    throw ("caller path is not a bounded path" : Failure)
  let parts := (path.data.toList.splitOn 47).filter (fun part => !part.isEmpty)
  let parts := parts.map (fun part => ByteArray.mk part.toArray)
  if !parts.all (fun part => part.size ≤ 255 && !PrivateNames.reservedBytes part) then
    throw ("caller path enters reserved private state" : Failure)
  return parts

-- §FS-host-boundary.ownership: Private anchor attributes also deny alternate ancestor spellings.
def publicHandle (fd : UInt64) : Program (Result UInt64) :=
  .call { op := .getAttribute, first := fd, second := 1, left := PrivateNames.attributeName } fun reply =>
    if nativeError reply && errorNumber reply == 61 then
      pure (.ok fd)
    else closeResult fd (.error "caller path enters private application state")

def openAt (parent : UInt64) (name : ByteArray) (directory : Bool) :
    Program (Result UInt64) :=
  .call {
    op := .openAt
    first := parent
    second := if directory then directoryFlags else readFlags
    left := name } fun reply =>
    match descriptor reply with
    | none => pure (.error (failure "caller path openat" reply))
    | some fd => publicHandle fd

def releaseParent (parent : UInt64) (child : Result UInt64) : Program (Result UInt64) := do
  let released ← closeResult parent child
  match released with
  | .ok value => return .ok value
  | .error error =>
    match child with
    | .error _ => return .error error
    | .ok fd => closeResult fd (.error error)

-- §FS-host-boundary.ownership: Every ancestor is retained and opened without following links.
def walk : UInt64 → List ByteArray → Bool → Program (Result UInt64)
  | parent, [], _ => pure (.ok parent)
  | parent, name :: rest, directory => do
    let opened ← openAt parent name (directory || !rest.isEmpty)
    let released ← releaseParent parent opened
    match released with
    | .error error => return .error error
    | .ok child => walk child rest directory

-- §FS-host-boundary.ownership: Compare real directory identities including mount identity.
def identity (fd : UInt64) : Program (Result ByteArray) :=
  .call { op := .directoryIdentity, first := fd } fun reply =>
    if reply.1 == 0 && reply.2.size == 24 then pure (.ok reply.2)
    else pure (.error (failure "directory identity" reply))

-- §FS-host-boundary.ownership: Audit a duplicate; the caller's selected directory stays retained.
def ancestry : Nat → UInt64 → ByteArray → Program (Result Unit)
  | 0, current, _ => closeResult current (.error "working directory ancestry exceeds its bound")
  | fuel + 1, current, rootIdentity => do
    let observed ← identity current
    match observed with
    | .error error => closeResult current (.error error)
    | .ok observed =>
      if observed == rootIdentity then closeResult current (.ok ())
      else
        let parent ← openAt current "..".toUTF8 true
        let released ← releaseParent current parent
        match released with
        | .error error => return .error error
        | .ok parent => ancestry fuel parent rootIdentity

def checkAncestry (base : UInt64) : Program (Result Unit) := do
  let root ← openAt cwd "/".toUTF8 true
  match root with
  | .error error => return .error error
  | .ok root =>
    let observed ← (identity root).bind (closeResult root)
    match observed with
    | .error error => return .error error
    | .ok rootIdentity =>
      let duplicate ← openAt base ".".toUTF8 true
      match duplicate with
      | .error error => return .error error
      | .ok duplicate => ancestry 4096 duplicate rootIdentity

structure Started where
  base : UInt64
  parts : List ByteArray

-- §FS-host-boundary.ownership: getcwd checks a spelling; it never selects a relative input.
def currentSpelling (reply : Reply) : Result Unit := do
  if reply.1 != 0 || reply.2.isEmpty || reply.2[0]! != 47 then
    throw (failure "working directory" reply)
  let _ ← components reply.2
  return ()

def start (path : ByteArray) : Program (Result Started) :=
  match components path with
  | .error error => pure (.error error)
  | .ok parts => do
    if path[0]! == 47 then
      let root ← openAt cwd "/".toUTF8 true
      return root.map (fun base => ⟨base, parts⟩)
    else
      let base ← openAt cwd ".".toUTF8 true
      match base with
      | .error error => return .error error
      | .ok base =>
        let spelling ← Program.effect { op := .workingDirectory }
        match currentSpelling spelling with
        | .error error => closeResult base (.error error)
        | .ok () =>
          let checked ← checkAncestry base
          match checked with
          | .error error => closeResult base (.error error)
          | .ok () => return .ok ⟨base, parts⟩

def «open» (path : ByteArray) (directory : Bool) : Program (Result UInt64) := do
  let selected ← start path
  match selected with
  | .error error => return .error error
  | .ok selected => walk selected.base selected.parts directory

def copyFile (path : ByteArray) (limit : Nat) : Program (Result CopiedFile) := do
  let opened ← «open» path false
  match opened with
  | .error error => return .error error
  | .ok fd => (copyOpened fd limit).bind (closeResult fd)

end LeanCage.Host.SourcePaths
