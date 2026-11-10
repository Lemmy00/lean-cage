import LeanCageHost.Effects

namespace LeanCage.Host.Filesystem

structure Failure where
  message : String
  errno : Option Nat := none
  deriving DecidableEq, Repr

instance : Coe String Failure := ⟨fun message => ⟨message, none⟩⟩
instance : ToString Failure := ⟨Failure.message⟩

abbrev Result (α : Type) := Except Failure α

structure Stat where
  device : Nat
  inode : Nat
  mode : Nat
  links : Nat
  uid : Nat
  gid : Nat
  size : Nat
  modified : Nat
  modifiedNanos : Nat
  changed : Nat
  changedNanos : Nat
  deriving DecidableEq, BEq

def Stat.regular (stat : Stat) : Bool := stat.mode &&& 61440 == 32768
def Stat.directory (stat : Stat) : Bool := stat.mode &&& 61440 == 16384

def parseStat (reply : Reply) : Option Stat :=
  if reply.1 != 0 || reply.2.size != 88 then none
  else
    let word := fun index => fromLittleEndian (reply.2.extract (8 * index) (8 * (index + 1)))
    some ⟨word 0, word 1, word 2, word 3, word 4, word 5, word 6,
      word 7, word 8, word 9, word 10⟩

def descriptor (reply : Reply) : Option UInt64 :=
  if nativeError reply || !reply.2.isEmpty || reply.1.toNat > 2147483647 then none
  else some reply.1

def failure (operation : String) (reply : Reply) : Failure :=
  if nativeError reply then
    ⟨s!"host {operation} failed (errno {errorNumber reply})", some (errorNumber reply)⟩
  else ⟨s!"host {operation} returned an invalid reply", none⟩

-- §FS-host-boundary.snapshot: Bound each actual read and check bytes before retaining them.
def readLoop : Nat → UInt64 → Nat → ByteArray → Program (Result ByteArray)
  | 0, _, _, _ => pure (.error "host read made no bounded progress")
  | fuel + 1, fd, limit, bytes =>
    if bytes.size > limit || bytes.size ≥ 2 ^ 63 then pure (.error "host input byte bound exceeded")
    else
      let requested := min chunkMax (limit + 1 - bytes.size)
      .call { op := .read, first := fd, second := requested.toUInt64, third := (bytes.size + 1).toUInt64 } fun reply =>
        if nativeError reply then pure (.error (failure "read" reply))
        else if reply.1.toNat != reply.2.size || reply.2.size > requested then
          pure (.error "host read returned invalid bytes")
        else if reply.2.isEmpty then pure (.ok bytes)
        else if bytes.size + reply.2.size > limit then pure (.error "host input byte bound exceeded")
        else readLoop fuel fd limit (bytes ++ reply.2)

def closeResult {α : Type} (fd : UInt64) (result : Result α) : Program (Result α) :=
  .call { op := .close, first := fd } fun reply =>
    match result with
    | .error error => pure (.error error)
    | .ok value =>
      if reply.1 == 0 && reply.2.isEmpty then pure (.ok value)
      else pure (.error (failure "close" reply))

structure CopiedFile where
  bytes : ByteArray
  stat : Stat

-- §FS-host-boundary.snapshot: The before/after checks detect observations, not an atomic view.
def copyOpened (fd : UInt64) (limit : Nat) : Program (Result CopiedFile) :=
  .call { op := .stat, first := fd } fun reply =>
    match parseStat reply with
    | none => pure (.error (failure "fstat" reply))
    | some before =>
      if !before.regular || before.links != 1 || before.size > limit then
        pure (.error "host input is not a bounded singly linked regular file")
      else (readLoop (limit + 1) fd limit .empty).bind fun result =>
        match result with
        | .error error => pure (.error error)
        | .ok bytes =>
          .call { op := .stat, first := fd } fun finalReply =>
            match parseStat finalReply with
            | none => pure (.error (failure "fstat" finalReply))
            | some after =>
              if after != before || bytes.size != before.size then
                pure (.error "host input changed during bounded copy")
              else pure (.ok ⟨bytes, before⟩)

def copyAt (parent : UInt64) (path : ByteArray) (limit : Nat) : Program (Result CopiedFile) :=
  if !rawPathValid path then pure (.error "invalid host input path")
  else .call { op := .openAt, first := parent, second := readFlags, left := path } fun reply =>
    match descriptor reply with
    | none => pure (.error (failure "openat" reply))
    | some fd => (copyOpened fd limit).bind (closeResult fd)

def readBounded (path : ByteArray) (limit : Nat) : Program (Result ByteArray) := do
  let result ← copyAt cwd path limit
  return result.map (·.bytes)

-- §FS-host-boundary.publication: Partial writes advance by the acknowledged count only.
def writeLoop : Nat → UInt64 → ByteArray → Nat → Program (Result Unit)
  | 0, _, _, _ => pure (.error "host write made no bounded progress")
  | fuel + 1, fd, bytes, offset =>
    if offset ≥ bytes.size then pure (.ok ())
    else
      let part := bytes.extract offset (min bytes.size (offset + chunkMax))
      .call { op := .write, first := fd, left := part } fun reply =>
        if nativeError reply then pure (.error (failure "write" reply))
        else if !reply.2.isEmpty || reply.1 == 0 || reply.1.toNat > part.size then
          pure (.error "host write returned invalid progress")
        else writeLoop fuel fd bytes (offset + reply.1.toNat)

def writeNew (parent : UInt64) (name bytes : ByteArray) (mode : UInt64 := 384) :
    Program (Result Unit) :=
  if !rawPathValid name then pure (.error "invalid host output path")
  else .call { op := .openAt, first := parent, second := newFileFlags, third := mode, left := name } fun reply =>
    match descriptor reply with
    | none => pure (.error (failure "exclusive openat" reply))
    | some fd => (writeLoop (bytes.size + 1) fd bytes 0).bind (closeResult fd)

def hash (bytes : ByteArray) : Program (Result ByteArray) :=
  .call { op := .sha256, left := bytes } fun reply =>
    if reply.1 == 0 && reply.2.size == 32 then pure (.ok reply.2)
    else pure (.error (failure "sha256" reply))

end LeanCage.Host.Filesystem
