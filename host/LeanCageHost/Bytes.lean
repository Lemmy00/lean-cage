namespace LeanCage.Host

-- §FS-host-boundary.transport: All native lengths narrow only after the stated byte bound.
def chunkMax : Nat := 65536
def reportMax : Nat := 65536
def treeMax : Nat := 4 * 1024 * 1024
def manifestMax : Nat := 16 * 1024 * 1024
def workspaceMax : Nat := 256 * 1024 * 1024
def stdinMax : Nat := 64 * 1024 * 1024
def captureMax : Nat := 16 * 1024 * 1024
def inodeMax : Nat := 65536

-- §FS-host-boundary.transport: Canonical fixed-width little-endian bytes retain every bit.
def littleEndian (width value : Nat) : ByteArray :=
  ⟨((List.range width).map (fun index => UInt8.ofNat (value / 256 ^ index))).toArray⟩

def fromLittleEndian (bytes : ByteArray) : Nat :=
  bytes.data.toList.foldr (fun byte value => byte.toNat + 256 * value) 0

end LeanCage.Host
