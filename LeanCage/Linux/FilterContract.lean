namespace LeanCage.Linux.Filter

-- §FS-filter-loading.input.abi: Input metadata is distinct from runtime ABI evidence.
inductive ByteOrder where
  | littleEndian
  | bigEndian
  deriving DecidableEq, Repr

structure Abi where
  auditArch : UInt32
  pointerBits : UInt8
  longBits : UInt8
  byteOrder : ByteOrder
  deriving DecidableEq, Repr

-- §FS-filter-loading.input.abi: Only native little-endian x86-64 LP64 is supported.
def nativeAbi : Abi := ⟨0xc000003e, 64, 64, .littleEndian⟩

-- §FS-filter-loading.input.layout: Fixed-width fields do not promise native struct layout.
structure Instruction where
  code : UInt16
  jt : UInt8
  jf : UInt8
  k : UInt32
  deriving DecidableEq, Repr

-- §FS-filter-loading.input.layout: Natural-number bounds must precede machine conversions.
def instructionBytes : Nat := 8
def maxInstructions : Nat := 4096
def maxInputBytes : Nat := maxInstructions * instructionBytes
def sockFprogMaxLength : Nat := 65535
def profileInstructionCount : Nat := 9
def profileByteCount : Nat := profileInstructionCount * instructionBytes

-- §FS-filter-loading.input.subset: A tag names the reference form, not validation evidence.
inductive Program where
  | denyGetppid
  deriving DecidableEq, Repr

-- §FS-filter-loading.input.subset: Exactly one canonical nine-instruction program.
def Program.instructions : Program → Array Instruction
  | .denyGetppid => #[
      ⟨0x0020, 0, 0, 0x00000004⟩,
      ⟨0x0015, 1, 0, 0xc000003e⟩,
      ⟨0x0006, 0, 0, 0x80000000⟩,
      ⟨0x0020, 0, 0, 0x00000000⟩,
      ⟨0x0035, 0, 1, 0x40000000⟩,
      ⟨0x0006, 0, 0, 0x80000000⟩,
      ⟨0x0015, 0, 1, 0x0000006e⟩,
      ⟨0x0006, 0, 0, 0x00050001⟩,
      ⟨0x0006, 0, 0, 0x7fff0000⟩
    ]

-- §FS-filter-loading.input.errors: Preserve the rejected descriptor/count/first index.
inductive DecodeError where
  | unsupportedAbi (abi : Abi)
  | emptyInput
  | oversizedInput (byteCount : Nat)
  | misalignedInput (byteCount : Nat)
  | unsupportedLength (instructionCount : Nat)
  | unsupportedInstruction (index : Nat)
  deriving DecidableEq, Repr

-- §FS-filter-loading.input.errors: Pure decoder interface; validation evidence needs a theorem.
abbrev Decoder := Abi → ByteArray → Except DecodeError Program

end LeanCage.Linux.Filter
