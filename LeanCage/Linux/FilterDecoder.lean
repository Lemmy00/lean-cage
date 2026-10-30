import LeanCage.Linux.FilterContract
import Std.Tactic

namespace LeanCage.Linux.Filter

-- §FS-filter-loading.input.layout: Prove the sum fits before constructing a machine word.
def decodeU16LE (b0 b1 : UInt8) : UInt16 :=
  UInt16.ofNatLT (b0.toNat + 256 * b1.toNat) (by
    have h0 := b0.toNat_lt_size
    have h1 := b1.toNat_lt_size
    change _ < 65536
    change _ < 256 at h0 h1
    omega)

-- §FS-filter-loading.input.layout: All four byte values contribute without truncation.
def decodeU32LE (b0 b1 b2 b3 : UInt8) : UInt32 :=
  UInt32.ofNatLT (b0.toNat + 256 * b1.toNat + 65536 * b2.toNat +
    16777216 * b3.toNat) (by
    have h0 := b0.toNat_lt_size
    have h1 := b1.toNat_lt_size
    have h2 := b2.toNat_lt_size
    have h3 := b3.toNat_lt_size
    change _ < 4294967296
    change _ < 256 at h0 h1 h2 h3
    omega)

-- §FS-filter-loading.input.layout: Every byte read requires a proof of its actual bound.
def readInstruction (bytes : ByteArray) (base : Nat) (h : base + 8 ≤ bytes.size) :
    Instruction :=
  ⟨decodeU16LE (bytes[base]'(by omega)) (bytes[base + 1]'(by omega)),
   bytes[base + 2]'(by omega), bytes[base + 3]'(by omega),
   decodeU32LE (bytes[base + 4]'(by omega)) (bytes[base + 5]'(by omega))
     (bytes[base + 6]'(by omega)) (bytes[base + 7]'(by omega))⟩

-- §FS-filter-loading.input.subset: The index is bounded independently of untrusted input.
def referenceInstruction (i : Fin profileInstructionCount) : Instruction :=
  Program.denyGetppid.instructions[i.val]'i.isLt

-- §FS-filter-loading.input.layout: Size validation discharges all instruction-read bounds.
def instructionAt (bytes : ByteArray) (hsize : bytes.size = profileByteCount)
    (i : Fin profileInstructionCount) : Instruction :=
  readInstruction bytes (8 * i.val) (by
    have hi := i.isLt
    change i.val < 9 at hi
    change bytes.size = 72 at hsize
    omega)

-- §FS-filter-loading.input.errors: Increasing indices make find? report the first difference.
def firstMismatch (bytes : ByteArray) (hsize : bytes.size = profileByteCount) :
    Option (Fin profileInstructionCount) :=
  (List.finRange profileInstructionCount).find? fun i =>
    decide (instructionAt bytes hsize i ≠ referenceInstruction i)

-- §FS-filter-loading.input.errors: Only the all-matching result produces the supported tag.
def decodeValidatedSize (bytes : ByteArray) (hsize : bytes.size = profileByteCount) :
    Except DecodeError Program :=
  match firstMismatch bytes hsize with
  | none => .ok .denyGetppid
  | some i => .error (.unsupportedInstruction i.val)

-- §FS-filter-loading.input.errors: Validate in the specified order before any byte reads.
def decode : Decoder := fun abi bytes =>
  if abi = nativeAbi then
    if bytes.size = 0 then
      .error .emptyInput
    else if maxInputBytes < bytes.size then
      .error (.oversizedInput bytes.size)
    else if hmod : bytes.size % instructionBytes ≠ 0 then
      .error (.misalignedInput bytes.size)
    else if hcount : bytes.size / instructionBytes ≠ profileInstructionCount then
      .error (.unsupportedLength (bytes.size / instructionBytes))
    else
      decodeValidatedSize bytes (by
        simp only [instructionBytes, profileInstructionCount] at hmod hcount
        change bytes.size = 72
        omega)
  else
    .error (.unsupportedAbi abi)

end LeanCage.Linux.Filter
