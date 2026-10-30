import LeanCage.Linux.FilterDecoder

namespace LeanCage.Linux.Filter

-- §FS-filter-loading.input.correctness: The statement uses byte equations, not the decoder.
def InstructionLayout (bytes : ByteArray) (base : Nat) (instruction : Instruction) : Prop :=
  ∃ h : base + 8 ≤ bytes.size,
    instruction.code.toNat = (bytes[base]'(by omega)).toNat +
      256 * (bytes[base + 1]'(by omega)).toNat ∧
    instruction.jt = bytes[base + 2]'(by omega) ∧
    instruction.jf = bytes[base + 3]'(by omega) ∧
    instruction.k.toNat = (bytes[base + 4]'(by omega)).toNat +
      256 * (bytes[base + 5]'(by omega)).toNat +
      65536 * (bytes[base + 6]'(by omega)).toNat +
      16777216 * (bytes[base + 7]'(by omega)).toNat

-- §FS-filter-loading.input.correctness: Exact byte layout and ABI describe accepted inputs.
def ValidInput (abi : Abi) (bytes : ByteArray) : Prop :=
  abi = nativeAbi ∧ bytes.size = profileByteCount ∧
    ∀ i : Fin profileInstructionCount,
      InstructionLayout bytes (8 * i.val) (referenceInstruction i)

-- §FS-filter-loading.input.layout: General word reconstruction is exact for every byte pair.
theorem decodeU16LE_toNat (b0 b1 : UInt8) :
    (decodeU16LE b0 b1).toNat = b0.toNat + 256 * b1.toNat := by
  simp only [decodeU16LE, UInt16.toNat_ofNatLT]

-- §FS-filter-loading.input.layout: General four-byte reconstruction preserves all 32 bits.
theorem decodeU32LE_toNat (b0 b1 b2 b3 : UInt8) :
    (decodeU32LE b0 b1 b2 b3).toNat =
      b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat := by
  simp only [decodeU32LE, UInt32.toNat_ofNatLT]

-- §FS-filter-loading.input.correctness: Instruction equality is exactly the specified layout.
theorem readInstruction_eq_iff (bytes : ByteArray) (base : Nat)
    (h : base + 8 ≤ bytes.size) (instruction : Instruction) :
    readInstruction bytes base h = instruction ↔ InstructionLayout bytes base instruction := by
  constructor
  · intro heq
    subst instruction
    exact ⟨h, decodeU16LE_toNat _ _, rfl, rfl, decodeU32LE_toNat _ _ _ _⟩
  · rintro ⟨_, hcode, hjt, hjf, hk⟩
    cases instruction with
    | mk code jt jf k =>
      simp only [readInstruction, Instruction.mk.injEq]
      exact ⟨UInt16.toNat.inj ((decodeU16LE_toNat _ _).trans hcode.symm),
        hjt.symm, hjf.symm, UInt32.toNat.inj ((decodeU32LE_toNat _ _ _ _).trans hk.symm)⟩

-- §FS-filter-loading.input.correctness: No mismatches means all mathematical layouts match.
theorem firstMismatch_eq_none_iff (bytes : ByteArray)
    (hsize : bytes.size = profileByteCount) :
    firstMismatch bytes hsize = none ↔
      ∀ i : Fin profileInstructionCount,
        InstructionLayout bytes (8 * i.val) (referenceInstruction i) := by
  simp only [firstMismatch, List.find?_eq_none, List.mem_finRange, forall_const,
    decide_eq_true_eq, Decidable.not_not]
  exact forall_congr' fun i => readInstruction_eq_iff bytes _ _ _

-- §FS-filter-loading.input.correctness: A reported mismatch is the first mathematical mismatch.
theorem firstMismatch_eq_some_iff (bytes : ByteArray)
    (hsize : bytes.size = profileByteCount) (i : Fin profileInstructionCount) :
    firstMismatch bytes hsize = some i ↔
      ¬ InstructionLayout bytes (8 * i.val) (referenceInstruction i) ∧
      ∀ j : Fin profileInstructionCount, j.val < i.val →
        InstructionLayout bytes (8 * j.val) (referenceInstruction j) := by
  constructor
  · intro hsome
    obtain ⟨hp, index, hindex, hget, hbefore⟩ := List.find?_eq_some_iff_getElem.mp hsome
    have hval : index = i.val := by simpa using congrArg Fin.val hget
    refine ⟨?_, ?_⟩
    · intro hlayout
      have heq : instructionAt bytes hsize i = referenceInstruction i :=
        (readInstruction_eq_iff bytes _ _ _).mpr hlayout
      exact (of_decide_eq_true hp) heq
    · intro j hj
      have hprevious := hbefore j.val (by omega)
      have heq : instructionAt bytes hsize j = referenceInstruction j := by
        simpa using hprevious
      exact (readInstruction_eq_iff bytes _ _ _).mp heq
  · rintro ⟨hbad, hbefore⟩
    apply List.find?_eq_some_iff_getElem.mpr
    refine ⟨?_, i.val, by simp, by simp, ?_⟩
    · simp only [decide_eq_true_eq]
      intro heq
      exact hbad ((readInstruction_eq_iff bytes _ _ _).mp heq)
    · intro index hindex
      have hbound : index < profileInstructionCount := Nat.lt_trans hindex i.isLt
      have heq : instructionAt bytes hsize ⟨index, hbound⟩ =
          referenceInstruction ⟨index, hbound⟩ :=
        (readInstruction_eq_iff bytes _ _ _).mpr (hbefore ⟨index, hbound⟩ hindex)
      simpa using heq

-- §FS-filter-loading.input.correctness: No assumptions about the input replace validation.
theorem decode_success {abi : Abi} {bytes : ByteArray} {program : Program}
    (h : decode abi bytes = .ok program) : ValidInput abi bytes := by
  unfold decode at h
  split at h
  next habi =>
    split at h
    next _ => cases h
    next _ =>
      split at h
      next _ => cases h
      next _ =>
        split at h
        next _ => cases h
        next hmod =>
          split at h
          next _ => cases h
          next hcount =>
            have hsize : bytes.size = profileByteCount := by
              simp only [instructionBytes, profileInstructionCount] at hmod hcount
              change bytes.size = 72
              omega
            change decodeValidatedSize bytes hsize = .ok program at h
            unfold decodeValidatedSize at h
            cases hfind : firstMismatch bytes hsize with
            | none =>
              exact ⟨habi, hsize, (firstMismatch_eq_none_iff bytes hsize).mp hfind⟩
            | some i => simp [hfind] at h
  next _ => cases h

-- §FS-filter-loading.input.correctness: Every specified input succeeds, without extra premises.
theorem decode_complete {abi : Abi} {bytes : ByteArray} (h : ValidInput abi bytes) :
    decode abi bytes = .ok .denyGetppid := by
  obtain ⟨habi, hsize, hfields⟩ := h
  have hfind := (firstMismatch_eq_none_iff bytes hsize).mpr hfields
  simp [decode, habi, hsize, profileByteCount, profileInstructionCount, instructionBytes,
    maxInputBytes, maxInstructions, decodeValidatedSize, hfind]

-- §FS-filter-loading.input.correctness: Full acceptance equivalence for every ABI and snapshot.
theorem decode_ok_iff (abi : Abi) (bytes : ByteArray) (program : Program) :
    decode abi bytes = .ok program ↔ ValidInput abi bytes := by
  cases program
  exact ⟨decode_success, decode_complete⟩

-- §FS-filter-loading.input.layout: Accepted indices and the 16-bit count cannot overflow.
theorem decode_bounds {abi : Abi} {bytes : ByteArray} {program : Program}
    (h : decode abi bytes = .ok program) :
    bytes.size = 72 ∧ bytes.size / 8 ≤ maxInstructions ∧
    bytes.size / 8 ≤ sockFprogMaxLength ∧
    (UInt16.ofNat (bytes.size / 8)).toNat = bytes.size / 8 ∧
    ∀ (index field : Nat), index < bytes.size / 8 → field < 8 →
      8 * index + field < bytes.size := by
  have hsize : bytes.size = 72 := (decode_success h).2.1
  refine ⟨hsize, ?_, ?_, ?_, ?_⟩
  · simp [hsize, maxInstructions]
  · simp [hsize, sockFprogMaxLength]
  · simp [hsize]
  · intro index field hi hf
    omega

-- §FS-filter-loading.input.errors: ABI rejection takes priority over every byte error.
theorem decode_unsupported_abi (abi : Abi) (bytes : ByteArray) (h : abi ≠ nativeAbi) :
    decode abi bytes = .error (.unsupportedAbi abi) := by
  simp [decode, h]

-- §FS-filter-loading.input.errors: Empty input is rejected before size/alignment checks.
theorem decode_empty (abi : Abi) (bytes : ByteArray)
    (habi : abi = nativeAbi) (hsize : bytes.size = 0) :
    decode abi bytes = .error .emptyInput := by
  simp [decode, habi, hsize]

-- §FS-filter-loading.input.errors: Oversize wins over any misalignment or wrong count.
theorem decode_oversized (abi : Abi) (bytes : ByteArray)
    (habi : abi = nativeAbi) (hsize : maxInputBytes < bytes.size) :
    decode abi bytes = .error (.oversizedInput bytes.size) := by
  have hnonempty : bytes.size ≠ 0 := by
    simp only [maxInputBytes, maxInstructions, instructionBytes] at hsize
    omega
  simp [decode, habi, hnonempty, hsize]

-- §FS-filter-loading.input.errors: Misalignment precedes the supported instruction count.
theorem decode_misaligned (abi : Abi) (bytes : ByteArray)
    (habi : abi = nativeAbi) (hnonempty : bytes.size ≠ 0)
    (hmax : bytes.size ≤ maxInputBytes) (hmod : bytes.size % instructionBytes ≠ 0) :
    decode abi bytes = .error (.misalignedInput bytes.size) := by
  have hnotmax : ¬ maxInputBytes < bytes.size := by omega
  simp [decode, habi, hnonempty, hnotmax, hmod]

-- §FS-filter-loading.input.errors: Reject an unsupported count without reading a field.
theorem decode_unsupported_length (abi : Abi) (bytes : ByteArray)
    (habi : abi = nativeAbi) (hnonempty : bytes.size ≠ 0)
    (hmax : bytes.size ≤ maxInputBytes) (hmod : bytes.size % instructionBytes = 0)
    (hcount : bytes.size / instructionBytes ≠ profileInstructionCount) :
    decode abi bytes = .error (.unsupportedLength (bytes.size / instructionBytes)) := by
  have hnotmax : ¬ maxInputBytes < bytes.size := by omega
  simp [decode, habi, hnonempty, hnotmax, hmod, hcount]

-- §FS-filter-loading.input.correctness: Invalid inputs return an error, never a program tag.
theorem decode_rejects_invalid (abi : Abi) (bytes : ByteArray) (h : ¬ ValidInput abi bytes) :
    ∃ error, decode abi bytes = .error error := by
  cases hresult : decode abi bytes with
  | error error => exact ⟨error, rfl⟩
  | ok program => exact False.elim (h (decode_success hresult))

-- §FS-filter-loading.input.errors: Proved size and ABI checks expose exactly the field check.
theorem decode_at_valid_size (abi : Abi) (bytes : ByteArray)
    (habi : abi = nativeAbi) (hsize : bytes.size = profileByteCount) :
    decode abi bytes = decodeValidatedSize bytes hsize := by
  simp [decode, habi, hsize, profileByteCount, profileInstructionCount, instructionBytes,
    maxInputBytes, maxInstructions]

-- §FS-filter-loading.input.correctness: The decoder reports exactly the earliest bad layout.
theorem decode_mismatch_iff (bytes : ByteArray) (hsize : bytes.size = profileByteCount)
    (i : Fin profileInstructionCount) :
    decode nativeAbi bytes = .error (.unsupportedInstruction i.val) ↔
      ¬ InstructionLayout bytes (8 * i.val) (referenceInstruction i) ∧
      ∀ j : Fin profileInstructionCount, j.val < i.val →
        InstructionLayout bytes (8 * j.val) (referenceInstruction j) := by
  rw [← firstMismatch_eq_some_iff bytes hsize i,
    decode_at_valid_size nativeAbi bytes rfl hsize]
  unfold decodeValidatedSize
  cases hfind : firstMismatch bytes hsize <;> simp [Fin.ext_iff]

-- §FS-filter-loading.input.correctness: Explicit bytes witness inhabited successful validation.
def canonicalBytes : ByteArray := ⟨#[
  0x20, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00,
  0x15, 0x00, 0x01, 0x00, 0x3e, 0x00, 0x00, 0xc0,
  0x06, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80,
  0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x35, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x40,
  0x06, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80,
  0x15, 0x00, 0x00, 0x01, 0x6e, 0x00, 0x00, 0x00,
  0x06, 0x00, 0x00, 0x00, 0x01, 0x00, 0x05, 0x00,
  0x06, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0x7f
]⟩

-- §FS-filter-loading.input.correctness: Kernel reduction checks a real accepted snapshot.
theorem decode_canonical : decode nativeAbi canonicalBytes = .ok .denyGetppid := by
  rfl

end LeanCage.Linux.Filter
