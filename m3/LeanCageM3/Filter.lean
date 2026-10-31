import LeanCageM2.Filter

namespace LeanCageM3.Filter
open LeanCage.Linux.Filter

-- §FS-workspace.execution: A closed versioned syscall table; filesystem authority is separate.
def allowed : List UInt32 :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
   16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 32, 33, 34,
   35, 36, 37, 38, 39, 57, 58, 59, 60, 61, 62, 63, 72, 73, 74, 75,
   76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91,
   92, 93, 94, 95, 96, 97, 98, 99, 100, 102, 104, 107, 108, 110, 111, 112,
   113, 115, 118, 120, 121, 124, 125, 127, 128, 129, 130, 131, 132, 133, 137, 138, 140,
   143, 145, 146, 147, 148, 149, 150, 151, 152, 157, 158, 160, 186, 187, 191, 192,
   193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 217, 218, 219, 221,
   222, 223, 224, 225, 226, 228, 229, 230, 231, 232, 233, 234, 235, 253, 254, 255,
   257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 273, 275,
   276, 277, 278, 280, 281, 282, 283, 284, 285, 286, 287, 289, 290, 291, 292, 293,
   295, 296, 302, 309, 318, 322, 324, 325, 326, 327, 328, 332, 334, 436, 439, 441,
   449]

def kill : UInt32 := 0x80000000
def deny : UInt32 := 0x50001
def fallback : UInt32 := 0x50026
def allow : UInt32 := 0x7fff0000

-- §FS-workspace.execution: clone3 returns ENOSYS for libc's clone fallback.
-- §AR-workspace.interfaces: clone allows reviewed thread/parent-tid and signal bits.
def cloneMask : UInt32 := 0x013d4fff

def action (arch nr low high : UInt32) : UInt32 :=
  if arch ≠ 0xc000003e ∨ nr ≥ 0x40000000 then kill
  else if nr = 435 then fallback
  else if nr = 56 then
    if high = 0 ∧ (low &&& ~~~cloneMask) = 0 then allow else deny
  else if nr ∈ allowed then allow else deny

def returns (value : UInt32) : Instruction := ⟨6, 0, 0, value⟩

def table : List UInt32 → List Instruction
  | [] => [returns deny]
  | nr :: rest => ⟨0x15, 0, 1, nr⟩ :: returns allow :: table rest

def instructionsFor (numbers : List UInt32) : List Instruction :=
  [⟨0x20, 0, 0, 4⟩, ⟨0x15, 1, 0, 0xc000003e⟩, returns kill,
   ⟨0x20, 0, 0, 0⟩, ⟨0x35, 0, 1, 0x40000000⟩, returns kill,
   ⟨0x15, 0, 1, 435⟩, returns fallback,
   ⟨0x15, 0, 7, 56⟩, ⟨0x20, 0, 0, 20⟩, ⟨0x15, 1, 0, 0⟩, returns deny,
   ⟨0x20, 0, 0, 16⟩, ⟨0x45, 0, 1, ~~~cloneMask⟩, returns deny, returns allow] ++ table numbers

def instructions : List Instruction := instructionsFor allowed

-- §AR-workspace.proofs: Executable cBPF suffix semantics with UInt32 loads, jumps and fail-closed
-- fuel.
def run (arch nr low high : UInt32) : Nat → List Instruction → UInt32 → Option UInt32
  | 0, _, _ => none
  | _ + 1, [], _ => none
  | fuel + 1, instruction :: rest, accumulator =>
    if instruction.code = 0x20 then
      match instruction.k with
      | 0 => run arch nr low high fuel rest nr
      | 4 => run arch nr low high fuel rest arch
      | 16 => run arch nr low high fuel rest low
      | 20 => run arch nr low high fuel rest high
      | _ => none
    else if instruction.code = 0x15 then
      run arch nr low high fuel
        (rest.drop (if accumulator = instruction.k then instruction.jt.toNat else instruction.jf.toNat)) accumulator
    else if instruction.code = 0x35 then
      run arch nr low high fuel
        (rest.drop (if accumulator ≥ instruction.k then instruction.jt.toNat else instruction.jf.toNat)) accumulator
    else if instruction.code = 0x45 then
      run arch nr low high fuel
        (rest.drop (if accumulator &&& instruction.k ≠ 0 then instruction.jt.toNat else instruction.jf.toNat)) accumulator
    else if instruction.code = 6 then some instruction.k
    else none

-- §AR-workspace.proofs: The table theorem quantifies over every syscall word and arbitrary table.
theorem table_action (numbers : List UInt32) (arch nr low high : UInt32) (extra : Nat) :
    run arch nr low high (numbers.length + extra + 2) (table numbers) nr =
      some (if nr ∈ numbers then allow else deny) := by
  induction numbers with
  | nil => simp [run, table, returns]
  | cons number rest ih =>
    by_cases eq : nr = number
    · subst number
      simp [table, run, returns, allow]
    · simpa [table, run, returns, eq, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih

private theorem load_arch (arch nr low high a : UInt32) (fuel : Nat) (rest : List Instruction) :
    run arch nr low high (fuel + 1) (⟨0x20,0,0,4⟩ :: rest) a =
      run arch nr low high fuel rest arch := by simp [run]

private theorem load_nr (arch nr low high a : UInt32) (fuel : Nat) (rest : List Instruction) :
    run arch nr low high (fuel + 1) (⟨0x20,0,0,0⟩ :: rest) a =
      run arch nr low high fuel rest nr := by simp [run]

private theorem ret (arch nr low high a k : UInt32) (fuel : Nat) (rest : List Instruction) :
    run arch nr low high (fuel + 1) (returns k :: rest) a = some k := by simp [run, returns]

private theorem jeq (arch nr low high a k : UInt32) (t f : UInt8) (fuel : Nat) (rest : List Instruction) :
    run arch nr low high (fuel + 1) (⟨0x15,t,f,k⟩ :: rest) a =
      run arch nr low high fuel (rest.drop (if a = k then t.toNat else f.toNat)) a := by simp [run]

private theorem jge (arch nr low high a k : UInt32) (t f : UInt8) (fuel : Nat) (rest : List Instruction) :
    run arch nr low high (fuel + 1) (⟨0x35,t,f,k⟩ :: rest) a =
      run arch nr low high fuel (rest.drop (if a ≥ k then t.toNat else f.toNat)) a := by simp [run]

-- §AR-workspace.proofs: Universal architecture/syscall/argument theorem for generated native
-- bytecode.
theorem program_action (numbers : List UInt32) (arch nr low high : UInt32) :
    run arch nr low high (numbers.length + 20) (instructionsFor numbers) 0 =
      some (if arch ≠ 0xc000003e ∨ nr ≥ 0x40000000 then kill
        else if nr = 435 then fallback
        else if nr = 56 then (if high = 0 ∧ (low &&& ~~~cloneMask) = 0 then allow else deny)
        else if nr ∈ numbers then allow else deny) := by
  unfold instructionsFor
  simp only [List.cons_append, List.nil_append]
  rw [load_arch, jeq]
  by_cases ha : arch = 0xc000003e
  · simp [ha]
    rw [load_nr, jge]
    by_cases hn : nr ≥ 0x40000000
    · simp [hn]
      rw [ret]
    · simp [hn]
      rw [jeq]
      by_cases hc : nr = 435
      · simp [hc]
        rw [ret]
      · simp [hc]
        rw [jeq]
        by_cases clone : nr = 56
        · simp [clone]
          by_cases hh : high = 0
          · by_cases hl : low &&& ~~~cloneMask = 0
            · simp [run, returns, hh, hl]
            · simp [run, returns, hh, hl]
          · simp [run, returns, hh]
        · simp [clone]
          simpa [ha, hn, hc, clone, Nat.add_assoc] using
            table_action numbers arch nr low high 12
  · simp [ha]
    rw [ret]

theorem policy_filter_action (arch nr low high : UInt32) :
    run arch nr low high (allowed.length + 20) instructions 0 = some (action arch nr low high) := by
  exact program_action allowed arch nr low high

def bytes : ByteArray := instructions.foldl (fun acc instruction =>
  acc ++ ByteArray.mk #[instruction.code.toUInt8, (instruction.code.toNat >>> 8).toUInt8,
    instruction.jt, instruction.jf, instruction.k.toUInt8, (instruction.k.toNat >>> 8).toUInt8,
    (instruction.k.toNat >>> 16).toUInt8, (instruction.k.toNat >>> 24).toUInt8]) ByteArray.empty

end LeanCageM3.Filter
