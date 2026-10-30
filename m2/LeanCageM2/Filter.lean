import LeanCage.Proofs.FilterDecoder

namespace LeanCageM2.Bytecode
open LeanCage.Linux.Filter

-- §FS-lifecycle.filter: Unsigned bytecode execution, failing closed on malformed programs/fuel.
def run (program : Array Instruction) (arch nr : UInt32) :
    Nat → Nat → UInt32 → Option UInt32
  | 0, _, _ => none
  | fuel + 1, pc, accumulator => do
    let instruction ← program[pc]?
    if instruction.code = 0x20 then
      let loaded ← if instruction.k = 4 then some arch
        else if instruction.k = 0 then some nr else none
      run program arch nr fuel (pc + 1) loaded
    else if instruction.code = 0x15 then
      let offset := if accumulator = instruction.k then instruction.jt else instruction.jf
      run program arch nr fuel (pc + 1 + offset.toNat) accumulator
    else if instruction.code = 0x35 then
      let offset := if accumulator ≥ instruction.k then instruction.jt else instruction.jf
      run program arch nr fuel (pc + 1 + offset.toNat) accumulator
    else if instruction.code = 6 then some instruction.k else none

def action (arch nr : UInt32) : UInt32 :=
  if arch ≠ 0xc000003e then 0x80000000
  else if nr ≥ 0x40000000 then 0x80000000
  else if nr = 110 then 0x50001 else 0x7fff0000

-- §FS-lifecycle.filter: Single-instruction rules prevent unrolling unknown control flow.
private theorem load_arch (p : Array Instruction) (arch nr a : UInt32) (f pc : Nat)
    (h : p[pc]? = some ⟨0x20, 0, 0, 4⟩) :
    run p arch nr (f + 1) pc a = run p arch nr f (pc + 1) arch := by
  rw [run, h]; rfl

private theorem load_nr (p : Array Instruction) (arch nr a : UInt32) (f pc : Nat)
    (h : p[pc]? = some ⟨0x20, 0, 0, 0⟩) :
    run p arch nr (f + 1) pc a = run p arch nr f (pc + 1) nr := by
  rw [run, h]; rfl

private theorem jeq (p : Array Instruction) (arch nr a k : UInt32) (t e : UInt8) (f pc : Nat)
    (h : p[pc]? = some ⟨0x15, t, e, k⟩) :
    run p arch nr (f + 1) pc a =
      run p arch nr f (pc + 1 + (if a = k then t else e).toNat) a := by
  rw [run, h]; rfl

private theorem jge (p : Array Instruction) (arch nr a k : UInt32) (t e : UInt8) (f pc : Nat)
    (h : p[pc]? = some ⟨0x35, t, e, k⟩) :
    run p arch nr (f + 1) pc a =
      run p arch nr f (pc + 1 + (if a ≥ k then t else e).toNat) a := by
  rw [run, h]; rfl

private theorem ret (p : Array Instruction) (arch nr a k : UInt32) (f pc : Nat)
    (h : p[pc]? = some ⟨6, 0, 0, k⟩) : run p arch nr (f + 1) pc a = some k := by
  rw [run, h]; rfl

-- §FS-lifecycle.filter: Every architecture/syscall word, by kernel-checked instruction rules.
theorem canonical_action (arch nr : UInt32) :
    run Program.denyGetppid.instructions arch nr 10 0 0 = some (action arch nr) := by
  let p := Program.denyGetppid.instructions
  have h0 : p[0]? = some ⟨0x20,0,0,4⟩ := by decide
  have h1 : p[1]? = some ⟨0x15,1,0,0xc000003e⟩ := by decide
  have h2 : p[2]? = some ⟨6,0,0,0x80000000⟩ := by decide
  have h3 : p[3]? = some ⟨0x20,0,0,0⟩ := by decide
  have h4 : p[4]? = some ⟨0x35,0,1,0x40000000⟩ := by decide
  have h5 : p[5]? = some ⟨6,0,0,0x80000000⟩ := by decide
  have h6 : p[6]? = some ⟨0x15,0,1,110⟩ := by decide
  have h7 : p[7]? = some ⟨6,0,0,0x50001⟩ := by decide
  have h8 : p[8]? = some ⟨6,0,0,0x7fff0000⟩ := by decide
  rw [load_arch p arch nr 0 9 0 h0, jeq p arch nr arch 0xc000003e 1 0 8 1 h1]
  by_cases ha : arch = 0xc000003e
  · rw [ite_eq_left ha]
    change run p arch nr 8 3 arch = _
    rw [load_nr p arch nr arch 7 3 h3, jge p arch nr nr 0x40000000 0 1 6 4 h4]
    by_cases hn : nr ≥ 0x40000000
    · rw [ite_eq_left hn]
      change run p arch nr 6 5 nr = _
      rw [ret p arch nr nr 0x80000000 5 5 h5]
      simp [action, ha, hn]
    · rw [ite_eq_right hn]
      change run p arch nr 6 6 nr = _
      rw [jeq p arch nr nr 110 0 1 5 6 h6]
      by_cases he : nr = 110
      · rw [ite_eq_left he]
        change run p arch nr 5 7 nr = _
        rw [ret p arch nr nr 0x50001 4 7 h7]
        simp [action, ha, he]
      · rw [ite_eq_right he]
        change run p arch nr 5 8 nr = _
        rw [ret p arch nr nr 0x7fff0000 4 8 h8]
        simp [action, ha, hn, he]
  · rw [ite_eq_right ha]
    change run p arch nr 8 2 arch = _
    rw [ret p arch nr arch 0x80000000 7 2 h2]
    simp [action, ha]

-- §FS-lifecycle.filter: A successful original decoder names exactly the proved bytecode.
theorem decoded_action (abi : Abi) (bytes : ByteArray) (program : Program)
    (_accepted : decode abi bytes = .ok program) (arch nr : UInt32) :
    run program.instructions arch nr 10 0 0 = some (action arch nr) := by
  cases program
  exact canonical_action arch nr

-- §FS-lifecycle.filter: Unsupported or unbounded machine behavior cannot yield allow.
theorem zero_fuel (program : Array Instruction) (arch nr : UInt32) (pc : Nat) (a : UInt32) :
    run program arch nr 0 pc a = none := rfl

end LeanCageM2.Bytecode
