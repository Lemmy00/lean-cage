import LeanCage

-- §AR-filter-slice.contracts: Interpret the reference fixture without OS effects or decoding.
-- These checks establish representative behavior, not a security theorem or Linux equivalence.
namespace LeanCage.Tests.FilterContract

open LeanCage.Linux.Filter

private def run (program : Array Instruction) (arch nr : UInt32) :
    Nat → Nat → UInt32 → Option UInt32
  | 0, _, _ => none
  | fuel + 1, pc, accumulator => do
    let instruction ← program[pc]?
    if instruction.code == 0x0020 then
      let loaded ← if instruction.k == 4 then some arch
                    else if instruction.k == 0 then some nr
                    else none
      run program arch nr fuel (pc + 1) loaded
    else if instruction.code == 0x0015 then
      let offset := if accumulator == instruction.k then instruction.jt else instruction.jf
      run program arch nr fuel (pc + 1 + offset.toNat) accumulator
    else if instruction.code == 0x0035 then
      let offset := if accumulator ≥ instruction.k then instruction.jt else instruction.jf
      run program arch nr fuel (pc + 1 + offset.toNat) accumulator
    else if instruction.code == 0x0006 then
      some instruction.k
    else
      none

private def action (arch nr : UInt32) : Option UInt32 :=
  run Program.denyGetppid.instructions arch nr 10 0 0

-- §AR-filter-slice.abi: Check useful native paths and both sides of the denial comparison.
#guard action 0xc000003e 39 == some 0x7fff0000
#guard action 0xc000003e 59 == some 0x7fff0000
#guard action 0xc000003e 157 == some 0x7fff0000
#guard action 0xc000003e 231 == some 0x7fff0000
#guard action 0xc000003e 109 == some 0x7fff0000
#guard action 0xc000003e 110 == some 0x00050001
#guard action 0xc000003e 111 == some 0x7fff0000

-- §AR-filter-slice.abi: An architecture mismatch must win even for an otherwise allowed number.
#guard action 0x40000003 39 == some 0x80000000
#guard action 0xc00000b7 110 == some 0x80000000

-- §AR-filter-slice.abi: Exercise unsigned threshold, x32 calls, and a negative syscall word.
#guard action 0xc000003e 0x3fffffff == some 0x7fff0000
#guard action 0xc000003e 0x40000000 == some 0x80000000
#guard action 0xc000003e 0x40000027 == some 0x80000000
#guard action 0xc000003e 0x4000006e == some 0x80000000
#guard action 0xc000003e 0xffffffff == some 0x80000000

end LeanCage.Tests.FilterContract
