import VirtualMachineProofs.Results
import VirtualMachineProofs.Prefix

namespace LeanCage.Host.VirtualMachine
open Filesystem

-- §FS-host-boundary.acceptance: Useful arbitrary bounded bytes follow the actual native read code.
theorem runtime_read_useful (fd : UInt64) (bytes : ByteArray)
    (positive : 0 < bytes.size) (bounded : bytes.size ≤ chunkMax) :
    Program.Returns (Runtime.read fd chunkMax)
      [.returned (.filesystem { op := .read, first := fd, second := chunkMax.toUInt64 })
        (bytes.size.toUInt64, bytes)] (.ok (.data bytes)) := by
  have fits : bytes.size < 2 ^ 64 := by
    have : chunkMax < 2 ^ 64 := by decide
    omega
  have count : bytes.size.toUInt64.toNat = bytes.size := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt fits]
  have native : nativeError (bytes.size.toUInt64, bytes) = false := by
    change decide (bytes.size.toUInt64.toNat ≥ 2 ^ 63) = false
    rw [count]
    have lower : bytes.size < 2 ^ 63 := by
      have : chunkMax < 2 ^ 63 := by decide
      omega
    simp [Nat.not_le.mpr lower]
  have nonempty : bytes.isEmpty = false := by
    simp only [ByteArray.isEmpty, beq_eq_false_iff_ne]
    omega
  unfold Runtime.read
  split
  · rename_i impossible
    have : ¬ (chunkMax == 0 || decide (chunkMax > chunkMax)) = true := by decide
    exact False.elim (this impossible)
  · dsimp only [Runtime.perform, Program.liftFilesystem, Filesystem.Program.effect, Program.bind]
    apply Program.Returns.call _ _ (bytes.size.toUInt64, bytes) [] _
    dsimp only [Program.bind]
    simp [native, count, nonempty, Nat.not_lt.mpr bounded]
    set_option smartUnfolding false in with_unfolding_all exact .pure _

theorem runtime_eof_useful (fd : UInt64) :
    Program.Returns (Runtime.read fd chunkMax)
      [.returned (.filesystem { op := .read, first := fd, second := chunkMax.toUInt64 })
        (0, .empty)] (.ok .eof) := by
  unfold Runtime.read
  split
  · rename_i impossible
    have : ¬ (chunkMax == 0 || decide (chunkMax > chunkMax)) = true := by decide
    exact False.elim (this impossible)
  · dsimp only [Runtime.perform, Program.liftFilesystem, Filesystem.Program.effect, Program.bind]
    apply Program.Returns.call _ _ ((0 : UInt64), ByteArray.empty) [] _
    change Program.Returns (.pure (.ok .eof : Filesystem.Result Runtime.Read)) [] (.ok .eof)
    exact .pure _

namespace Witness
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
abbrev packet := Transport.Witness.goodWire

def initial : State := { transport := Transport.Witness.initial, connection := some 42 }
def delivered : State := consumeResult 42 43 44 1 initial (.ok (.data packet))
def completed : State := consumeResult 42 43 44 2 delivered (.ok .eof)
def dataEvent : Program.Event := .returned
  (.filesystem { op := .read, first := 42, second := chunkMax.toUInt64 }) (packet.size.toUInt64, packet)
def eofEvent : Program.Event := .returned
  (.filesystem { op := .read, first := 42, second := chunkMax.toUInt64 }) (0, .empty)

def consumer : Program State := do
  let state ← consume 42 43 44 1 initial
  consume 42 43 44 2 state

theorem data_delivered : Program.Returns (consume 42 43 44 1 initial) [dataEvent] delivered := by
  rw [consume_factor]
  exact Program.returns_bind (runtime_read_useful 42 packet (by decide) (by decide)) (.pure delivered)

theorem eof_observed : Program.Returns (consume 42 43 44 2 delivered) [eofEvent] completed := by
  rw [consume_factor]
  exact Program.returns_bind (runtime_eof_useful 42) (.pure completed)

-- §FS-host-boundary.acceptance: The same actual two reads reach a complete framed result.
theorem actual_useful_consumer : Program.Returns consumer [dataEvent, eofEvent] completed :=
  Program.returns_bind data_delivered eof_observed

set_option maxRecDepth 8192 in
set_option cbv.maxSteps 2000000 in
theorem useful_framed : completed.transport.finish = .ok Transport.Witness.result := by cbv

set_option maxRecDepth 8192 in
set_option cbv.maxSteps 2000000 in
theorem no_eof_incomplete : delivered.transport.finish = .error Transport.Error.incomplete.message ∧
    delivered.transport.report? = some Transport.Witness.report := by cbv

-- §FS-host-boundary.transport: An EOF read lost after the report cannot become an observation.
theorem actual_lost_eof : Program.Prefix consumer
    [dataEvent, .lost (.filesystem { op := .read, first := 42, second := chunkMax.toUInt64 })] := by
  have loss : Program.Prefix (consume 42 43 44 2 delivered)
      [.lost (.filesystem { op := .read, first := 42, second := chunkMax.toUInt64 })] := by
    rw [consume_factor]
    exact .lost _ _
  exact prefix_of_return_bind data_delivered loss

end Witness
end LeanCage.Host.VirtualMachine
