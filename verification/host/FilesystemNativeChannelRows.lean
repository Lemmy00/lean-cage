import NativeChannelCode
import FilesystemNativeCodeRows
import FilesystemInitial

namespace LeanCage.Host.NativeChannels

-- §AR-host-boundary.interfaces.gateway: Project canonical actual references,
-- preserving all flags/SDK handles/CWD in the enclosing full snapshot.
theorem encoded_object_at (references : Kernel.NativeReferences) (fd : Nat) :
    objectAt (NativeCode.encodeReferences references) fd =
      if fd < 2 ^ 64 then (references.handles (UInt64.ofNat fd)).map (·.object) else none := by
  by_cases bound : fd < 2 ^ 64
  · cases current : references.handles (UInt64.ofNat fd) <;>
      simp [objectAt, NativeCode.encodeReferences, bound, current, NativeCode.encodeHandle]
  · simp [objectAt, NativeCode.encodeReferences, bound]

-- §FS-host-boundary.caller: The source-built channel observations feed the SAME
-- native exec snapshot's raw projection. No fabricated zero flags or reduced
-- parent/native table is used to identify that snapshot.
def initial_binding_of_native_evidence (references : Kernel.NativeReferences) (data control : Nat)
    (evidence : Evidence (NativeCode.encodeReferences references) data control)
    (ipc : Nat → Prop) (dataIpc : ipc data) (controlIpc : ipc control) :
    Kernel.InitialEngineBinding ipc references.rawProjection.handles references.rawProjection.closeOnExec := by
  rcases evidence with ⟨input, output, cancellation, inputFlag, outputFlag, cancellationFlag, separate⟩
  refine ⟨data, control, ?_, dataIpc, controlIpc⟩
  refine ⟨?_, ?_, ?_, separate, ?_, ?_, ?_, ?_⟩
  · simpa [encoded_object_at, Kernel.rawObjects, Kernel.NativeReferences.rawProjection,
      Kernel.NativeReferences.engineSlot] using input
  · simpa [encoded_object_at, Kernel.rawObjects, Kernel.NativeReferences.rawProjection,
      Kernel.NativeReferences.engineSlot] using output
  · simpa [encoded_object_at, Kernel.rawObjects, Kernel.NativeReferences.rawProjection,
      Kernel.NativeReferences.engineSlot] using cancellation
  · intro fd notInput notOutput notCancellation
    by_cases bound : fd < 2 ^ 64
    · simp only [Kernel.rawObjects, bound, ↓reduceIte, Kernel.NativeReferences.rawProjection,
        Kernel.NativeReferences.engineSlot]
      have zero : (UInt64.ofNat fd == 0) = false := by
        apply Bool.eq_false_iff.mpr; intro equal
        have same : UInt64.ofNat fd = 0 := of_decide_eq_true equal
        have words := congrArg UInt64.toNat same
        exact notInput (by simpa [UInt64.toNat_ofNat_of_lt' bound] using words)
      have one : (UInt64.ofNat fd == 1) = false := by
        apply Bool.eq_false_iff.mpr; intro equal
        have same : UInt64.ofNat fd = 1 := of_decide_eq_true equal
        have words := congrArg UInt64.toNat same
        exact notOutput (by simpa [UInt64.toNat_ofNat_of_lt' bound] using words)
      have three : (UInt64.ofNat fd == 3) = false := by
        apply Bool.eq_false_iff.mpr; intro equal
        have same : UInt64.ofNat fd = 3 := of_decide_eq_true equal
        have words := congrArg UInt64.toNat same
        exact notCancellation (by simpa [UInt64.toNat_ofNat_of_lt' bound] using words)
      simp only [zero, one, three, Bool.false_or, Bool.false_eq_true, ↓reduceIte, Option.map_none]
    · simp [Kernel.rawObjects, bound]
  · simpa [Kernel.rawCloseExec, Kernel.NativeReferences.rawProjection,
      Kernel.NativeReferences.engineSlot, NativeCode.encodeReferences] using inputFlag
  · simpa [Kernel.rawCloseExec, Kernel.NativeReferences.rawProjection,
      Kernel.NativeReferences.engineSlot, NativeCode.encodeReferences] using outputFlag
  · simpa [Kernel.rawCloseExec, Kernel.NativeReferences.rawProjection,
      Kernel.NativeReferences.engineSlot, NativeCode.encodeReferences] using cancellationFlag

end LeanCage.Host.NativeChannels
