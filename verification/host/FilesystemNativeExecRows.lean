import FilesystemNativeChannelRows
import FilesystemNativeEffects

namespace LeanCage.Host.NativeChannels

variable {kernel : Kernel.Contract} {sourceProgram : Program UInt32}
  {runtime : Kernel.ActorRuntime kernel sourceProgram} {primitive : Kernel.NativePrimitive kernel}
  {ticks : List (Kernel.ActorTick runtime)} {position : Nat}
  {before after : Kernel.NativeProcesses} {code : NativeCode.CallRow}

-- §FS-host-boundary.caller: Channel evidence refers to this child's actual exec
-- row and its full output table, rather than to the parent's source-spawn key.
-- The product is an already observed exec; no eventual spawn reply is required.
theorem actual_exec_binding
    (row : NativeCode.PrimitiveRowAt primitive ticks position before after code)
    (image data control : Nat) (executed : code.product = .executed image)
    (evidence : Evidence code.afterReferences data control)
    (ipc : Nat → Prop) (dataIpc : ipc data) (controlIpc : ipc control) :
    ∃ arguments execution,
      row.call.operation = .exec arguments ∧
      after.executions code.process = some execution ∧
      execution.image = image ∧ execution.arguments = arguments ∧
      row.call.afterReferences = execution.references ∧
      Nonempty (Kernel.InitialEngineBinding ipc execution.references.rawProjection.handles
        execution.references.rawProjection.closeOnExec) := by
  have product : row.call.product = .executed image := by
    have accepted := row.interpreted.product
    rw [executed] at accepted
    change some (Kernel.NativeProduct.executed image) = some row.call.product at accepted
    exact (Option.some.inj accepted).symm
  obtain ⟨arguments, execution, operation, stored, actualImage, actualArguments, table⟩ :=
    Kernel.native_exec_table row.call product
  refine ⟨arguments, execution, operation, ?_, actualImage, actualArguments, table, ?_⟩
  · simpa only [row.interpreted.process] using stored
  · refine ⟨initial_binding_of_native_evidence execution.references data control ?_ ipc dataIpc controlIpc⟩
    simpa only [row.interpreted.output, table] using evidence

end LeanCage.Host.NativeChannels
