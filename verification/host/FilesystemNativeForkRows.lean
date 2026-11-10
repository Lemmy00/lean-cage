import FilesystemNativeCodeRows

namespace LeanCage.Host.NativeCode

variable {kernel : Kernel.Contract} {sourceProgram : Program UInt32}
  {runtime : Kernel.ActorRuntime kernel sourceProgram} {primitive : Kernel.NativePrimitive kernel}
  {ticks : List (Kernel.ActorTick runtime)} {key : SourceKey}
  {before after : Kernel.NativeProcesses} {code : CallRow}

-- §AR-host-boundary.primitives: This observation is the actual fork before child
-- file actions/exec, rather than the enclosing SDK call's eventual return.
structure ForkReferences (primitive : Kernel.NativePrimitive kernel) : Prop where
  cloned : ∀ (tick : Kernel.ActorTick runtime) (before after : Kernel.NativeProcesses)
    (call : Kernel.NativeCallAt primitive tick before after) (child : Kernel.NativeToken),
    call.product = .created child → after.references child = some call.beforeReferences

-- §FS-host-boundary.ownership: A committed child has this same source-built spawn
-- and parent lifetime even if no SDK acknowledgement will ever be delivered.
theorem source_committed_fork (binding : SelectedCall primitive ticks key before after code)
    (child : Kernel.NativeToken) (arguments : Spawn)
    (created : code.product = .created child) (operation : code.operation = .spawn arguments) :
    before.allocated child = false ∧ after.allocated child = true ∧
    ∃ actual birth,
      binding.call.operation = .spawn actual ∧ encodeSpawn actual = arguments ∧
      after.births child = some birth ∧ birth.parent = key.process ∧ birth.arguments = actual := by
  have product : binding.call.product = .created child := by
    have accepted := binding.interpreted.product
    rw [created] at accepted
    change some (Kernel.NativeProduct.created child) = some binding.call.product at accepted
    exact (Option.some.inj accepted).symm
  have observed := binding.call.native
  rw [product] at observed
  obtain ⟨absent, born⟩ := primitive.created _ _ _ _ _ _ _ _ _ observed
  obtain ⟨actual, birth, selected, committed, stored, parent, actualArguments⟩ :=
    primitive.fresh_source _ _ _ _ _ _ _ _ _ _ binding.call.native absent born
  have encoded := selected_operation binding
  rw [selected, operation] at encoded
  have encodedArguments : encodeSpawn actual = arguments := by
    simpa only [encodeOperation, Operation.spawn.injEq] using encoded
  exact ⟨absent, born, actual, birth, selected, encodedArguments, stored,
    parent.trans binding.current, actualArguments⟩

-- §FS-host-boundary.ownership: Preserve the full inherited fork table/CWD. Only
-- source-held entries are supplied by the source lease producer; other slots
-- keep this one actual fork snapshot's values.
theorem source_fork_references (fork : ForkReferences (runtime := runtime) primitive)
    (binding : SelectedCall primitive ticks key before after code)
    (child : Kernel.NativeToken) (created : code.product = .created child) :
    after.references child = some (decodeReferences code.beforeReferences) := by
  have product : binding.call.product = .created child := by
    have accepted := binding.interpreted.product
    rw [created] at accepted
    change some (Kernel.NativeProduct.created child) = some binding.call.product at accepted
    exact (Option.some.inj accepted).symm
  rw [binding.interpreted.input, references_roundtrip]
  exact fork.cloned binding.tick before after binding.call child product

end LeanCage.Host.NativeCode
