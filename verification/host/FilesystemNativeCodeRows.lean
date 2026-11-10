import FilesystemNativeDecoding
import FilesystemNativeReferences

namespace LeanCage.Host.NativeCode

variable {kernel : Kernel.Contract} {sourceProgram : Program UInt32}
  {runtime : Kernel.ActorRuntime kernel sourceProgram} {primitive : Kernel.NativePrimitive kernel}
  {tick : Kernel.ActorTick runtime} {before after : Kernel.NativeProcesses}

def encodeCall (call : Kernel.NativeCallAt primitive tick before after) : CallRow :=
  { process := call.token
    caller := encodeCredentials call.caller
    beforeReferences := encodeReferences call.beforeReferences
    afterReferences := encodeReferences call.afterReferences
    operation := encodeOperation call.operation
    reply := call.reply.map encodeReply
    product := encodeProduct call.product }

structure Interprets (code : CallRow) (call : Kernel.NativeCallAt primitive tick before after) : Prop where
  process : code.process = call.token
  caller : decodeCredentials code.caller = call.caller
  input : code.beforeReferences = encodeReferences call.beforeReferences
  output : code.afterReferences = encodeReferences call.afterReferences
  operation : operation? code.operation = some call.operation
  reply : code.reply = call.reply.map encodeReply
  product : product? code.product = some call.product

-- §FS-host-boundary.ownership: Preserve the full caller table/CWD at this exact row.
-- An earlier engine table or the three-channel projection supplies no such encoding.
theorem encode_call_exact (call : Kernel.NativeCallAt primitive tick before after) :
    Interprets (encodeCall call) call := by
  exact ⟨rfl, credentials_roundtrip _, rfl, rfl,
    operation_roundtrip _, rfl, product_roundtrip _⟩

-- §AR-host-boundary.interfaces.gateway: The shared source key keeps actual allocation lifetimes.
structure SelectedCall (primitive : Kernel.NativePrimitive kernel)
    (ticks : List (Kernel.ActorTick runtime)) (key : SourceKey)
    (before after : Kernel.NativeProcesses) (code : CallRow) where
  position : Nat
  tick : Kernel.ActorTick runtime
  selected : ticks[position]? = some tick
  call : Kernel.NativeCallAt primitive tick before after
  current : call.token = key.process
  entryBefore : key.entryPosition ≤ position
  headers : key.actionsLifetime ≠ key.attributesLifetime
  interpreted : Interprets code call

-- §AR-host-boundary.primitives: One SDK operation maps to this one actual physical row.
-- Source entry/order, fresh local headers and constructed operands are absent here.
structure PrimitiveRowAt (primitive : Kernel.NativePrimitive kernel)
    (ticks : List (Kernel.ActorTick runtime)) (position : Nat)
    (before after : Kernel.NativeProcesses) (code : CallRow) where
  tick : Kernel.ActorTick runtime
  selected : ticks[position]? = some tick
  call : Kernel.NativeCallAt primitive tick before after
  interpreted : Interprets code call

-- §AR-host-boundary.interfaces.gateway: The checked C producer supplies these three
-- invocation facts; the per-operation adapter supplies only the actual row above.
def bindSourceRow {ticks : List (Kernel.ActorTick runtime)} {key : SourceKey} {code : CallRow}
    {position : Nat} (row : PrimitiveRowAt primitive ticks position before after code)
    (process : code.process = key.process) (entry : key.entryPosition ≤ position)
    (headers : key.actionsLifetime ≠ key.attributesLifetime) :
    SelectedCall primitive ticks key before after code :=
  ⟨position, row.tick, row.selected, row.call,
    row.interpreted.process.symm.trans process, entry, headers, row.interpreted⟩

variable {ticks : List (Kernel.ActorTick runtime)} {key : SourceKey} {code : CallRow}

-- §FS-host-boundary.caller: This binding consumes the actual pending call code without
-- presuming a later SDK success, child creation or execution observation.
theorem selected_operation (binding : SelectedCall primitive ticks key before after code) :
    encodeOperation binding.call.operation = code.operation :=
  operation_exact binding.interpreted.operation

theorem selected_input_table (binding : SelectedCall primitive ticks key before after code) :
    before.references key.process = some (decodeReferences code.beforeReferences) := by
  rw [binding.interpreted.input, references_roundtrip, ← binding.current]
  exact binding.call.inputTable

theorem selected_committed_product (binding : SelectedCall primitive ticks key before after code) :
    encodeProduct binding.call.product = code.product :=
  product_exact binding.interpreted.product

-- §FS-host-boundary.ownership: A source-held entry is read from this exact full
-- native table; malformed or erased reference encodings cannot create a lease.
theorem source_handle_at (binding : SelectedCall primitive ticks key before after code)
    (fd : Nat) (bound : fd < 2 ^ 64) (handle : Handle)
    (selected : code.beforeReferences.handles fd = some handle) :
    ∃ actual, binding.call.beforeReferences.handles (UInt64.ofNat fd) = some actual ∧
      encodeHandle actual = handle ∧
      binding.call.beforeReferences.closeOnExec (UInt64.ofNat fd) =
        code.beforeReferences.closeOnExec fd := by
  rw [binding.interpreted.input] at selected
  simp only [encodeReferences, bound, ↓reduceIte] at selected
  cases current : binding.call.beforeReferences.handles (UInt64.ofNat fd) with
  | none => simp only [current, Option.map_none] at selected; cases selected
  | some actual =>
    refine ⟨actual, rfl, ?_, ?_⟩
    · simpa only [current, Option.map_some, Option.some.injEq] using selected
    · simp only [binding.interpreted.input, encodeReferences, bound, ↓reduceIte]

theorem source_working_directory (binding : SelectedCall primitive ticks key before after code) :
    binding.call.beforeReferences.workingDirectory = code.beforeReferences.workingDirectory := by
  rw [binding.interpreted.input]
  rfl

-- §FS-host-boundary.ownership: Commit, optional reply and both full parent tables
-- belong to the same source-bound call, even when the source reply is lost.
theorem bound_source_row {position : Nat}
    (row : PrimitiveRowAt primitive ticks position before after code)
    (process : code.process = key.process) (entry : key.entryPosition ≤ position)
    (headers : key.actionsLifetime ≠ key.attributesLifetime) :
    let binding := bindSourceRow row process entry headers
    encodeOperation binding.call.operation = code.operation ∧
    before.references key.process = some (decodeReferences code.beforeReferences) ∧
    after.references key.process = some (decodeReferences code.afterReferences) ∧
    binding.call.reply.map encodeReply = code.reply ∧
    encodeProduct binding.call.product = code.product := by
  dsimp only
  refine ⟨selected_operation (bindSourceRow row process entry headers),
    selected_input_table (bindSourceRow row process entry headers), ?_, ?_,
    selected_committed_product (bindSourceRow row process entry headers)⟩
  · rw [row.interpreted.output, references_roundtrip, ← process, row.interpreted.process]
    exact row.call.outputTable
  · exact row.interpreted.reply.symm

end LeanCage.Host.NativeCode
