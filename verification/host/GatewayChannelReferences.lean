import GatewayChannelHistory

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

-- §FS-host-boundary.ownership: Raw reference places keep current and retiring
-- tables separate. SDK support is a current physical sample, never an old
-- exec snapshot treated as a live reference; CWD is not a socket reference.
inductive ReferencePlace where
  | native (process : NativeToken) (descriptor : UInt64)
  | retiring (process : NativeToken) (descriptor : UInt64)
  | engine (actor : ActorId) (descriptor : UInt64)
  | support (process : NativeToken) (descriptor : UInt64)

def referenceAt (population : Population) (native : NativeProcesses)
    (support : NativeToken → UInt64 → Option Handle) : ReferencePlace → Option Handle
  | .native process descriptor => (native.references process).bind (fun table => table.handles descriptor)
  | .retiring process descriptor => (native.retiring process).bind (fun table => table.handles descriptor)
  | .engine actor descriptor => (population.actors actor).bind (fun engine => engine.references descriptor)
  | .support process descriptor => support process descriptor

def NoEndpointReference (population : Population) (native : NativeProcesses)
    (support : NativeToken → UInt64 → Option Handle) (object : ObjectId) : Prop :=
  ∀ place handle, referenceAt population native support place = some handle → handle.object ≠ object

theorem native_reference_present (population : Population) (native : NativeProcesses)
    (support : NativeToken → UInt64 → Option Handle) (process : NativeToken)
    (table : NativeReferences) (descriptor : UInt64) (handle : Handle)
    (current : native.references process = some table) (held : table.handles descriptor = some handle) :
    referenceAt population native support (.native process descriptor) = some handle := by
  simp only [referenceAt, current, Option.bind_some, held]

theorem retained_native_reference_excludes_last_drop
    (population : Population) (native : NativeProcesses)
    (support : NativeToken → UInt64 → Option Handle) (process : NativeToken)
    (table : NativeReferences) (descriptor : UInt64) (handle : Handle)
    (current : native.references process = some table) (held : table.handles descriptor = some handle) :
    ¬ NoEndpointReference population native support handle.object := by
  intro absent
  exact absent (.native process descriptor) handle
    (native_reference_present population native support process table descriptor handle current held) rfl

inductive NativeReadOperand : NativeOperation → UInt64 → Prop where
  | receive (descriptor extent flags : UInt64) : NativeReadOperand (.receive descriptor extent flags) descriptor
  | adapted (request : Request) (reading : request.op = .read) : NativeReadOperand (.vfs (.adapted request)) request.first

inductive NativeReadShutdown : NativeOperation → UInt64 → Prop where
  | shutdown (descriptor how : UInt64) (reading : how = 0 ∨ how = 2) :
      NativeReadShutdown (.shutdown descriptor how) descriptor

-- This boundary is applied to the actual resolved operand of ONE external
-- host-code operation. It does not classify verified C, SDK setup or engine
-- source, grant an invocation role, or assert a queue/whole-callback frame.
def ExternalReadAuthority {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {native : NativePrimitive kernel} {tick : ActorTick runtime} {before after : NativeProcesses}
    (call : NativeCallAt native tick before after) (object : ObjectId) : Prop :=
  ∀ descriptor handle,
    (NativeReadOperand call.operation descriptor ∨ NativeReadShutdown call.operation descriptor) →
    call.beforeReferences.handles descriptor = some handle → handle.object ≠ object

inductive NativeEndpointRead {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {native : NativePrimitive kernel} {tick : ActorTick runtime} {before after : NativeProcesses}
    (call : NativeCallAt native tick before after) (object : ObjectId) : Prop where
  | read (descriptor : UInt64) (handle : Handle) (operand : NativeReadOperand call.operation descriptor)
      (input : call.beforeReferences.handles descriptor = some handle) (endpoint : handle.object = object) :
      NativeEndpointRead call object

inductive NativeEndpointShutdown {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {native : NativePrimitive kernel} {tick : ActorTick runtime} {before after : NativeProcesses}
    (call : NativeCallAt native tick before after) (object : ObjectId) : Prop where
  | shutdown (descriptor : UInt64) (handle : Handle) (operand : NativeReadShutdown call.operation descriptor)
      (input : call.beforeReferences.handles descriptor = some handle) (endpoint : handle.object = object) :
      NativeEndpointShutdown call object

theorem external_no_endpoint_read {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {native : NativePrimitive kernel} {tick : ActorTick runtime} {before after : NativeProcesses}
    (call : NativeCallAt native tick before after) (object : ObjectId)
    (authority : ExternalReadAuthority call object) :
    ¬ NativeEndpointRead call object ∧ ¬ NativeEndpointShutdown call object := by
  constructor
  · intro read
    cases read with
    | read descriptor handle operand input endpoint => exact authority descriptor handle (.inl operand) input endpoint
  · intro shutdown
    cases shutdown with
    | shutdown descriptor handle operand input endpoint => exact authority descriptor handle (.inr operand) input endpoint

-- §AR-host-boundary.primitives: Closing the write half is distinguished from
-- read shutdown in the actual integer operand. It cannot discard unread reply
-- bytes merely because the source requests SHUT_WR.
theorem shutdown_write_not_read (descriptor : UInt64) :
    ¬ NativeReadShutdown (.shutdown descriptor 1) descriptor := by
  intro shutdown
  cases shutdown with
  | shutdown descriptor how reading => rcases reading with false | false <;> contradiction

end LeanCage.Host.PrivateStreams
