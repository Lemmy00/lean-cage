import GatewayChannelEngineReaders
import GatewayChannelReferenceHistory
import GatewayChannelResidualBatch

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
  {before after : Processes} {callers next : NativeProcesses} {ticks : List (ActorTick runtime)} {pair : Pair} {Token : Type}

def residualReadOpcode : NativeOperation → Bool
  | .receive _ _ flags => flags != 0
  | .vfs (.adapted request) => request.op == .read && request.third == 0
  | _ => false

theorem residual_read_opcode {tick : ActorTick runtime} {current following : NativeProcesses}
    {call : NativeCallAt native tick current following} {object : ObjectId}
    (read : NativeResidualRead call object) : residualReadOpcode call.operation = true := by
  rcases read.operation with ⟨request, operation, reading, stream, descriptor⟩ | ⟨extent, flags, operation, nonzero⟩
  · simp only [operation, residualReadOpcode, reading, stream, beq_self_eq_true, Bool.and_self]
  · simp only [operation, residualReadOpcode, bne_iff_ne, ne_eq, nonzero, not_false_eq_true]

theorem native_read_operand_unique {operation : NativeOperation} {first last : UInt64}
    (left : NativeReadOperand operation first) (right : NativeReadOperand operation last) : first = last := by
  cases left <;> cases right <;> rfl

-- §AR-host-boundary.interfaces.gateway: These are individual source opcode
-- or resolved-operand receipts. A kernel primitive grants none of these
-- source/caller facts, and no complete invocation is labelled a safe reader.
inductive NativeResidualSource {tick : ActorTick runtime} {current following : NativeProcesses}
    (call : NativeCallAt native tick current following) (socket : SocketLifetime) : Type where
  | opcode (allowed : residualReadOpcode call.operation = false) : NativeResidualSource call socket
  | operand (descriptor : UInt64) (handle : Handle) (read : NativeReadOperand call.operation descriptor)
      (input : call.beforeReferences.handles descriptor = some handle) (outside : ¬ socket.matches handle) :
      NativeResidualSource call socket
  | external (profile : ExternalEndpointOperands call socket.object) : NativeResidualSource call socket

theorem native_residual_source_excludes {tick : ActorTick runtime} {current following : NativeProcesses}
    {call : NativeCallAt native tick current following} {socket : SocketLifetime}
    (source : NativeResidualSource call socket) (read : NativeResidualRead call socket.object)
    (description : read.handle.description = socket.description) : False := by
  cases source with
  | opcode allowed => have impossible := residual_read_opcode read; rw [allowed] at impossible; cases impossible
  | operand descriptor handle operand input outside =>
    have same := native_read_operand_unique read.input_operand operand
    have selected := read.input
    rw [same, input] at selected
    have equal := Option.some.inj selected
    exact outside (equal ▸ ⟨read.endpoint, description⟩)
  | external profile => exact profile read.descriptor read.handle (.read read.input_operand) read.input read.endpoint

-- Literal flags-zero recv is the actual gateway source case. It remains
-- a permitted canonical read, accounted once by NativeReadRow.
def native_flags_zero_source {tick : ActorTick runtime} {current following : NativeProcesses}
    (call : NativeCallAt native tick current following) (descriptor extent : UInt64)
    (operation : call.operation = .receive descriptor extent 0) (socket : SocketLifetime) :
    NativeResidualSource call socket := .opcode (by simp [operation, residualReadOpcode])

def readShutdownOpcode : NativeOperation → Bool
  | .shutdown _ how => how == 0 || how == 2
  | _ => false

theorem shutdown_operand_opcode {operation : NativeOperation} {descriptor : UInt64}
    (operand : NativeReadShutdown operation descriptor) : readShutdownOpcode operation = true := by
  cases operand with
  | shutdown descriptor how reading => rcases reading with zero | both <;> simp [readShutdownOpcode, *]

theorem read_shutdown_opcode {tick : ActorTick runtime} {current following : NativeProcesses}
    {call : NativeCallAt native tick current following} {object : ObjectId}
    (shutdown : NativeEndpointShutdown call object) : readShutdownOpcode call.operation = true := by
  cases shutdown with
  | shutdown descriptor handle operand input endpoint => exact shutdown_operand_opcode operand

theorem native_shutdown_operand_unique {operation : NativeOperation} {first last : UInt64}
    (left : NativeReadShutdown operation first) (right : NativeReadShutdown operation last) : first = last := by
  cases left <;> cases right <;> rfl

inductive NativeShutdownSource {tick : ActorTick runtime} {current following : NativeProcesses}
    (call : NativeCallAt native tick current following) (socket : SocketLifetime) : Type where
  | opcode (allowed : readShutdownOpcode call.operation = false) : NativeShutdownSource call socket
  | operand (descriptor : UInt64) (handle : Handle) (shutdown : NativeReadShutdown call.operation descriptor)
      (input : call.beforeReferences.handles descriptor = some handle) (outside : ¬ socket.matches handle) :
      NativeShutdownSource call socket
  | external (profile : ExternalEndpointOperands call socket.object) : NativeShutdownSource call socket

structure SocketShutdown {tick : ActorTick runtime} {current following : NativeProcesses}
    (call : NativeCallAt native tick current following) (socket : SocketLifetime) where
  descriptor : UInt64
  handle : Handle
  operand : NativeReadShutdown call.operation descriptor
  input : call.beforeReferences.handles descriptor = some handle
  identity : socket.matches handle

theorem socket_shutdown_excluded {tick : ActorTick runtime} {current following : NativeProcesses}
    {call : NativeCallAt native tick current following} {socket : SocketLifetime}
    (source : NativeShutdownSource call socket) (shutdown : SocketShutdown call socket) : False := by
  cases source with
  | opcode allowed =>
    have actual : NativeEndpointShutdown call socket.object :=
      .shutdown shutdown.descriptor shutdown.handle shutdown.operand shutdown.input shutdown.identity.1
    have impossible := read_shutdown_opcode actual
    rw [allowed] at impossible
    cases impossible
  | operand descriptor handle operand input outside =>
    have same := native_shutdown_operand_unique shutdown.operand operand
    have selected := shutdown.input
    rw [same, input] at selected
    have equal := Option.some.inj selected
    exact outside (equal ▸ shutdown.identity)
  | external profile =>
    exact profile shutdown.descriptor shutdown.handle (shutdown_private_operand shutdown.operand) shutdown.input shutdown.identity.1

inductive SocketResidualReadOrigin (position : Nat)
    {first last : Processes} {current following : NativeProcesses} {tick : ActorTick runtime}
    (row : NativeExternalStep process child native hostUid first current tick last following)
    (socket : SocketLifetime) (additional : Prop) : Type 1 where
  | native (call : NativeCallAt native tick current following) (stored : embeddedNative row = some call)
      (read : NativeResidualRead call socket.object) (description : read.handle.description = socket.description) :
      SocketResidualReadOrigin position row socket additional
  | engine (entry : EngineReadEntry ticks pair) (began : entry.position ≤ position) (identity : socket.matches entry.handle) :
      SocketResidualReadOrigin position row socket additional
  | additional (observed : additional) : SocketResidualReadOrigin position row socket additional

inductive SocketResidualDiscardOrigin (position : Nat)
    {first last : Processes} {current following : NativeProcesses} {tick : ActorTick runtime}
    (row : NativeExternalStep process child native hostUid first current tick last following)
    (snapshot : SocketReferenceSnapshot) (socket : SocketLifetime) (additional : Prop) : Type 1 where
  | read (cause : SocketResidualReadOrigin (ticks := ticks) (pair := pair) position row socket additional) :
      SocketResidualDiscardOrigin position row snapshot socket additional
  | shutdown (call : NativeCallAt native tick current following) (stored : embeddedNative row = some call)
      (operand : SocketShutdown call socket) : SocketResidualDiscardOrigin position row snapshot socket additional
  | lastReference (released : snapshot.released socket) : SocketResidualDiscardOrigin position row snapshot socket additional

-- §AR-host-boundary.primitives: A raw residual effect identifies its actual
-- input socket reference and cause at this stored row. Its source still has
-- to exclude additional SDK/child/foreign readers; none are silently dropped.
structure SocketResidualRuntime
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    (primitive : Primitive process child native hostUid before after callers next ticks pair Token)
    (references : SocketReferenceRuntime process child native hostUid)
    {first last : SocketReferenceSnapshot} (recording : SocketReferenceRecording references journal first last)
    (socket : SocketLifetime) (additional : Nat → SocketLifetime → Prop) : Prop where
  read : ∀ position
    (point : SelectedNativeCut process child native hostUid before after callers next ticks position),
    selectNativeCut journal position = some point → ∀ current following,
    SocketReferenceRecording.at references recording position = some (current, following) → ∀ bytes initial final,
    primitive.other position (.read .caller bytes) initial final →
    current.held socket ∧ Nonempty (SocketResidualReadOrigin (ticks := ticks) (pair := pair) position
      point.cut.current socket (additional position socket))
  discard : ∀ position
    (point : SelectedNativeCut process child native hostUid before after callers next ticks position),
    selectNativeCut journal position = some point → ∀ current following,
    SocketReferenceRecording.at references recording position = some (current, following) → ∀ bytes initial final,
    primitive.other position (.discard .caller bytes) initial final →
    current.held socket ∧ Nonempty (SocketResidualDiscardOrigin (ticks := ticks) (pair := pair) position
      point.cut.current following socket (additional position socket))

end LeanCage.Host.PrivateStreams
