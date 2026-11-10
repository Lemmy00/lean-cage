import GatewayChannelExternalOperands
import GatewayChannelDiscards
import GatewayChannelReadJournal

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {tick : ActorTick runtime} {ticks : List (ActorTick runtime)} {pair : Pair} {Token : Type}

-- §AR-host-boundary.primitives: A flags-zero native recv is accounted by its
-- exact committed product in NativeReadRow. Filesystem reads and other recv
-- flags remain separate possible causes; they are not erased by an FD role.
structure NativeResidualRead (call : NativeCallAt native tick callers next) (object : ObjectId) where
  descriptor : UInt64
  handle : Handle
  input : call.beforeReferences.handles descriptor = some handle
  endpoint : handle.object = object
  operation : (∃ request, call.operation = .vfs (.adapted request) ∧ request.op = .read ∧ request.third = 0 ∧ request.first = descriptor) ∨
    ∃ extent flags, call.operation = .receive descriptor extent flags ∧ flags ≠ 0

structure ActorStreamRead (tick : ActorTick runtime) (object : ObjectId) where
  source : ActorEndpointRead tick object
  stream : source.request.third = 0

inductive ResidualReadOrigin
    (row : NativeExternalStep process child native hostUid before callers tick after next)
    (additional : Prop) (object : ObjectId) : Type 1 where
  | native (call : NativeCallAt native tick callers next) (stored : embeddedNative row = some call)
      (read : NativeResidualRead call object) : ResidualReadOrigin row additional object
  | actor (read : ActorStreamRead tick object) : ResidualReadOrigin row additional object
  | additional (observed : additional) : ResidualReadOrigin row additional object

inductive ResidualDiscardOrigin
    (row : NativeExternalStep process child native hostUid before callers tick after next)
    (support : NativeToken → UInt64 → Option Handle) (additional : Prop) (object : ObjectId) : Type 1 where
  | read (cause : ResidualReadOrigin row additional object) : ResidualDiscardOrigin row support additional object
  | shutdown (call : NativeCallAt native tick callers next) (stored : embeddedNative row = some call)
      (operand : NativeEndpointShutdown call object) : ResidualDiscardOrigin row support additional object
  | lastReference (released : NoEndpointReference tick.after next support object) :
      ResidualDiscardOrigin row support additional object

-- This adapter partitions effects of the SAME raw operation. It is a
-- per-operation observation law; the canonical recv is processed once.
-- Additional SDK/child/foreign readers remain an explicit observed cause.
-- Their individual source/authority producer must exclude that separate case.
structure ResidualKernelEffects
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    (primitive : Primitive process child native hostUid before after callers next ticks pair Token)
    (support : Nat → NativeToken → UInt64 → Option Handle)
    (additional : Nat → ObjectId → Prop) : Prop where
  read : ∀ position
    (point : SelectedNativeCut process child native hostUid before after callers next ticks position),
    selectNativeCut journal position = some point → ∀ bytes initial final,
    primitive.other position (.read .caller bytes) initial final →
    Nonempty (ResidualReadOrigin point.cut.current (additional position pair.caller) pair.caller)
  discard : ∀ position
    (point : SelectedNativeCut process child native hostUid before after callers next ticks position),
    selectNativeCut journal position = some point → ∀ bytes initial final,
    primitive.other position (.discard .caller bytes) initial final →
    Nonempty (ResidualDiscardOrigin point.cut.current (support position) (additional position pair.caller) pair.caller)

-- §AR-host-boundary.interfaces.gateway: Actual source operands with recv
-- flags zero are permitted reads. Their bytes have already been counted;
-- they do not justify an additional hidden read or discard of later bytes.
theorem NativeResidualRead.input_operand
    {call : NativeCallAt native tick callers next} {object : ObjectId}
    (read : NativeResidualRead call object) : NativeReadOperand call.operation read.descriptor := by
  rcases read.operation with ⟨request, operation, reading, stream, descriptor⟩ | ⟨extent, flags, operation, _⟩
  · rw [operation, ← descriptor]
    exact .adapted request reading
  · rw [operation]
    exact .receive ..

theorem external_excludes_residual_read
    (call : NativeCallAt native tick callers next) (object : ObjectId)
    (profile : ExternalEndpointOperands call object) : ¬ Nonempty (NativeResidualRead call object) := by
  rintro ⟨read⟩
  exact profile read.descriptor read.handle (.read read.input_operand) read.input read.endpoint

theorem native_receive_zero_excludes_residual_read
    (call : NativeCallAt native tick callers next) (descriptor extent : UInt64)
    (operation : call.operation = .receive descriptor extent 0) (object : ObjectId) :
    ¬ Nonempty (NativeResidualRead call object) := by
  rintro ⟨read⟩
  rcases read.operation with ⟨request, actual, reading, stream, atDescriptor⟩ | ⟨actualExtent, flags, actual, nonzero⟩
  · rw [operation] at actual
    cases actual
  · rw [operation] at actual
    obtain ⟨_, _, identity⟩ := NativeOperation.receive.inj actual
    exact nonzero identity.symm

-- No-read opcodes are a source fact about one operation, not a callback or
-- a complete invocation. The actual SDK/source producer supplies the opcode.
theorem native_no_read_excludes_residual_read
    (call : NativeCallAt native tick callers next) (object : ObjectId)
    (operation : ∀ descriptor, ¬ NativeReadOperand call.operation descriptor) :
    ¬ Nonempty (NativeResidualRead call object) := by
  rintro ⟨read⟩
  exact operation read.descriptor read.input_operand

theorem residual_read_excluded
    (row : NativeExternalStep process child native hostUid before callers tick after next)
    (additional : Prop) (object : ObjectId)
    (nativeRead : ∀ call, embeddedNative row = some call → ¬ Nonempty (NativeResidualRead call object))
    (actorRead : ¬ Nonempty (ActorStreamRead tick object)) (other : ¬ additional) :
    ¬ Nonempty (ResidualReadOrigin row additional object) := by
  rintro ⟨read⟩
  cases read with
  | native call stored read => exact nativeRead call stored ⟨read⟩
  | actor read => exact actorRead ⟨read⟩
  | additional observed => exact other observed

theorem residual_discard_excluded
    (row : NativeExternalStep process child native hostUid before callers tick after next)
    (support : NativeToken → UInt64 → Option Handle) (additional : Prop) (object : ObjectId)
    (process : NativeToken) (table : NativeReferences) (descriptor : UInt64) (handle : Handle)
    (current : next.references process = some table) (held : table.handles descriptor = some handle)
    (endpoint : handle.object = object)
    (nativeRead : ∀ call, embeddedNative row = some call → ¬ Nonempty (NativeResidualRead call object))
    (actorRead : ¬ Nonempty (ActorStreamRead tick object)) (other : ¬ additional)
    (shutdown : ∀ call, embeddedNative row = some call → ¬ NativeEndpointShutdown call object) :
    ¬ Nonempty (ResidualDiscardOrigin row support additional object) := by
  rintro ⟨cause⟩
  cases cause with
  | read cause => exact residual_read_excluded row additional object nativeRead actorRead other ⟨cause⟩
  | shutdown call stored operand => exact shutdown call stored operand
  | lastReference released =>
    exact retained_native_reference_excludes_last_drop tick.after next support process table descriptor handle current held
      (by simpa only [endpoint] using released)

end LeanCage.Host.PrivateStreams
