import GatewayChannelPairSource
import GatewayChannelCode

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

-- §AR-host-boundary.interfaces.gateway: Convert the actual allocated handles
-- to shared source data. The C entry producer supplies the invocation binding;
-- field consistency supplies no trusted origin or exclusive-access conclusion.
theorem pair_use_consistent {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {native : NativePrimitive kernel} {tick : ActorTick runtime} {before after : NativeProcesses}
    {ipc : ObjectId → Prop} {call : NativeCallAt native tick before after} {first second : UInt64}
    (allocation : PairAllocation ipc call first second)
    (invocation : ChannelCode.Invocation) (formed : invocation.WellFormed)
    (position : Nat) (kind : ChannelCode.PairKind)
    (process : call.token = invocation.key.process) (ordered : invocation.key.entryPosition ≤ position)
    (operation : call.operation = .socketPair 1 526337 0) (product : call.product = .socketPair first second) :
    ∃ use : ChannelCode.PairUse, use.Consistent ∧ use.invocation = invocation ∧ use.kind = kind ∧
      use.position = position ∧ use.row = NativeCode.encodeCall call ∧
      use.leftObject = allocation.left.object ∧ use.rightObject = allocation.right.object := by
  let use : ChannelCode.PairUse := {
    invocation, kind, position
    row := NativeCode.encodeCall call
    leftFd := first.toNat
    rightFd := second.toNat
    leftObject := allocation.left.object
    rightObject := allocation.right.object
    leftDescription := allocation.left.description
    rightDescription := allocation.right.description }
  refine ⟨use, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨formed, process, ordered, ?_, ?_, allocation.leftBound, allocation.rightBound,
    ?_, allocation.objectsSeparate, allocation.descriptionsSeparate, ?_, ?_, ?_, ?_⟩
  · change NativeCode.encodeOperation call.operation = .socketPair 1 526337 0
    rw [operation]
    rfl
  · change NativeCode.encodeProduct call.product = .socketPair first.toNat second.toNat
    rw [product]
    rfl
  · intro same
    exact allocation.slotsSeparate (UInt64.toNat_inj.mp same)
  · refine ⟨NativeCode.encodeHandle allocation.left, ?_, rfl, rfl⟩
    simp only [use, NativeCode.encodeCall, NativeCode.encodeReferences, UInt64.toNat_lt, ↓reduceIte,
      UInt64.ofNat_toNat, allocation.leftOutput, Option.map_some]
  · refine ⟨NativeCode.encodeHandle allocation.right, ?_, rfl, rfl⟩
    simp only [use, NativeCode.encodeCall, NativeCode.encodeReferences, UInt64.toNat_lt, ↓reduceIte,
      UInt64.ofNat_toNat, allocation.rightOutput, Option.map_some]
  · simpa only [use, NativeCode.encodeCall, NativeCode.encodeReferences, UInt64.toNat_lt,
      ↓reduceIte, UInt64.ofNat_toNat] using allocation.leftCloseExec
  · simpa only [use, NativeCode.encodeCall, NativeCode.encodeReferences, UInt64.toNat_lt,
      ↓reduceIte, UInt64.ofNat_toNat] using allocation.rightCloseExec

end LeanCage.Host.PrivateStreams
