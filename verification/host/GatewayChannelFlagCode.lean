import GatewayChannelFlagEffects
import GatewayChannelAuthorityCode

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

-- §AR-host-boundary.interfaces.gateway: The complete encoded table preserves
-- alias flags, including support slots, with no three-descriptor projection.
theorem aliases_code (references : NativeReferences) (object : ObjectId)
    (actual : AliasesCloseExec object references) :
    ChannelCode.AliasesCloseExec (NativeCode.encodeReferences references) object := by
  intro fd handle selected same
  by_cases bounded : fd < 2 ^ 64
  · simp only [NativeCode.encodeReferences, bounded, ↓reduceIte] at selected ⊢
    cases current : references.handles (UInt64.ofNat fd) with
    | none => simp only [current, Option.map_none] at selected; cases selected
    | some original =>
      have identity : NativeCode.encodeHandle original = handle := by
        simpa only [current, Option.map_some, Option.some.injEq] using selected
      have object : original.object = object := (congrArg NativeCode.Handle.object identity).trans same
      exact actual _ original current object
  · simp only [NativeCode.encodeReferences, bounded, ↓reduceIte] at selected
    cases selected

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel} {native : NativePrimitive kernel}
  {tick : ActorTick runtime} {before after : NativeProcesses}

theorem actual_input_alias_code (call : NativeCallAt native tick before after) (object : ObjectId)
    (code : NativeCode.CallRow) (interpreted : NativeCode.Interprets code call)
    (initial : NativeAliasesCloseExec object before) :
    ChannelCode.AliasesCloseExec code.beforeReferences object := by
  rw [interpreted.input]
  exact aliases_code call.beforeReferences object (initial call.token _ call.active call.inputTable)

theorem actual_output_alias_code (call : NativeCallAt native tick before after) (object : ObjectId)
    (code : NativeCode.CallRow) (interpreted : NativeCode.Interprets code call)
    (actual : AliasesCloseExec object call.afterReferences) :
    ChannelCode.AliasesCloseExec code.afterReferences object := by
  rw [interpreted.output]
  exact aliases_code call.afterReferences object actual

end LeanCage.Host.PrivateStreams
