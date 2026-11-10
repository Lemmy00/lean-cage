import GatewayChannelReceives
import GatewayStreamSynchronization

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)} {pair : Pair}

-- §AR-host-boundary.interfaces.gateway: One canonical observation of the
-- exact native call stored in this journal. Every full descriptor slot is
-- retained; source invocation and reader custody are proved separately.
noncomputable def nativeReadAt
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    (position : Nat) : Option (NativeReadEntry process child native hostUid before after callers next ticks pair) :=
  match _selected : selectNativeCut journal position with
  | none => none
  | some point =>
    match stored : embeddedNative point.cut.current with
    | none => none
    | some call =>
      match operation : call.operation with
      | .receive descriptor extent flags =>
        match product : call.product with
        | .received bytes =>
          match input : call.beforeReferences.handles descriptor with
          | none => none
          | some handle =>
            let build (side : Side) (endpoint : handle.object = pair.endpoint side) :
                NativeReadEntry process child native hostUid before after callers next ticks pair := {
              position
              tick := point.tick
              cut := point.cut
              call
              embedded := stored
              code := NativeCode.encodeCall call
              interpreted := NativeCode.encode_call_exact call
              descriptor
              extent
              flags
              bytes
              operation
              product
              receiver := side
              handle
              input
              endpoint }
            if caller : handle.object = pair.caller then some (build .caller caller)
            else if engine : handle.object = pair.engine then some (build .engine engine)
            else none
        | _ => none
      | _ => none

theorem nativeReadAt_actual
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    (position : Nat) (entry : NativeReadEntry process child native hostUid before after callers next ticks pair)
    (selected : nativeReadAt journal position = some entry) :
    ActualNativeRead journal entry ∧ entry.position = position := by
  classical
  unfold nativeReadAt at selected
  split at selected
  next => cases selected
  next point atPoint =>
    split at selected
    next => cases selected
    next call stored =>
      split at selected
      all_goals try contradiction
      next descriptor extent flags operation =>
        split at selected
        all_goals try contradiction
        next bytes product =>
          split at selected
          next => cases selected
          next handle input =>
            split at selected
            · cases Option.some.inj selected
              exact ⟨atPoint, rfl⟩
            · split at selected
              · cases Option.some.inj selected
                exact ⟨atPoint, rfl⟩
              · cases selected

-- §AR-host-boundary.primitives: This actual kernel receive is consumed once
-- at its stored global row. It cannot be repeated or omitted by choosing a
-- second read witness for an equal tick.
inductive NativeReadRow
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    {Token : Type} (primitive : Primitive process child native hostUid before after callers next ticks pair Token)
    (position : Nat) (initial : PhysicalState) : List Record → PhysicalState → Type 1 where
  | outside (none : nativeReadAt (pair := pair) journal position = none) : NativeReadRow journal primitive position initial [] initial
  | received (entry : NativeReadEntry process child native hostUid before after callers next ticks pair)
      (selected : nativeReadAt journal position = some entry) (flags : entry.flags = 0)
      (before final : State) (live : initial.stream = some before)
      (actual : primitive.read entry before final) :
      NativeReadRow journal primitive position initial
        [⟨position, .channel (.read entry.receiver entry.bytes.data.toList), [.read entry.receiver entry.bytes.data.toList]⟩]
        { initial with stream := some final }

noncomputable def NativeReadRow.erase
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    {Token : Type} {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {position : Nat} {initial final : PhysicalState} {records : List Record}
    (row : NativeReadRow journal primitive position initial records final) :
    ObservedJournal primitive position initial records final := by
  cases row with
  | outside => exact .nil _ _
  | received entry selected flags before final live actual =>
    have atPosition := (nativeReadAt_actual journal position entry selected).2
    rw [← atPosition]
    exact .cons (Nat.le_refl _) (.read entry initial before final live flags actual) (.nil _ _)

end LeanCage.Host.PrivateStreams
