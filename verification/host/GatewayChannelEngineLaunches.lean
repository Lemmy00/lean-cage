import GatewayChannelOFDReferences
import GatewayChannelBirths
import FilesystemNativeHandoff

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

def SocketTableAbsent (socket : SocketLifetime) (references : UInt64 → Option Handle) : Prop :=
  ∀ descriptor handle, references descriptor = some handle → ¬ socket.matches handle

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)}

-- §FS-host-boundary.ownership: Both endpoint orientations come from actual
-- pair births in this one journal. Another invocation's fresh pair cannot
-- name the original caller endpoint; neither can its peer at the same birth.
theorem actual_pair_peer_not_caller (lifetimes : LifetimeContract runtime)
    (namespaceLaws : NativeNamespaceContract native)
    {initial : World} {final : Population} (source : ActorJournal runtime (Population.empty initial) ticks final)
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    {original other : Pair}
    (first : PairBirthEntry process child native hostUid before after callers next ticks original)
    (last : PairBirthEntry process child native hostUid before after callers next ticks other)
    (firstActual : ActualPairBirth journal first) (lastActual : ActualPairBirth journal last) :
    other.engine ≠ original.caller := by
  by_cases same : first.position = last.position
  · have objects := actual_same_position_pair journal first last firstActual lastActual same
    intro equal
    exact original.separate (equal.symm.trans objects.2.symm)
  · exact Ne.symm (distinct_pair_endpoints_separate lifetimes namespaceLaws source first last same .caller .engine)

theorem raw_reference_channel_object (references : NativeReferences) (data control : Nat)
    (evidence : NativeChannels.Evidence (NativeCode.encodeReferences references) data control)
    (descriptor : UInt64) (handle : Handle) (present : references.rawProjection.handles descriptor = some handle) :
    handle.object = data ∨ handle.object = control := by
  rcases evidence with ⟨input, output, cancellation, inputFlag, outputFlag, cancellationFlag, separate⟩
  by_cases zero : descriptor = 0
  · subst descriptor
    have full : references.handles 0 = some handle := present
    have observed := input
    simp only [NativeChannels.encoded_object_at, show 0 < 2 ^ 64 by decide, ↓reduceIte,
      show UInt64.ofNat 0 = 0 by rfl, full, Option.map_some, Option.some.injEq] at observed
    exact .inl observed
  · by_cases one : descriptor = 1
    · subst descriptor
      have full : references.handles 1 = some handle := present
      have observed := output
      simp only [NativeChannels.encoded_object_at, show 1 < 2 ^ 64 by decide, ↓reduceIte,
        show UInt64.ofNat 1 = 1 by rfl, full, Option.map_some, Option.some.injEq] at observed
      exact .inl observed
    · by_cases three : descriptor = 3
      · subst descriptor
        have full : references.handles 3 = some handle := present
        have observed := cancellation
        simp only [NativeChannels.encoded_object_at, show 3 < 2 ^ 64 by decide, ↓reduceIte,
          show UInt64.ofNat 3 = 3 by rfl, full, Option.map_some, Option.some.injEq] at observed
        exact .inr observed
      · have absent := native_raw_other_absent references descriptor zero one three
        rw [absent] at present
        cases present

def embeddedHandoff {first last : Processes} {current following : NativeProcesses} {tick : ActorTick runtime}
    (row : NativeExternalStep process child native hostUid first current tick last following) :
    Option (NativeHandoffAt tick current) :=
  match row with
  | .launch _ handoff => some handoff
  | _ => none

-- §AR-host-boundary.interfaces.gateway: The source-built exec observations
-- are attached to the actual stored handoff and actual pair births. Full
-- references, including stderr/SDK slots, remain in handoff.execution.
structure EngineSourceChannels
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    {tick : ActorTick runtime} {current : NativeProcesses} (handoff : NativeHandoffAt tick current) where
  data : Pair
  control : Pair
  dataBirth : PairBirthEntry process child native hostUid before after callers next ticks data
  controlBirth : PairBirthEntry process child native hostUid before after callers next ticks control
  actualData : ActualPairBirth journal dataBirth
  actualControl : ActualPairBirth journal controlBirth
  evidence : NativeChannels.Evidence (NativeCode.encodeReferences handoff.execution.references) data.engine control.engine

-- This is a receipt family, not a platform role label. Each handoff's pure
-- evidence must be produced by its actual C/SDK source-plan consumer.
def EngineChannelRows
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next) : Prop :=
  ∀ position (point : SelectedNativeCut process child native hostUid before after callers next ticks position),
    selectNativeCut journal position = some point → ∀ handoff,
    embeddedHandoff point.cut.current = some handoff → Nonempty (EngineSourceChannels journal handoff)

theorem source_channels_exclude_caller (lifetimes : LifetimeContract runtime)
    (namespaceLaws : NativeNamespaceContract native)
    {initial : World} {final : Population} (source : ActorJournal runtime (Population.empty initial) ticks final)
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    {original : Pair} (birth : PairBirthEntry process child native hostUid before after callers next ticks original)
    (actual : ActualPairBirth journal birth)
    {tick : ActorTick runtime} {current : NativeProcesses} {handoff : NativeHandoffAt tick current}
    (channels : EngineSourceChannels journal handoff) :
    ∀ descriptor handle, handoff.execution.references.rawProjection.handles descriptor = some handle →
      handle.object ≠ original.caller := by
  intro descriptor handle present
  have data := actual_pair_peer_not_caller lifetimes namespaceLaws source journal birth channels.dataBirth actual channels.actualData
  have control := actual_pair_peer_not_caller lifetimes namespaceLaws source journal birth channels.controlBirth actual channels.actualControl
  rcases raw_reference_channel_object handoff.execution.references _ _ channels.evidence descriptor handle present with object | object
  · exact object ▸ data
  · exact object ▸ control

end LeanCage.Host.PrivateStreams
