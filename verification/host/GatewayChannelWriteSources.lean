import GatewayStreamEngineChunks
import GatewayResponseAckBytes

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)} {pair : Pair} {Token : Type}

-- §FS-host-boundary.ownership: These are per-source-entry process, endpoint
-- orientation and OFD identities from the same actual channel family. They
-- contain no payload/response, queue, read exclusivity or whole-helper result.
structure ChannelWriteSources
    (primitive : Primitive process child native hostUid before after callers next ticks pair Token)
    (actor : ActorId) (description : DescriptionId) : Prop where
  engine : ∀ entry token, primitive.enteredEngine token entry →
    entry.actor = actor ∧ entry.sender = .engine ∧ entry.handle.description = description
  native : ∀ entry token, primitive.enteredNative token entry → entry.sender = .caller

theorem ObservedStep.channel_writer_bytes
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {actor : ActorId} {description : DescriptionId} (sources : ChannelWriteSources primitive actor description)
    {position : Nat} {initial final : PhysicalState} {record : Record}
    (step : ObservedStep primitive initial record final) (ordered : position ≤ record.position)
    (registered : Registered primitive position initial) :
    record.actions.flatMap (written .caller) = (record.engineChunk actor).toList.flatMap Prod.snd := by
  cases step with
  | engine | native | read | birth => rfl
  | observation position inside token current state initial final reply stored live actual => cases reply <;> rfl
  | other position inside state action final actual =>
    have noWrite := (primitive.otherLaw _ _ _ _ actual).2.1
    cases action <;> try rfl
    next sender bytes => exact False.elim (noWrite sender bytes rfl)
  | commit position inside token current state initial final extent stored live actual =>
    have origin := registered _ current stored
    generalize keyIdentity : (primitive.input token).1 = key at origin
    generalize inputIdentity : current.input = input at origin
    cases origin with
    | engine entry sourceToken entered earlier =>
      obtain ⟨sameActor, sender, ofd⟩ := sources.engine entry sourceToken entered
      simp only [EngineWriteEntry.description] at *
      simp [Record.engineChunk, Record.bytesFor, written, Side.peer, sameActor, sender, EngineWriteEntry.key]
    | native entry sourceToken entered earlier =>
      have sender := sources.native entry sourceToken entered
      simp only [NativeWriteEntry.description] at *
      simp [Record.engineChunk, written, Side.peer, sender, NativeWriteEntry.key, nativeKey]

-- §FS-host-boundary.caller: Every queue write toward the caller is exactly
-- one commit of the selected actual engine. Native request/cancellation sends
-- cannot be relabeled as reply bytes by choosing an equal descriptor number.
theorem actual_channel_writer_bytes
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {actor : ActorId} {description : DescriptionId} (sources : ChannelWriteSources primitive actor description)
    {position : Nat} {initial final : PhysicalState} {records : List Record}
    (journal : ObservedJournal primitive position initial records final)
    (registered : Registered primitive position initial) :
    (records.flatMap Record.actions).flatMap (written .caller) =
      (records.filterMap (Record.engineChunk actor)).flatMap Prod.snd := by
  induction journal with
  | nil => rfl
  | cons ordered actual tail ih =>
    have first := actual.channel_writer_bytes sources ordered registered
    have rest := ih (actual.registered ordered registered)
    simp only [List.flatMap_cons, List.flatMap_append, first]
    cases selected : Record.engineChunk actor _ <;> simp [selected, rest]

-- §FS-host-boundary.caller: The raw process/OFD placement is consumed by the
-- actual engine source classifier. An encoded-response premise is not part
-- of ChannelWriteSources; it is derived from this SAME source handoff/history.
theorem source_channel_engine_response
    (descriptors : DescriptorContract kernel) (introductions : DescriptionIntroductionContract kernel)
    (retirement : DescriptorRetirementContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (environment : InterferenceContract kernel)
    {initialWorld : World} {population : Population}
    (journal : ActorJournal runtime (Population.empty initialWorld) ticks population)
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    (actor : ActorId) (handle : Handle)
    (sources : ChannelWriteSources primitive actor handle.description)
    (tick : ActorTick runtime) (engine : EngineState)
    (history : SelectedActorHistory runtime initialWorld ticks tick actor engine)
    (inherited : history.launch.references 1 = some handle) (endpoint : handle.object = pair.engine)
    (entry : EngineWriteEntry ticks pair) (token : Token) (entered : primitive.enteredEngine token entry) :
    Nonempty (EngineResponse entry) := by
  obtain ⟨sameActor, sender, sameDescription⟩ := sources.engine entry token entered
  subst actor
  obtain ⟨current⟩ := actual_running_actor_history descriptors lifetimes references environment journal
    entry.selected entry.present entry.running
  have launch := selected_launch_references_unique journal current history
  have input : current.launch.references 1 = some handle := by rw [launch]; exact inherited
  apply engine_response_from_inherited descriptors introductions retirement sdk lifetimes references
    journal entry current 1 handle input
  · have selected : entry.handle.object = pair.engine := by simpa only [sender, Pair.endpoint] using entry.endpoint
    exact selected.trans endpoint.symm
  · exact sameDescription

end LeanCage.Host.PrivateStreams
