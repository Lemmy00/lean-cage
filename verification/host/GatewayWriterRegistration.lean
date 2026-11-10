import GatewayWriterSynchronizationComplete

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)} {pair : Pair} {Token : Type}

-- §AR-host-boundary.interfaces.gateway: This pure call-key adapter registers
-- an actual source head. It supplies no kernel progress, return or response;
-- those remain observations of the individual operation.
structure EngineTokens
    (primitive : Primitive process child native hostUid before after callers next ticks pair Token) where
  token : EngineWriteEntry ticks pair → Token
  entered : ∀ entry, primitive.enteredEngine (token entry) entry

structure EngineRegistration
    (primitive : Primitive process child native hostUid before after callers next ticks pair Token)
    (position : Nat) (tick : ActorTick runtime) (initial : PhysicalState) where
  final : PhysicalState
  records : List Record
  actual : ObservedJournal primitive position initial records final
  positions : ∀ record ∈ records, record.position = position
  pending : ∀ record ∈ records, pendingRecord record
  outside : ∀ observation, writeObservationAt tick = some observation → final.ledger observation.key = none →
    OutsidePair pair tick observation

-- §FS-host-boundary.caller: Registration is constructed from the actual raw
-- source head and descriptor snapshot. A private write/loss cannot be skipped
-- by claiming its call key absent; no ACK count or future writer is assumed.
theorem actual_engine_registration
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    (tokens : EngineTokens primitive) {position : Nat} {tick : ActorTick runtime}
    (selectedTick : ticks[position]? = some tick) (initial : PhysicalState) :
    Nonempty (EngineRegistration primitive position tick initial) := by
  classical
  cases scan : writeObservationAt tick with
  | none =>
    exact ⟨⟨initial, [], .nil _ _, by simp, by simp, by
      intro observation selected absent; rw [scan] at selected; cases selected⟩⟩
  | some observation =>
    cases stored : initial.ledger observation.key with
    | some current =>
      exact ⟨⟨initial, [], .nil _ _, by simp, by simp, by
        intro other selected absent
        have same := Option.some.inj (scan.symm.trans selected)
        subst other
        rw [stored] at absent
        cases absent⟩⟩
    | none =>
      obtain ⟨engine, present, ordinal, writing, observed⟩ := write_observation_fields tick observation scan
      obtain ⟨original, next, originalPresent, running, head⟩ :=
        actual_filesystem_observation_head tick.operation observation.actor observation.request observation.reply observed
      have identity := Option.some.inj (present.symm.trans originalPresent)
      subst original
      have build : ∀ handle side, engine.references observation.request.first = some handle →
          handle.object = pair.endpoint side → Nonempty (EngineRegistration primitive position tick initial) := by
        intro handle side input endpoint
        let entry : EngineWriteEntry ticks pair := {
          position, tick, selected := selectedTick, actor := observation.actor, engine, present, running,
          request := observation.request, next, head, writing, sender := side, handle, input, endpoint }
        have key : entry.key = observation.key := by
          simp only [EngineWriteEntry.key, WriteObservation.key, entry, ordinal]
        have fresh : initial.ledger entry.key = none := by rw [key]; exact stored
        let middle : PhysicalState :=
          { initial with ledger := initial.ledger.set entry.key ⟨entry.description, 0, Nat.zero_le _, .pending⟩ }
        refine ⟨⟨middle, [⟨position, .begin entry.key entry.description, []⟩],
          .cons (Nat.le_refl _) (.engine initial entry (tokens.token entry) (tokens.entered entry) fresh) (.nil _ _),
          ?_, ?_, ?_⟩⟩
        · intro record member; cases List.mem_singleton.mp member; rfl
        · intro record member; cases List.mem_singleton.mp member; exact True.intro
        · intro other selected absent
          have same := Option.some.inj (scan.symm.trans selected)
          subst other
          simp only [middle, Ledger.set, key, ite_true] at absent
          cases absent
      cases input : engine.references observation.request.first with
      | none =>
        refine ⟨⟨initial, [], .nil _ _, by simp, by simp, ?_⟩⟩
        intro other selected absent current currentAt handle currentInput
        have same := Option.some.inj (scan.symm.trans selected)
        subst other
        have source := Option.some.inj (present.symm.trans currentAt)
        subst current
        rw [input] at currentInput
        cases currentInput
      | some handle =>
        by_cases caller : handle.object = pair.caller
        · exact build handle .caller input caller
        · by_cases engineSide : handle.object = pair.engine
          · exact build handle .engine input engineSide
          · refine ⟨⟨initial, [], .nil _ _, by simp, by simp, ?_⟩⟩
            intro other selected absent current currentAt actual currentInput
            have same := Option.some.inj (scan.symm.trans selected)
            subst other
            have source := Option.some.inj (present.symm.trans currentAt)
            subst current
            have sameHandle := Option.some.inj (input.symm.trans currentInput)
            subst actual
            exact ⟨caller, engineSide⟩

-- Later actual pending progress cannot delete the just-registered key. Thus
-- the outside test at the ACK boundary is derived, not a channel-safety premise.
theorem EngineRegistration.outside_after
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {position : Nat} {tick : ActorTick runtime} {initial : PhysicalState}
    (registration : EngineRegistration primitive position tick initial)
    {boundary : Nat} {records : List Record} {final : PhysicalState}
    (progress : ObservedJournal primitive boundary registration.final records final) :
    ∀ observation, writeObservationAt tick = some observation → final.ledger observation.key = none →
      OutsidePair pair tick observation := by
  intro observation selected absent
  apply registration.outside observation selected
  cases stored : registration.final.ledger observation.key with
  | none => rfl
  | some current =>
    obtain ⟨last, present, input, increased, bytes⟩ := progress.key_bytes observation.key current stored
    rw [absent] at present
    cases present

end LeanCage.Host.PrivateStreams
