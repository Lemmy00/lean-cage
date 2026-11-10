import FilesystemChildLifetimeCuts
import FilesystemPrimitiveObservations
import ValidationReapingProofs
import ValidatorPrefixCuts

namespace LeanCage.Host.Kernel
open Filesystem

structure OrderedPrimitiveObservations {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    (initial : World) (all : List (ActorTick runtime)) (tick : ActorTick runtime)
    (actor : ActorId) (engine : EngineState) {β γ : Type}
    (firstEffect : Effect β) (firstReply : β) (secondEffect : Effect γ) (secondReply : γ) where
  first : PrimitiveObservationAt runtime initial all tick actor engine firstEffect firstReply
  second : PrimitiveObservationAt runtime initial all tick actor engine secondEffect secondReply
  earlier : first.rawBefore.length < second.rawBefore.length

-- §FS-host-boundary.ownership: Split ONE actual lowering witness twice, retaining
-- source order and the same selected actor history. Equal-valued SDK results
-- never justify replacing either captured source occurrence.
theorem primitive_observations_ordered {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    {β γ : Type} {firstEffect : Effect β} {firstReply : β} {secondEffect : Effect γ} {secondReply : γ}
    {before between after : List Program.Event}
    (trace : adapter.occurrence.logicalBefore = before ++ .returned firstEffect firstReply ::
      (between ++ .returned secondEffect secondReply :: after))
    (firstIdentity : PrimitiveFilesystem.lowerEffect firstEffect = Program.effect firstEffect)
    (secondIdentity : PrimitiveFilesystem.lowerEffect secondEffect = Program.effect secondEffect) :
    Nonempty (OrderedPrimitiveObservations runtime initial all tick actor engine
      firstEffect firstReply secondEffect secondReply) := by
  obtain ⟨first⟩ := primitive_observation_chunked adapter trace firstIdentity
  obtain ⟨middleRaw, afterRaw, leadingChunks, afterChunks, rawTrace⟩ :=
    PrimitiveFilesystem.chunks_selected_identity first.chunks rfl secondIdentity
  let remaining := afterRaw ++ adapter.occurrence.inside.map Program.filesystemPrefixEvent
  have suffix : first.observation.rawAfter = middleRaw ++ .returned secondEffect secondReply :: remaining := by
    rw [first.suffix, rawTrace]
    simp only [List.append_assoc, List.cons_append, remaining]
  have tail := first.observation.tail
  rw [suffix] at tail
  obtain ⟨middle, leading, following⟩ := actor_with_split middleRaw _ tail
  obtain ⟨beforeSecond, afterSecond, environment, actual, sampled, final⟩ := actor_with_head following
  let beforeSecondEvents := first.observation.rawBefore ++ .returned firstEffect firstReply :: middleRaw
  have prefixHistory : ActorHistoryWith runtime actor (SourceReturnAt runtime all actor) 0
      (first.observation.source.launch.tick.after.project (.initialFrom (PrimitiveFilesystem.lower Entrypoint.run)
        first.observation.source.launch.references first.observation.source.launch.closeExec
        first.observation.source.launch.workingDirectory)) beforeSecondEvents beforeSecond := by
    apply actor_with_append first.observation.leading
    simpa only [Nat.zero_add, beforeSecondEvents, List.append_nil] using
      (ActorHistoryWith.returned first.observation.actual first.observation.sampled
        (actor_with_append leading environment))
  let second : PrimitiveObservationAt runtime initial all tick actor engine secondEffect secondReply := {
    source := first.observation.source
    rawBefore := beforeSecondEvents
    rawAfter := remaining
    trace := by
      rw [first.observation.trace, suffix]
      simp only [beforeSecondEvents, List.append_assoc, List.cons_append]
    before := beforeSecond
    after := afterSecond
    leading := prefixHistory
    actual
    sampled := by
      simpa only [beforeSecondEvents, List.length_append, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using sampled
    tail := by
      simpa only [beforeSecondEvents, List.length_append, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using final }
  exact ⟨⟨first.observation, second, by
    simp only [second, beforeSecondEvents, List.length_append, List.length_cons]
    omega⟩⟩

-- §FS-host-boundary.ownership: The genuine reaped validator branch retains
-- the actual returned Child from its own source spawn, followed by that same
-- value's successful wait. Rejection statuses are still successful reaping.
theorem validator_reaping_observations {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    {bundle : Validation.Bundle} {raw : ByteArray} (context : ValidatorPrefixCuts.Observed bundle raw)
    (reaped : context.result.reaped = true) {outer inside : List Program.Event}
    (trace : adapter.occurrence.logicalBefore = outer ++ context.events ++ inside) :
    ∃ child status,
      context.spawned.child = .ok child ∧
      Nonempty (OrderedPrimitiveObservations runtime initial all tick actor engine
        (.spawn (Validation.validatorArguments bundle
          (context.spawned.written.allocated.directory.path ++ "/policy.json"))) (.ok child)
        (.wait child) (.ok status)) := by
  obtain ⟨child, output, status, reading, returned, read, observedTrace, result⟩ :=
    Validation.observe_reaped_source raw context.spawned.child context.observe reaped
  have spawnTrace := PrimitiveFilesystem.effect_returns_singleton
    (.spawn (Validation.validatorArguments bundle
      (context.spawned.written.allocated.directory.path ++ "/policy.json"))) context.spawned.spawn
  rw [returned] at spawnTrace
  have actualTrace : adapter.occurrence.logicalBefore =
      (outer ++ context.spawned.written.events) ++
        .returned (.spawn (Validation.validatorArguments bundle
          (context.spawned.written.allocated.directory.path ++ "/policy.json"))) (.ok child) ::
        (reading ++ .returned (.wait child) (.ok status) :: inside) := by
    rw [trace]
    simp only [ValidatorPrefixCuts.Observed.events, ValidatorPrefixCuts.Spawned.events,
      spawnTrace, observedTrace, List.append_assoc, List.cons_append, List.nil_append]
    rfl
  exact ⟨child, status, returned, primitive_observations_ordered adapter actualTrace rfl rfl⟩

end LeanCage.Host.Kernel
