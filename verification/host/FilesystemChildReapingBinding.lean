import FilesystemChildReapingSource

namespace LeanCage.Host.Kernel
open Filesystem PrivateStreams

structure SelectedSdkObservation {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {β : Type} {effect : Effect β} {reply : β}
    {before after : Processes} {first last : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid before first all after last)
    (observation : PrimitiveObservationAt runtime initial all tick actor engine effect reply) where
  position : Nat
  selected : SelectedNativeCut process child native hostUid before after first last all position
  same : selectNativeCut recording position = some selected
  occurs : all[position]? = some selected.tick
  input : EngineState
  present : selected.tick.before.actors actor = some input
  ordinal : input.events.length = observation.rawBefore.length
  action : selected.tick.action = .returned actor effect reply

-- §AR-host-boundary.primitives: Select the SDK occurrence from the SAME
-- native/child journal value, retaining its actual process tables and source
-- ordinal rather than reconstructing another call on an equal tick.
theorem selected_sdk_observation {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {β : Type} {effect : Effect β} {reply : β}
    {before after : Processes} {first last : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid before first all after last)
    (observation : PrimitiveObservationAt runtime initial all tick actor engine effect reply) :
    Nonempty (SelectedSdkObservation recording observation) := by
  obtain ⟨position, actualTick, input, output, atTick, action, present, afterPresent,
    ordinal, beforeWorld, afterWorld⟩ := observation.sampled
  obtain ⟨cut, same⟩ := selectNativeCut_exists recording atTick
  exact ⟨⟨position, ⟨actualTick, cut⟩, same, atTick, input, present, ordinal, action⟩⟩

structure ValidatorReapingBinding {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {before after : Processes} {first last : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid before first all after last)
    (bundle : Validation.Bundle) (raw : ByteArray) (context : ValidatorPrefixCuts.Observed bundle raw)
    (position : Nat) where
  value : Validation.ValidatorChild
  status : UInt32
  returned : context.spawned.child = .ok value
  observations : OrderedPrimitiveObservations runtime initial all tick actor engine
    (.spawn (Validation.validatorArguments bundle
      (context.spawned.written.allocated.directory.path ++ "/policy.json"))) (.ok value)
    (.wait value) (.ok status)
  spawning : SelectedSdkObservation recording observations.first
  waiting : SelectedSdkObservation recording observations.second
  lease : SpawnedChildLease process all
    (Validation.validatorArguments bundle (context.spawned.written.allocated.directory.path ++ "/policy.json")) value
  sourceActor : lease.actor = actor
  sourceBirth : lease.birth.position = spawning.position
  sourceTick : lease.birth.tick = spawning.selected.tick
  sourceBefore : lease.birth.before = spawning.selected.cut.priorProcesses
  sourceAfter : lease.birth.after = spawning.selected.cut.nextProcesses
  sourceOrdinal : lease.engine.events.length = observations.first.rawBefore.length
  ordered : spawning.position < waiting.position
  earlier : waiting.position < position
  use : ReapingUse lease waiting.selected.tick.action

-- §FS-host-boundary.ownership: The cleanup branch's actual source observation
-- produces one ordered spawn/Child/wait binding on the SAME global recording.
-- SDK opaque-lease capture remains a one-operation primitive observation.
theorem actual_validator_reaping_binding {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {before after : Processes} {first last : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid before first all after last)
    {position : Nat} {tick : ActorTick runtime} (selected : all[position]? = some tick)
    {actor : ActorId} {engine : EngineState} (present : tick.before.actors actor = some engine)
    {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    {bundle : Validation.Bundle} {raw : ByteArray} (context : ValidatorPrefixCuts.Observed bundle raw)
    (reaped : context.result.reaped = true) {outer inside : List Program.Event}
    (trace : adapter.occurrence.logicalBefore = outer ++ context.events ++ inside) :
    Nonempty (ValidatorReapingBinding recording bundle raw context position (actor := actor) (engine := engine)
      (initial := initial) (tick := tick)) := by
  obtain ⟨value, status, returned, ⟨observations⟩⟩ := validator_reaping_observations adapter context reaped trace
  obtain ⟨spawning⟩ := selected_sdk_observation recording observations.first
  obtain ⟨waiting⟩ := selected_sdk_observation recording observations.second
  obtain ⟨lease, birthPosition, birthTick, owner, birthBefore, birthAfter⟩ :=
    spawned_child_lease_from_head spawning.selected.cut.current spawning.occurs spawning.action
  have leasePresent := lease.present
  rw [birthTick, owner] at leasePresent
  have sameInput : lease.engine = spawning.input := Option.some.inj (leasePresent.symm.trans spawning.present)
  have firstEarlier : spawning.input.events.length < waiting.input.events.length := by
    rw [spawning.ordinal, waiting.ordinal]
    exact observations.earlier
  have waitEarlier : waiting.input.events.length < engine.events.length := by
    rw [waiting.ordinal]
    have length := congrArg List.length observations.second.trace
    simp only [List.length_append, List.length_cons] at length
    omega
  refine ⟨{
    value
    status
    returned
    observations
    spawning
    waiting
    lease
    sourceActor := owner
    sourceBirth := birthPosition
    sourceTick := birthTick
    sourceBefore := birthBefore
    sourceAfter := birthAfter
    sourceOrdinal := (congrArg (fun input : EngineState => input.events.length) sameInput).trans spawning.ordinal
    ordered := source_ordinal_orders_positions journal spawning.occurs waiting.occurs actor
      spawning.input waiting.input spawning.present waiting.present firstEarlier
    earlier := source_ordinal_orders_positions journal waiting.occurs selected actor waiting.input engine
      waiting.present present waitEarlier
    use := ?_ }⟩
  rw [waiting.action, ← owner]
  exact ReapingUse.wait status

-- §FS-host-boundary.ownership: Primitive capture identifies this source lease
-- at its exact successful wait; the application then derives no later child
-- use after cleanup, independently of PID reuse or subsequent request names.
theorem ValidatorReapingBinding.no_later_child {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {laws : ChildLifecycleContract process child native hostUid}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {before after : Processes} {first last : NativeProcesses}
    {recording : NativeExternalJournal process child native hostUid before first all after last}
    {bundle : Validation.Bundle} {raw : ByteArray} {context : ValidatorPrefixCuts.Observed bundle raw} {position : Nat}
    (source : ValidatorReapingBinding recording bundle raw context position (actor := actor) (engine := engine)
      (initial := initial) (tick := tick))
    {prior final : ReapedChildren} (lifetimes : ChildLifecycleJournal laws recording prior final)
    (captured : laws.usesLease source.waiting.selected.cut.current source.lease.key) :
    source.waiting.selected.cut.last.NoChildToken source.lease.token ∧ final source.lease.token = true :=
  actual_reaping_excludes_child_tail lifetimes source.waiting.selected source.waiting.same source.lease captured source.use

end LeanCage.Host.Kernel
