import FilesystemChildReapingBinding
import VirtualMachineProofs.ReapingSource
import ReceiveProofs
import RunPrefixCuts

namespace LeanCage.Host.Kernel
open Filesystem PrivateStreams

-- §FS-host-boundary.ownership: Transport/artifact projection never changes
-- the actual VM reaping observation used to authorize run-name cleanup.
theorem receive_cleanup_source (request : String) (bundle : Validation.Bundle) (preflight : Bool)
    (policy : Policy.Accepted) (vm : VirtualMachine.Result) :
    Snapshot.PostProgram (fun input => input.outcome.vmCleanup = vm.cleanup)
      (receive request bundle preflight policy vm) := by
  unfold receive
  dsimp only
  split
  · exact .pure rfl
  · split
    · exact .pure rfl
    · split
      · exact .pure rfl
      · apply Snapshot.post_bind (Snapshot.post_true _)
        intro validated _
        cases validated <;> exact .pure rfl

theorem dispatch_known_reaping_source {caller : GatewayWire.Request} {bundle : Validation.Bundle} {override : Option Nat}
    (context : RunPrefixCuts.Dispatched caller bundle override) (known : context.input.outcome.vmCleanup ≠ "unknown") :
    (context.dispatching = [] ∧ context.input.outcome.vmCleanup = "not_started") ∨
    (∃ (child : IO.Process.Child (VirtualMachine.arguments bundle context.imaged.allocated.directory.path).toStdioConfig)
      (status : UInt32) (before after : List Program.Event),
      context.dispatching =
        .returned (.spawn (VirtualMachine.arguments bundle context.imaged.allocated.directory.path)) (.ok child) ::
          (before ++ .returned (.tryWait child) (.ok (some status)) :: after)) := by
  have source := context.dispatch
  unfold RunPrefixCuts.Imaged.dispatchProgram dispatchImage at source
  cases image : context.imaged.image with
  | error error =>
    rw [image] at source
    obtain ⟨events, same⟩ := Program.returns_pure _ source
    exact .inl ⟨events, by rw [same]; rfl⟩
  | ok value =>
    rw [image] at source
    obtain ⟨vmEvents, vm, receiving, vmSource, receiveSource, trace⟩ := Program.returns_bind_split _ _ source
    obtain ⟨rawEvents, actualReceive, _⟩ := Program.lift_filesystem_source _ receiveSource
    have sameCleanup := Snapshot.post_returns (receive_cleanup_source _ _ _ _ _) actualReceive
    have vmKnown : vm.cleanup ≠ "unknown" := by
      intro unknown
      exact known (sameCleanup.trans unknown)
    obtain ⟨child, status, before, after, actualTrace⟩ :=
      VirtualMachine.actual_run_reaping_source _ _ _ _ vmSource vmKnown
    exact .inr ⟨child, status, before, after ++ receiving, by
      rw [trace, actualTrace]
      simp only [List.cons_append, List.append_assoc]⟩

structure VmReapingBinding {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {before after : Processes} {first last : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid before first all after last)
    (bundle : Validation.Bundle) (directory : String) (position : Nat) where
  value : IO.Process.Child (VirtualMachine.arguments bundle directory).toStdioConfig
  status : UInt32
  observations : OrderedPrimitiveObservations runtime initial all tick actor engine
    (.spawn (VirtualMachine.arguments bundle directory)) (.ok value) (.tryWait value) (.ok (some status))
  spawning : SelectedSdkObservation recording observations.first
  waiting : SelectedSdkObservation recording observations.second
  lease : SpawnedChildLease process all (VirtualMachine.arguments bundle directory) value
  sourceActor : lease.actor = actor
  sourceBirth : lease.birth.position = spawning.position
  sourceTick : lease.birth.tick = spawning.selected.tick
  sourceBefore : lease.birth.before = spawning.selected.cut.priorProcesses
  sourceAfter : lease.birth.after = spawning.selected.cut.nextProcesses
  sourceOrdinal : lease.engine.events.length = observations.first.rawBefore.length
  ordered : spawning.position < waiting.position
  earlier : waiting.position < position
  use : ReapingUse lease waiting.selected.tick.action

-- §FS-host-boundary.ownership: The actual dispatched run has either no VM
-- spawn at all or the SAME source spawn/Child/tryWait lifetime binding before
-- cleanup. The physical wait capture remains an individual SDK observation.
theorem actual_vm_reaping_binding {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {before after : Processes} {first last : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid before first all after last)
    {position : Nat} {tick : ActorTick runtime} (selected : all[position]? = some tick)
    {actor : ActorId} {engine : EngineState} (present : tick.before.actors actor = some engine)
    {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    {caller : GatewayWire.Request} {bundle : Validation.Bundle} {override : Option Nat}
    (context : RunPrefixCuts.Dispatched caller bundle override)
    (known : context.input.outcome.vmCleanup ≠ "unknown") {outer inside : List Program.Event}
    (trace : adapter.occurrence.logicalBefore = outer ++ context.events ++ inside) :
    (context.dispatching = [] ∧ context.input.outcome.vmCleanup = "not_started") ∨
      Nonempty (VmReapingBinding recording bundle context.imaged.allocated.directory.path position
        (actor := actor) (engine := engine) (initial := initial) (tick := tick)) := by
  rcases dispatch_known_reaping_source context known with notSpawned | ⟨value, status, between, after, events⟩
  · exact .inl notSpawned
  · have actualTrace : adapter.occurrence.logicalBefore =
        (outer ++ context.imaged.events) ++
          .returned (.spawn (VirtualMachine.arguments bundle context.imaged.allocated.directory.path)) (.ok value) ::
            (between ++ .returned (.tryWait value) (.ok (some status)) :: (after ++ inside)) := by
      rw [trace]
      simp only [RunPrefixCuts.Dispatched.events, events, List.append_assoc, List.cons_append]
    obtain ⟨observations⟩ := primitive_observations_ordered adapter actualTrace rfl rfl
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
    refine .inr ⟨{
      value
      status
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
    exact ReapingUse.tryWait status

theorem VmReapingBinding.no_later_child {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {laws : ChildLifecycleContract process child native hostUid}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {before after : Processes} {first last : NativeProcesses}
    {recording : NativeExternalJournal process child native hostUid before first all after last}
    {bundle : Validation.Bundle} {directory : String} {position : Nat}
    (source : VmReapingBinding recording bundle directory position (actor := actor) (engine := engine)
      (initial := initial) (tick := tick))
    {prior final : ReapedChildren} (lifetimes : ChildLifecycleJournal laws recording prior final)
    (captured : laws.usesLease source.waiting.selected.cut.current source.lease.key) :
    source.waiting.selected.cut.last.NoChildToken source.lease.token ∧ final source.lease.token = true :=
  actual_reaping_excludes_child_tail lifetimes source.waiting.selected source.waiting.same source.lease captured source.use

end LeanCage.Host.Kernel
