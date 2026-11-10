import FilesystemNativeEffects

namespace LeanCage.Host.Kernel

abbrev ReapedChildren := ProcessToken → Bool

-- §AR-host-boundary.primitives: The lease identifies the actual source birth,
-- not a reusable PID or equality of an opaque SDK value from another invocation.
structure SdkChildKey where
  actor : ActorId
  position : Nat
  ordinal : Nat
  token : ProcessToken

structure SpawnedChildLease {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} (process : ProcessContract runtime)
    (all : List (ActorTick runtime)) (arguments : IO.Process.SpawnArgs)
    (value : IO.Process.Child arguments.toStdioConfig) where
  actor : ActorId
  token : ProcessToken
  birth : RecordedProcessBirth process all token
  engine : EngineState
  present : birth.tick.before.actors actor = some engine
  action : birth.tick.action = .returned actor (.spawn arguments) (.ok value)

def SpawnedChildLease.key {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {process : ProcessContract runtime}
    {all : List (ActorTick runtime)} {arguments : IO.Process.SpawnArgs}
    {value : IO.Process.Child arguments.toStdioConfig}
    (lease : SpawnedChildLease process all arguments value) : SdkChildKey :=
  ⟨lease.actor, lease.birth.position, lease.engine.events.length, lease.token⟩

-- §FS-host-boundary.ownership: The selected recording head itself supplies the
-- birth token and exact returned Child value. No second process transcript or
-- child/PID injectivity assumption supplies the lease.
theorem spawned_child_lease_from_head {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {process : ProcessContract runtime}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {before after : Processes} {first last : NativeProcesses} {tick : ActorTick runtime}
    (current : NativeExternalStep process child native hostUid before first tick after last)
    {all : List (ActorTick runtime)} {position : Nat} (selected : all[position]? = some tick)
    {actor : ActorId} {arguments : IO.Process.SpawnArgs} {value : IO.Process.Child arguments.toStdioConfig}
    (action : tick.action = .returned actor (.spawn arguments) (.ok value)) :
    ∃ lease : SpawnedChildLease process all arguments value,
      lease.birth.position = position ∧ lease.birth.tick = tick ∧ lease.actor = actor ∧
      lease.birth.before = before ∧ lease.birth.after = after := by
  have actual := current.external.process
  obtain ⟨token, fresh, allocated, owner, spawned, pid, positive, bound⟩ :=
    process.spawn_success _ _ _ _ _ _ actual action
  have event : tick.action.eventFor actor = some (.returned (.spawn arguments) (.ok value)) := by
    simp only [action, ActorAction.eventFor, ↓reduceIte]
  obtain ⟨engine, present⟩ := tick_event_engine tick event
  exact ⟨⟨actor, token, ⟨position, tick, before, after, selected, actual, fresh, allocated⟩, engine, present, action⟩,
    rfl, rfl, rfl, rfl, rfl⟩

-- §FS-host-boundary.ownership: Both successful SDK observations are truthful
-- reaping observations of the selected opaque resource, including cached waits.
inductive ReapingUse {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {process : ProcessContract runtime}
    {all : List (ActorTick runtime)} {arguments : IO.Process.SpawnArgs}
    {value : IO.Process.Child arguments.toStdioConfig}
    (lease : SpawnedChildLease process all arguments value) : ActorAction → Prop where
  | wait (status : UInt32) : ReapingUse lease (.returned lease.actor (.wait value) (.ok status))
  | tryWait (status : UInt32) : ReapingUse lease (.returned lease.actor (.tryWait value) (.ok (some status)))

-- §AR-host-boundary.primitives: Observations are per actual recording head.
-- The SDK adapter binds its captured opaque-child lease separately; no whole
-- child lifetime, descendant cleanup or safe-helper assertion is a primitive.
structure ChildLifecycleContract {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} (process : ProcessContract runtime)
    (child : ChildPrimitive kernel) (native : NativePrimitive kernel) (hostUid : Nat) where
  observed : {before after : Processes} → {first last : NativeProcesses} → {tick : ActorTick runtime} →
    NativeExternalStep process child native hostUid before first tick after last →
      ReapedChildren → ReapedChildren → Prop
  monotone : ∀ {before after first last tick} (current :
      NativeExternalStep process child native hostUid before first tick after last) {prior next},
    observed current prior next → ∀ token, prior token = true → next token = true
  childLive : ∀ {before after callers tick} (recorded : process.step tick before after)
    (call : ChildCallAt child tick before after) {prior next},
    observed (.child (callers := callers) recorded call) prior next → prior call.token = false
  usesLease : {before after : Processes} → {first last : NativeProcesses} → {tick : ActorTick runtime} →
    NativeExternalStep process child native hostUid before first tick after last → SdkChildKey → Prop
  reaped : ∀ {before after first last tick} (current :
      NativeExternalStep process child native hostUid before first tick after last) {prior next},
    observed current prior next → ∀ {all arguments value} (lease : SpawnedChildLease process all arguments value),
      usesLease current lease.key → ReapingUse lease tick.action → next lease.token = true

-- §FS-host-boundary.ownership: This companion keeps the exact recording value,
-- not another equal-ticked selection of native/child calls. Every row comes
-- from the individual observed SDK/kernel operation, including error and loss.
inductive ChildLifecycleJournal {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {process : ProcessContract runtime}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    (laws : ChildLifecycleContract process child native hostUid) :
    {before after : Processes} → {first last : NativeProcesses} → {ticks : List (ActorTick runtime)} →
    NativeExternalJournal process child native hostUid before first ticks after last →
      ReapedChildren → ReapedChildren → Prop where
  | nil {processes : Processes} {callers : NativeProcesses} (reaped : ReapedChildren) :
      ChildLifecycleJournal laws (.nil processes callers) reaped reaped
  | cons {before middle after : Processes} {first next last : NativeProcesses}
      {tick : ActorTick runtime} {ticks : List (ActorTick runtime)}
      {current : NativeExternalStep process child native hostUid before first tick middle next}
      {rest : NativeExternalJournal process child native hostUid middle next ticks after last}
      {prior intermediate final : ReapedChildren}
      (actual : laws.observed current prior intermediate)
      (tail : ChildLifecycleJournal laws rest intermediate final) :
      ChildLifecycleJournal laws (.cons current rest) prior final

theorem child_lifecycle_monotone {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {process : ProcessContract runtime}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {laws : ChildLifecycleContract process child native hostUid}
    {before after : Processes} {first last : NativeProcesses} {ticks : List (ActorTick runtime)}
    {recording : NativeExternalJournal process child native hostUid before first ticks after last}
    {prior final : ReapedChildren} (journal : ChildLifecycleJournal laws recording prior final)
    (token : ProcessToken) (reaped : prior token = true) : final token = true := by
  induction journal with
  | nil => exact reaped
  | cons actual tail ih => exact ih (laws.monotone _ actual token reaped)

def NativeExternalStep.childToken? {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {process : ProcessContract runtime}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {before after : Processes} {first last : NativeProcesses} {tick : ActorTick runtime}
    (current : NativeExternalStep process child native hostUid before first tick after last) : Option ProcessToken :=
  match current with
  | .child _ call => some call.token
  | _ => none

def NativeExternalJournal.NoChildToken {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {process : ProcessContract runtime}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {before after : Processes} {first last : NativeProcesses} {ticks : List (ActorTick runtime)}
    (recording : NativeExternalJournal process child native hostUid before first ticks after last)
    (token : ProcessToken) : Prop :=
  match recording with
  | .nil _ _ => True
  | .cons current rest => current.childToken? ≠ some token ∧ rest.NoChildToken token

-- §FS-host-boundary.ownership: Once the exact token has been reaped, no later
-- child syscall on that same recording can belong to it. Other children,
-- actors, public interference, partial teardown and namespace changes remain.
theorem no_child_after_reaping {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {process : ProcessContract runtime}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {laws : ChildLifecycleContract process child native hostUid}
    {before after : Processes} {first last : NativeProcesses} {ticks : List (ActorTick runtime)}
    {recording : NativeExternalJournal process child native hostUid before first ticks after last}
    {prior final : ReapedChildren} (journal : ChildLifecycleJournal laws recording prior final)
    (token : ProcessToken) (reaped : prior token = true) : recording.NoChildToken token := by
  induction journal with
  | nil => exact True.intro
  | @cons before middle after first next last tick ticks current rest prior intermediate final actual tail ih =>
    constructor
    · cases current with
      | child recorded call =>
        intro same
        have identity : call.token = token := Option.some.inj same
        have live := laws.childLive recorded call actual
        rw [identity, reaped] at live
        cases live
      | application | launch | ordinary | native | retiring => intro impossible; cases impossible
    · exact ih (laws.monotone _ actual token reaped)

-- §FS-host-boundary.ownership: The current wait/tryWait's own SDK observation
-- establishes reaping; monotonicity then rules out later syscalls of that SAME
-- token. Error/loss observations need not claim a successful wait or no child.
theorem reaping_head_excludes_child_tail {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {process : ProcessContract runtime}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {laws : ChildLifecycleContract process child native hostUid}
    {before middle after : Processes} {first next last : NativeProcesses}
    {tick : ActorTick runtime} {ticks : List (ActorTick runtime)}
    {current : NativeExternalStep process child native hostUid before first tick middle next}
    {rest : NativeExternalJournal process child native hostUid middle next ticks after last}
    {prior intermediate final : ReapedChildren}
    (observed : laws.observed current prior intermediate)
    (tail : ChildLifecycleJournal laws rest intermediate final)
    {all : List (ActorTick runtime)} {arguments : IO.Process.SpawnArgs}
    {value : IO.Process.Child arguments.toStdioConfig}
    (lease : SpawnedChildLease process all arguments value)
    (captured : laws.usesLease current lease.key) (use : ReapingUse lease tick.action) :
    rest.NoChildToken lease.token ∧ final lease.token = true := by
  have reaped := laws.reaped current observed lease captured use
  exact ⟨no_child_after_reaping tail lease.token reaped, child_lifecycle_monotone tail lease.token reaped⟩

end LeanCage.Host.Kernel
