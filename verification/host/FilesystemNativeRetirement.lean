import FilesystemNativeEffects
import FilesystemNativeNamespace
import FilesystemRetirement

namespace LeanCage.Host.Kernel

variable {sourceProgram : Program UInt32}

private theorem native_retirement_actual {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {before after : Population} {token : NativeToken} {observation : EngineRetirement}
    {beforeResources afterResources : RetirementResources}
    (actual : ActorStep runtime (.nativeRetire token observation beforeResources afterResources) before after) :
    runtime.nativeRetire token observation beforeResources afterResources before.shared after.shared := by
  cases actual with
  | nativeRetire operation => exact operation

-- §AR-host-boundary.primitives: The ledger record selects the SAME physical teardown row,
-- not a later SDK return, EOF, PID lookup, or future assumption of completed cleanup.
theorem NativeRetirementAt.observed {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {tick : ActorTick runtime} {before after : NativeProcesses} (exit : NativeRetirementAt tick before after) :
    runtime.nativeRetire exit.token exit.observation exit.beforeResources exit.afterResources
      tick.before.shared tick.after.shared := by
  exact native_retirement_actual (exit.action ▸ tick.operation)

theorem NativeRetirementAt.stopped {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {tick : ActorTick runtime} {before after : NativeProcesses} (exit : NativeRetirementAt tick before after) :
    after.references exit.token = none ∧ after.nativeOwned exit.token = false ∧
      after.retiring exit.token = some exit.afterResources := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [NativeProcesses.retire, ite_eq_left] using congrArg (fun processes => processes.references exit.token) exit.next
  · simpa only [NativeProcesses.retire, ite_eq_left] using congrArg (fun processes => processes.nativeOwned exit.token) exit.next
  · simpa only [NativeProcesses.retire, ite_eq_left] using congrArg (fun processes => processes.retiring exit.token) exit.next

theorem NativeExternalStep.stopped {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat}
    {before after : Processes} {callers next : NativeProcesses} {tick : ActorTick runtime}
    (step : NativeExternalStep process child native hostUid before callers tick after next)
    {token : NativeToken} (inactive : callers.nativeOwned token = false) : next.nativeOwned token = false := by
  cases step with
  | application | ordinary | child => exact inactive
  | launch recorded handoff =>
    by_cases same : token = handoff.actor
    · simp only [NativeProcesses.transfer, same, ite_eq_left]
    · simpa only [NativeProcesses.transfer, ite_eq_right same] using inactive
  | native recorded call retirementFrame =>
    rw [native.native_ownership _ _ _ _ _ _ _ _ _ call.native]
    exact inactive
  | retiring recorded exit =>
    rw [exit.next]
    by_cases same : token = exit.token
    · simp only [NativeProcesses.retire, same, ite_eq_left]
    · simpa only [NativeProcesses.retire, ite_eq_right same] using inactive

theorem native_journal_stopped {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat}
    {before after : Processes} {callers next : NativeProcesses} {ticks : List (ActorTick runtime)}
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    {token : NativeToken} (inactive : callers.nativeOwned token = false) : next.nativeOwned token = false := by
  induction journal with
  | nil => exact inactive
  | cons actual tail ih => exact ih (actual.stopped inactive)

theorem native_stopped_cannot_call {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {native : NativePrimitive kernel} {before after : NativeProcesses} {tick : ActorTick runtime}
    (call : NativeCallAt native tick before after) (inactive : before.nativeOwned call.token = false) : False := by
  have owned := call.owned
  rw [inactive] at owned
  cases owned

theorem native_stopped_cannot_launch {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {before : NativeProcesses} {tick : ActorTick runtime} (handoff : NativeHandoffAt tick before)
    (inactive : before.nativeOwned handoff.actor = false) : False := by
  have owned := handoff.owned
  rw [inactive] at owned
  cases owned

-- §FS-host-boundary.ownership: A partial exit can only release resources of this native
-- lifetime. Every actually surviving descriptor and CWD remains globally held.
theorem native_retirement_held_before {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (laws : RetirementContract runtime) {tick : ActorTick runtime} {before after : NativeProcesses}
    (exit : NativeRetirementAt tick before after) {object : ObjectId} (held : NativeHeld after object) :
    NativeHeld before object := by
  rw [exit.next] at held
  rcases held with ⟨token, references, present, held⟩ | ⟨token, resources, present, held⟩
  · by_cases same : token = exit.token
    · simp only [NativeProcesses.retire, same, ite_eq_left] at present
      cases present
    · exact .inl ⟨token, references, by simpa only [NativeProcesses.retire, ite_eq_right same] using present, held⟩
  · by_cases same : token = exit.token
    · subst token
      simp only [NativeProcesses.retire, ite_eq_left] at present
      have identity := Option.some.inj present
      subst resources
      have earlier : exit.beforeResources.Held object := by
        rcases held with ⟨fd, handle, present, identity⟩ | directory
        · exact .inl ⟨fd, handle, laws.native_subset _ _ _ _ _ _ _ _ exit.observed present, identity⟩
        · exact .inr ((laws.native_directory _ _ _ _ _ _ exit.observed).2.2 object directory)
      rcases exit.input with ⟨references, owned, present, identity⟩ | present
      · rw [identity] at earlier
        rcases earlier with descriptor | directory
        · exact .inl ⟨exit.token, references, present, .inl descriptor⟩
        · exact .inl ⟨exit.token, references, present, .inr (Option.some.inj directory)⟩
      · exact .inr ⟨exit.token, exit.beforeResources, present, earlier⟩
    · exact .inr ⟨token, resources, by
        simpa only [NativeProcesses.retire, ite_eq_right same] using present, held⟩

theorem native_retirement_resources_complete {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (laws : RetirementContract runtime) {tick : ActorTick runtime} {before after : NativeProcesses}
    (exit : NativeRetirementAt tick before after) (complete : exit.observation.finished = true) :
    exit.afterResources.handles = (fun _ => none) ∧ exit.afterResources.directory = none :=
  laws.native_complete _ _ _ _ _ _ exit.observed complete

end LeanCage.Host.Kernel
