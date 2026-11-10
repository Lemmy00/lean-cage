import GatewayChannelProcessHistory

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

-- §AR-host-boundary.primitives: These operands can replace an already live
-- descriptor. Fresh open/dup allocation cannot reuse an occupied input slot;
-- descriptor-table release and actual image replacement remain explicit.
inductive NativeReferenceReplacement : NativeOperation → NativeProduct → UInt64 → Prop where
  | close (request : Request) (product : NativeProduct) (closing : request.op = .close) :
      NativeReferenceReplacement (.vfs (.adapted request)) product request.first
  | cursor (request : Request) (product : NativeProduct) (closing : request.op = .dirClose) :
      NativeReferenceReplacement (.vfs (.adapted request)) product request.second
  | duplicate (source target flags : UInt64) (product : NativeProduct) :
      NativeReferenceReplacement (.duplicate source target flags) product target
  | image (arguments : NativeExec) (image : ObjectId) (descriptor : UInt64) :
      NativeReferenceReplacement (.exec arguments) (.executed image) descriptor

structure NativeReferenceContract {kernel : Contract} (native : NativePrimitive kernel) : Prop where
  own : ∀ {runtime : PrimitiveActorRuntime kernel} {tick : ActorTick runtime} {before after : NativeProcesses}
    (call : NativeCallAt native tick before after) descriptor handle,
    call.beforeReferences.handles descriptor = some handle →
    call.afterReferences.handles descriptor = some handle ∨ NativeReferenceReplacement call.operation call.product descriptor

-- This is an individual source operand, not a callback frame: the selected
-- operation's actual replacement target is different from this held FD.
def RetainsDescriptor {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {native : NativePrimitive kernel} {tick : ActorTick runtime} {before after : NativeProcesses}
    (call : NativeCallAt native tick before after) (descriptor : UInt64) : Prop :=
  ¬ NativeReferenceReplacement call.operation call.product descriptor

theorem actual_call_retains_descriptor {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {native : NativePrimitive kernel} (platform : NativeReferenceContract native)
    {tick : ActorTick runtime} {before after : NativeProcesses}
    (call : NativeCallAt native tick before after) (descriptor : UInt64) (handle : Handle)
    (input : call.beforeReferences.handles descriptor = some handle)
    (source : RetainsDescriptor call descriptor) : call.afterReferences.handles descriptor = some handle := by
  rcases platform.own call descriptor handle input with retained | replaced
  · exact retained
  · exact False.elim (source replaced)

theorem receive_retains_descriptor (descriptor extent flags held : UInt64) (product : NativeProduct) :
    ¬ NativeReferenceReplacement (.receive descriptor extent flags) product held := by intro impossible; cases impossible

theorem send_retains_descriptor (descriptor extent flags held : UInt64) (bytes : ByteArray) (product : NativeProduct) :
    ¬ NativeReferenceReplacement (.send descriptor bytes extent flags) product held := by intro impossible; cases impossible

theorem shutdown_retains_descriptor (descriptor how held : UInt64) (product : NativeProduct) :
    ¬ NativeReferenceReplacement (.shutdown descriptor how) product held := by intro impossible; cases impossible

theorem fcntl_retains_descriptor (descriptor command argument held : UInt64) (product : NativeProduct) :
    ¬ NativeReferenceReplacement (.fcntl descriptor command argument) product held := by intro impossible; cases impossible

theorem spawn_retains_descriptor (arguments : NativeSpawn) (held : UInt64) (product : NativeProduct) :
    ¬ NativeReferenceReplacement (.spawn arguments) product held := by intro impossible; cases impossible

-- An actual input lease plus a distinct endpoint at the same current table
-- derives different numeric descriptors; reuse is never excluded by number alone.
theorem actual_distinct_endpoint_descriptors (references : NativeReferences)
    (first last : UInt64) (left right : Handle)
    (before : references.handles first = some left) (after : references.handles last = some right)
    (separate : left.object ≠ right.object) : first ≠ last := by
  intro same
  subst last
  have identity := Option.some.inj (before.symm.trans after)
  exact separate (congrArg Handle.object identity)

-- A source proof supplies only the actual replacement-operand exclusions of
-- each selected own-process row. Other processes keep their actual effects;
-- normal/detached source resumption supplies survival independently.
def NativeReferenceSource {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses} {tick : ActorTick runtime}
    (row : NativeExternalStep process child native hostUid before callers tick after next)
    (query : NativeToken) (descriptor : UInt64) : Prop :=
  match row with
  | .native _ call _ _ => call.token = query → RetainsDescriptor call descriptor
  | _ => True

inductive NativeReferenceSources {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    (query : NativeToken) (descriptor : UInt64) :
    {before after : Processes} → {callers next : NativeProcesses} → {ticks : List (ActorTick runtime)} →
    NativeExternalJournal process child native hostUid before callers ticks after next → Prop where
  | nil (before : Processes) (callers : NativeProcesses) : NativeReferenceSources query descriptor (.nil before callers)
  | cons {before middle after : Processes} {callers next final : NativeProcesses}
      {tick : ActorTick runtime} {ticks : List (ActorTick runtime)}
      {row : NativeExternalStep process child native hostUid before callers tick middle next}
      {tail : NativeExternalJournal process child native hostUid middle next ticks after final}
      (source : NativeReferenceSource row query descriptor) (remaining : NativeReferenceSources query descriptor tail) :
      NativeReferenceSources query descriptor (.cons row tail)

theorem native_reference_row_retained {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    (platform : NativeReferenceContract native)
    {before after : Processes} {callers next : NativeProcesses} {tick : ActorTick runtime}
    (row : NativeExternalStep process child native hostUid before callers tick after next)
    (query : NativeToken) (descriptor : UInt64) (table : NativeReferences) (handle : Handle)
    (allocated : callers.allocated query = true) (input : callers.references query = some table)
    (held : table.handles descriptor = some handle) (survived : next.nativeOwned query = true)
    (source : NativeReferenceSource row query descriptor) :
    ∃ current, next.references query = some current ∧ current.handles descriptor = some handle := by
  cases row with
  | application | ordinary | child => exact ⟨table, input, held⟩
  | launch recorded handoff =>
    by_cases same : query = handoff.actor
    · simp only [NativeProcesses.transfer, same, ite_true] at survived; contradiction
    · exact ⟨table, by simpa only [NativeProcesses.transfer, ite_eq_right same] using input, held⟩
  | native recorded call retirementFrame otherReferences =>
    by_cases same : query = call.token
    · subst query
      have identity := Option.some.inj (input.symm.trans call.inputTable)
      subst table
      exact ⟨call.afterReferences, call.outputTable,
        actual_call_retains_descriptor platform call descriptor handle held (source rfl)⟩
    · exact ⟨table, (otherReferences query same allocated).trans input, held⟩
  | retiring recorded exit =>
    rw [exit.next] at survived ⊢
    by_cases same : query = exit.token
    · simp only [NativeProcesses.retire, same, ite_true] at survived; contradiction
    · exact ⟨table, by simpa only [NativeProcesses.retire, ite_eq_right same] using input, held⟩

-- §FS-host-boundary.caller: The same global native history retains the exact
-- caller endpoint/OFD through all source-classified operations up to the real
-- surviving resumption. No whole callback/reader/queue frame is postulated.
theorem native_reference_history_retained {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    (platform : NativeReferenceContract native)
    {before after : Processes} {callers next : NativeProcesses} {ticks : List (ActorTick runtime)}
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    (query : NativeToken) (descriptor : UInt64) (table : NativeReferences) (handle : Handle)
    (allocated : callers.allocated query = true) (input : callers.references query = some table)
    (held : table.handles descriptor = some handle) (survived : next.nativeOwned query = true)
    (source : NativeReferenceSources query descriptor journal) :
    ∃ current, next.references query = some current ∧ current.handles descriptor = some handle := by
  induction source generalizing table with
  | nil => exact ⟨table, input, held⟩
  | @cons before middle after callers next final tick ticks row tail currentSource remaining ih =>
    have middleAlive := native_journal_owned_backwards tail query survived
    obtain ⟨current, present, retained⟩ := native_reference_row_retained platform row query descriptor table handle
      allocated input held middleAlive currentSource
    exact ih current (row.monotone query allocated) present retained survived

end LeanCage.Host.PrivateStreams
