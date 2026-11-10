import FilesystemBackend
import FilesystemNativeOperations

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

-- §AR-host-boundary.primitives: Child syscalls share storage/OFDs while using their own FD table.
def SameShared (first second : World) : Prop :=
  first.allocated = second.allocated ∧ first.attributes = second.attributes ∧
  first.information = second.information ∧ first.entries = second.entries ∧
  first.contents = second.contents ∧ first.descriptionAllocated = second.descriptionAllocated ∧
  first.descriptions = second.descriptions ∧ first.inodeFlags = second.inodeFlags

-- §AR-host-boundary.primitives: QEMU socket creation/bind is distinct from the host adapter ABI.
inductive ChildOperation where
  | adapted (request : Request)
  | unixSocket (flags : UInt64)
  | bindUnix (fd : UInt64) (path : ByteArray)

-- §AR-host-boundary.primitives: An observation binds one actual task lifetime, syscall and table.
structure ChildPrimitive (kernel : Contract) where
  observed : ProcessToken → Credentials → World → ChildOperation → Option Reply → World → Prop
  interpreted : ∀ token caller before after request reply,
    observed token caller before (.adapted request) reply after → kernel.step before request reply after

structure ChildCallAt {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (primitive : ChildPrimitive kernel) (tick : ActorTick runtime) (before after : Processes) where
  token : ProcessToken
  caller : Credentials
  beforeReferences : ChildReferences
  afterReferences : ChildReferences
  active : before.allocated token = true
  inputTable : before.references token = some beforeReferences
  outputTable : after.references token = some afterReferences
  operation : ChildOperation
  reply : Option Reply
  action : tick.action = .foreign caller
  native : primitive.observed token caller (beforeReferences.project tick.before.shared)
    operation reply (afterReferences.project tick.after.shared)

-- §FS-host-boundary.ownership: Foreign DAC and owned child operations have different evidence.
inductive ExternalStepWith {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (contract : ProcessContract runtime) (primitive : ChildPrimitive kernel) (hostUid : Nat)
    (nativePrimitive : Option (NativePrimitive kernel)) :
    Processes → ActorTick runtime → Processes → Type 1 where
  | application {before after : Processes} {tick : ActorTick runtime}
      (recorded : contract.step tick before after)
      (notForeign : ∀ caller, tick.action ≠ .foreign caller) :
      ExternalStepWith contract primitive hostUid nativePrimitive before tick after
  | ordinary {before after : Processes} {tick : ActorTick runtime} (caller : Credentials)
      (recorded : contract.step tick before after)
      (action : tick.action = .foreign caller) (allowed : OrdinaryForeign caller hostUid) :
      ExternalStepWith contract primitive hostUid nativePrimitive before tick after
  | child {before after : Processes} {tick : ActorTick runtime}
      (recorded : contract.step tick before after) (call : ChildCallAt primitive tick before after) :
      ExternalStepWith contract primitive hostUid nativePrimitive before tick after
  | native {before after : Processes} {tick : ActorTick runtime}
      {nativeBefore nativeAfter : NativeProcesses}
      (recorded : contract.step tick before after) (native : NativePrimitive kernel)
      (enabled : nativePrimitive = some native)
      (call : NativeCallAt native tick nativeBefore nativeAfter) :
      ExternalStepWith contract primitive hostUid nativePrimitive before tick after

abbrev ExternalStep {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (contract : ProcessContract runtime) (primitive : ChildPrimitive kernel) (hostUid : Nat)
    (before : Processes) (tick : ActorTick runtime) (after : Processes)
    (nativePrimitive : Option (NativePrimitive kernel) := none) : Type 1 :=
  ExternalStepWith contract primitive hostUid nativePrimitive before tick after

theorem ExternalStep.process {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {contract : ProcessContract runtime} {primitive : ChildPrimitive kernel} {hostUid : Nat}
    {nativePrimitive : Option (NativePrimitive kernel)}
    {before after : Processes} {tick : ActorTick runtime}
    (step : ExternalStep contract primitive hostUid (nativePrimitive := nativePrimitive) before tick after) :
    contract.step tick before after := by
  cases step with
  | application recorded => exact recorded
  | ordinary caller recorded => exact recorded
  | child recorded => exact recorded
  | native recorded => exact recorded

inductive ExternalJournalWith {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (contract : ProcessContract runtime) (primitive : ChildPrimitive kernel) (hostUid : Nat)
    (nativePrimitive : Option (NativePrimitive kernel)) :
    Processes → List (ActorTick runtime) → Processes → Type 1 where
  | nil (processes : Processes) :
      ExternalJournalWith contract primitive hostUid nativePrimitive processes [] processes
  | cons {before middle after : Processes} {tick : ActorTick runtime} {ticks : List (ActorTick runtime)}
      (actual : ExternalStep contract primitive hostUid (nativePrimitive := nativePrimitive) before tick middle)
      (tail : ExternalJournalWith contract primitive hostUid nativePrimitive middle ticks after) :
      ExternalJournalWith contract primitive hostUid nativePrimitive before (tick :: ticks) after

abbrev ExternalJournal {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (contract : ProcessContract runtime) (primitive : ChildPrimitive kernel) (hostUid : Nat)
    (before : Processes) (ticks : List (ActorTick runtime)) (after : Processes)
    (nativePrimitive : Option (NativePrimitive kernel) := none) : Type 1 :=
  ExternalJournalWith contract primitive hostUid nativePrimitive before ticks after

theorem external_journal_processes {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {contract : ProcessContract runtime} {primitive : ChildPrimitive kernel} {hostUid : Nat}
    {nativePrimitive : Option (NativePrimitive kernel)}
    {before after : Processes} {ticks : List (ActorTick runtime)}
    (recording : ExternalJournal contract primitive hostUid (nativePrimitive := nativePrimitive) before ticks after) :
    ProcessJournal contract before ticks after := by
  induction recording with
  | nil => exact .nil _
  | cons actual tail ih => exact .cons actual.process ih

structure ExternalCut {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (contract : ProcessContract runtime) (primitive : ChildPrimitive kernel) (hostUid : Nat)
    (initial final : Processes) (ticks : List (ActorTick runtime)) (position : Nat) (tick : ActorTick runtime)
    (nativePrimitive : Option (NativePrimitive kernel) := none) where
  leading : List (ActorTick runtime)
  trailing : List (ActorTick runtime)
  count : position = leading.length
  shape : ticks = leading ++ tick :: trailing
  before : Processes
  after : Processes
  first : ExternalJournal contract primitive hostUid (nativePrimitive := nativePrimitive) initial leading before
  current : ExternalStep contract primitive hostUid (nativePrimitive := nativePrimitive) before tick after
  last : ExternalJournal contract primitive hostUid (nativePrimitive := nativePrimitive) after trailing final

-- §FS-host-boundary.acceptance: The selected child call keeps the same global/process cursor.
theorem selected_external_cut {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {contract : ProcessContract runtime} {primitive : ChildPrimitive kernel} {hostUid : Nat}
    {nativePrimitive : Option (NativePrimitive kernel)}
    {before after : Processes} {ticks : List (ActorTick runtime)}
    (recording : ExternalJournal contract primitive hostUid (nativePrimitive := nativePrimitive) before ticks after)
    {position : Nat} {tick : ActorTick runtime} (selected : ticks[position]? = some tick) :
    Nonempty (ExternalCut contract primitive hostUid before after ticks position tick (nativePrimitive := nativePrimitive)) := by
  induction recording generalizing position with
  | nil => cases selected
  | @cons before middle after first ticks actual tail ih =>
    cases position with
    | zero =>
      have same := Option.some.inj selected
      subst first
      exact ⟨⟨[], ticks, rfl, rfl, before, middle, .nil _, actual, tail⟩⟩
    | succ position =>
      obtain ⟨cut⟩ := ih selected
      exact ⟨{
        cut with
        leading := first :: cut.leading
        count := by simpa only [List.length_cons] using congrArg Nat.succ cut.count
        shape := by simp only [cut.shape, List.cons_append]
        first := .cons actual cut.first }⟩

structure OwnedChildCall {kernel : Contract} {runtime : ActorRuntime kernel}
    (contract : ProcessContract runtime) (primitive : ChildPrimitive kernel) (ticks : List (ActorTick runtime))
    (position : Nat) (tick : ActorTick runtime) where
  before : Processes
  after : Processes
  call : ChildCallAt primitive tick before after
  source : BackendSource contract ticks position before call.token

-- §FS-host-boundary.ownership: A host-account child cannot enter as an ordinary foreign action.
theorem actual_foreign_source {kernel : Contract} {runtime : ActorRuntime kernel}
    {contract : ProcessContract runtime} {primitive : ChildPrimitive kernel} {hostUid : Nat}
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {processes : Processes} (recording : ExternalJournal contract primitive hostUid Processes.empty ticks processes)
    {position : Nat} {tick : ActorTick runtime} (selected : ticks[position]? = some tick)
    (caller : Credentials) (action : tick.action = .foreign caller) :
    OrdinaryForeign caller hostUid ∨ Nonempty (OwnedChildCall contract primitive ticks position tick) := by
  obtain ⟨cut⟩ := selected_external_cut recording selected
  have current := cut.current
  cases current with
  | application recorded notForeign => exact False.elim (notForeign caller action)
  | ordinary observed recorded observedAction allowed =>
    have same : observed = caller := by
      have actionSame := observedAction.symm.trans action
      cases actionSame
      rfl
    exact .inl (same ▸ allowed)
  | child recorded call =>
    obtain ⟨source⟩ := actual_backend_source journal cut.leading cut.trailing tick cut.shape
      (external_journal_processes cut.first) call.token call.active
    refine .inr ⟨⟨cut.before, cut.after, call, ?_⟩⟩
    exact { source with earlier := by simpa only [cut.count] using source.earlier }
  | native recorded native enabled call => cases enabled

-- §FS-host-boundary.ownership: Child effects are one syscall on this exact copied/current table.
theorem owned_child_kernel_step {kernel : Contract} {runtime : ActorRuntime kernel}
    {contract : ProcessContract runtime} {primitive : ChildPrimitive kernel} {ticks : List (ActorTick runtime)}
    {position : Nat} {tick : ActorTick runtime}
    (source : OwnedChildCall contract primitive ticks position tick) {request : Request}
    (operation : source.call.operation = .adapted request) :
    kernel.step (source.call.beforeReferences.project tick.before.shared) request source.call.reply
      (source.call.afterReferences.project tick.after.shared) := by
  have observed := source.call.native
  rw [operation] at observed
  exact primitive.interpreted _ _ _ _ _ _ observed

end LeanCage.Host.Kernel
