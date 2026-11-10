import GatewayChannelFlagEffects
import GatewayChannelHistory

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)}

-- §AR-host-boundary.interfaces.gateway: These are raw source facts or the
-- actual external operand boundary for ONE stored call, never an alias outcome.
inductive NativeFlagAuthority {tick : ActorTick runtime} {before after : NativeProcesses}
    (call : NativeCallAt native tick before after) (object : ObjectId) : Type where
  | unchanged (operation : DescriptorNoAliasWrite call.operation) : NativeFlagAuthority call object
  | cloexec (source minimum : UInt64) (operation : call.operation = .fcntl source 1030 minimum) :
      NativeFlagAuthority call object
  | operands (profile : ExternalDescriptorProfile call object) : NativeFlagAuthority call object

def NativeRowFlagSource {tick : ActorTick runtime} {middle : Processes}
    (actual : NativeExternalStep process child native hostUid before callers tick middle next) (object : ObjectId) : Type :=
  match actual with
  | .native _ call _ _ => NativeFlagAuthority call object
  | _ => PUnit

-- §FS-host-boundary.ownership: This source-classification goal is indexed by
-- the exact supplied journal value. Its production remains application work.
inductive NativeFlagClassifications (object : ObjectId) :
    {before after : Processes} → {callers next : NativeProcesses} → {ticks : List (ActorTick runtime)} →
    NativeExternalJournal process child native hostUid before callers ticks after next → Type 1 where
  | nil (before : Processes) (callers : NativeProcesses) : NativeFlagClassifications object (.nil before callers)
  | cons {before middle after : Processes} {callers next final : NativeProcesses}
      {tick : ActorTick runtime} {ticks : List (ActorTick runtime)}
      {actual : NativeExternalStep process child native hostUid before callers tick middle next}
      {rest : NativeExternalJournal process child native hostUid middle next ticks after final}
      (current : NativeRowFlagSource actual object) (tail : NativeFlagClassifications object rest) :
      NativeFlagClassifications object (.cons actual rest)

theorem native_row_aliases {ipc : ObjectId → Prop}
    (platform : NativeDescriptorContract native ipc) (fork : NativeCode.ForkReferences (runtime := runtime) native)
    {tick : ActorTick runtime} {middle : Processes}
    (actual : NativeExternalStep process child native hostUid before callers tick middle next)
    (object : ObjectId) (kind : ipc object) (live : tick.before.shared.allocated object = true)
    (source : NativeRowFlagSource actual object) (initial : NativeAliasesCloseExec object callers) :
    NativeAliasesCloseExec object next := by
  cases actual with
  | application | ordinary | child => exact initial
  | launch recorded handoff =>
    intro token references active present
    by_cases same : token = handoff.actor
    · simp only [NativeProcesses.transfer, same, ite_eq_left] at present
      cases present
    · exact initial token references active (by
        simpa only [NativeProcesses.transfer, ite_eq_right same] using present)
  | native recorded call retiring others =>
    apply native_call_preserves_all_aliases fork call object initial
    have own := initial call.token call.beforeReferences call.active call.inputTable
    cases source with
    | unchanged operation => exact source_operation_preserves_aliases platform call object kind live operation own
    | cloexec fd minimum operation =>
      exact source_cloexec_duplicate_preserves_aliases platform call object kind live fd minimum operation own
    | operands profile => exact external_operation_preserves_aliases platform call object kind live profile own
  | retiring recorded exit =>
    intro token references active present
    rw [exit.next] at present active
    by_cases same : token = exit.token
    · simp only [NativeProcesses.retire, same, ite_eq_left] at present
      cases present
    · exact initial token references active (by
        simpa only [NativeProcesses.retire, ite_eq_right same] using present)

-- §FS-host-boundary.ownership: The fold stores derived custody at each SAME
-- head. Another valid witness for equal ticks cannot substitute its FD table.
inductive NativeAliasExecution (object : ObjectId) :
    {before after : Processes} → {callers next : NativeProcesses} → {ticks : List (ActorTick runtime)} →
    NativeExternalJournal process child native hostUid before callers ticks after next → Type 1 where
  | nil (before : Processes) (callers : NativeProcesses) (aliases : NativeAliasesCloseExec object callers) :
      NativeAliasExecution object (.nil before callers)
  | cons {before middle after : Processes} {callers next final : NativeProcesses}
      {tick : ActorTick runtime} {ticks : List (ActorTick runtime)}
      {actual : NativeExternalStep process child native hostUid before callers tick middle next}
      {rest : NativeExternalJournal process child native hostUid middle next ticks after final}
      (aliases : NativeAliasesCloseExec object callers) (tail : NativeAliasExecution object rest) :
      NativeAliasExecution object (.cons actual rest)

theorem native_alias_execution {ipc : ObjectId → Prop}
    (platform : NativeDescriptorContract native ipc) (fork : NativeCode.ForkReferences (runtime := runtime) native)
    (lifetimes : LifetimeContract runtime) (object : ObjectId) (kind : ipc object)
    {recording : NativeExternalJournal process child native hostUid before callers ticks after next}
    (classifications : NativeFlagClassifications object recording)
    {start finish : Population} (history : ActorJournal runtime start ticks finish)
    (live : start.shared.allocated object = true) (initial : NativeAliasesCloseExec object callers) :
    Nonempty (NativeAliasExecution object recording) := by
  induction classifications generalizing start finish with
  | nil before callers => exact ⟨.nil before callers initial⟩
  | @cons before middle after callers next final tick ticks actual rest current tail ih =>
    cases history with
    | cons following =>
      obtain ⟨derived⟩ := ih following (actor_step_allocated lifetimes tick.operation object live)
        (native_row_aliases platform fork actual object kind live current initial)
      exact ⟨.cons initial derived⟩

theorem native_alias_execution_after_pair {ipc : ObjectId → Prop}
    (descriptors : NativeDescriptorContract native ipc) (pairs : SocketPairContract native ipc)
    (fork : NativeCode.ForkReferences (runtime := runtime) native) (lifetimes : LifetimeContract runtime)
    (namespaceLaws : NativeNamespaceContract native)
    (recording : NativeExternalJournal process child native hostUid before callers ticks after next)
    {pair : Pair} (entry : PairBirthEntry process child native hostUid before after callers next ticks pair)
    (_actual : ActualPairBirth recording entry)
    (references : NativeReferencesLive entry.cut.priorNative entry.tick.before.shared)
    (classifications : NativeFlagClassifications pair.caller entry.cut.last)
    {start finish : Population} (history : ActorJournal runtime start ticks finish) :
    Nonempty (NativeAliasExecution pair.caller entry.cut.last) := by
  obtain ⟨allocation⟩ := pairs.created entry.call entry.first entry.second entry.operation entry.product
  have sameHandle := Option.some.inj (allocation.leftOutput.symm.trans entry.firstInput)
  have object : allocation.left.object = pair.caller :=
    (congrArg Handle.object sameHandle).trans entry.callerObject
  have initial : NativeAliasesCloseExec pair.caller entry.cut.nextNative := by
    simpa only [object] using pair_initializes_all_native_aliases fork allocation references
  have live := pair_birth_allocated namespaceLaws entry .caller
  have kind : ipc pair.caller := object ▸ allocation.leftIpc
  rw [entry.cut.shape] at history
  obtain ⟨middle, prior, suffix⟩ := actor_journal_split entry.cut.leading _ history
  cases suffix with
  | cons following =>
    exact native_alias_execution descriptors fork lifetimes pair.caller kind classifications following live initial

theorem NativeAliasExecution.selected_before
    {recording : NativeExternalJournal process child native hostUid before callers ticks after next}
    {object : ObjectId} (execution : NativeAliasExecution object recording)
    {position : Nat} (selected : SelectedNativeCut process child native hostUid before after callers next ticks position)
    (same : selectNativeCut recording position = some selected) :
    NativeAliasesCloseExec object selected.cut.priorNative := by
  induction execution generalizing position with
  | nil => simp only [selectNativeCut] at same; cases same
  | @cons before middle after callers next final tick ticks actual rest aliases tail ih =>
    cases position with
    | zero =>
      have identity : selected = ⟨tick, ⟨[], ticks, rfl, rfl, before, middle, callers, next, .nil _ _, actual, rest⟩⟩ :=
        (Option.some.inj same).symm
      cases identity
      exact aliases
    | succ position =>
      let extend := fun (chosen : SelectedNativeCut process child native hostUid middle after next final ticks position) =>
        ({ tick := chosen.tick
           cut := { chosen.cut with
             leading := tick :: chosen.cut.leading
             count := by simp only [List.length_cons, chosen.cut.count]
             shape := by simp only [chosen.cut.shape, List.cons_append]
             first := .cons actual chosen.cut.first } } :
          SelectedNativeCut process child native hostUid before after callers final (tick :: ticks) (position + 1))
      change (selectNativeCut rest position).map extend = some selected at same
      cases earlier : selectNativeCut rest position with
      | none => simp only [earlier, Option.map_none] at same; cases same
      | some chosen =>
        have prior := ih chosen earlier
        simp only [earlier, Option.map_some] at same
        have identity := (Option.some.inj same).symm
        cases identity
        exact prior

end LeanCage.Host.PrivateStreams
