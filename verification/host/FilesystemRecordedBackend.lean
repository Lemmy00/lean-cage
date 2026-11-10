import FilesystemPrimitiveBackend
import FilesystemNativeAuthority

namespace LeanCage.Host.Kernel

private def head_tick {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {before after : Processes} {first last : NativeProcesses} {tick : ActorTick runtime}
    (_source : NativeExternalStep process child native hostUid before first tick after last) : ActorTick runtime := tick

def RecordedChildSource {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} (all : List (ActorTick runtime)) (position : Nat)
    {before after : Processes} {first last : NativeProcesses} {tick : ActorTick runtime} :
    NativeExternalStep process child native hostUid before first tick after last → Prop
  | .child _ call => Nonempty (PrimitiveBackendSource process all position before call.token)
  | _ => True

-- §FS-host-boundary.ownership: Each child source receipt belongs to the actual
-- embedded call and current process ledger of this ONE recording, not an
-- alternative ChildCallAt witness over an equal foreign tick.
def RecordedChildSources {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} (all : List (ActorTick runtime))
    {before after : Processes} {first last : NativeProcesses} {ticks : List (ActorTick runtime)} :
    NativeExternalJournal process child native hostUid before first ticks after last → List (ActorTick runtime) → Prop
  | .nil _ _, _ => True
  | .cons current rest, processed =>
    RecordedChildSource all processed.length current ∧ RecordedChildSources all rest (processed ++ [head_tick current])

private theorem process_append {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {process : ProcessContract runtime}
    {before middle after : Processes} {leading trailing : List (ActorTick runtime)}
    (first : ProcessJournal process before leading middle) (last : ProcessJournal process middle trailing after) :
    ProcessJournal process before (leading ++ trailing) after := by
  induction first with
  | nil => exact last
  | cons current rest ih => exact .cons current (ih last)

theorem actual_recorded_child_sources {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {after : Processes} {first last : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid Processes.empty first all after last) :
    RecordedChildSources all recording [] := by
  have follow : ∀ {before after : Processes} {first last : NativeProcesses} {ticks : List (ActorTick runtime)}
      (remaining : NativeExternalJournal process child native hostUid before first ticks after last)
      (processed : List (ActorTick runtime)),
      all = processed ++ ticks → ProcessJournal process Processes.empty processed before →
      RecordedChildSources all remaining processed := by
    intro before after first last ticks remaining
    induction remaining with
    | nil => intro processed shape registry; trivial
    | @cons before middle after first next last tick ticks current rest ih =>
      intro processed shape registry
      refine ⟨?_, ih (processed ++ [tick]) (by simpa only [List.append_assoc, List.singleton_append] using shape)
        (process_append registry (.cons current.external.process (.nil _)))⟩
      cases current with
      | application | launch | ordinary | native | retiring => trivial
      | child recorded call =>
        exact actual_primitive_backend_source journal processed ticks tick shape registry call.token call.active
  exact follow recording [] (by simp) (.nil _)

-- §AR-host-boundary.interfaces: A producer for the actual embedded child calls
-- suffices for all source-authority consumers. No alternate-call quantification
-- and no whole child-lifetime frame is required.
def RecordedChildAuthority {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {before after : Processes} {first last : NativeProcesses} {ticks : List (ActorTick runtime)} :
    NativeExternalJournal process child native hostUid before first ticks after last → Prop
  | .nil _ _ => True
  | .cons current rest =>
    (match current with | .child _ call => ChildAuthoritySafe call.operation | _ => True) ∧ RecordedChildAuthority rest

theorem recorded_native_authority_journal {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {before after : Processes} {first last : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid before first all after last)
    (backend : RecordedChildAuthority recording) : NativeAuthorityJournal recording := by
  have follow : ∀ {before after : Processes} {first last : NativeProcesses} {ticks : List (ActorTick runtime)}
      (remaining : NativeExternalJournal process child native hostUid before first ticks after last)
      (processed : List (ActorTick runtime)), all = processed ++ ticks →
      RecordedChildAuthority remaining → NativeAuthorityJournal remaining := by
    intro before after first last ticks remaining
    induction remaining with
    | nil => intro processed shape actual; trivial
    | @cons before middle after first next last tick ticks current rest ih =>
      intro processed shape actual
      have selected : all[processed.length]? = some tick := by
        rw [shape, List.getElem?_append_right (Nat.le_refl _)]
        simp only [Nat.sub_self, List.getElem?_cons_zero]
      refine ⟨?_, ih (processed ++ [tick]) (by simpa only [List.append_assoc, List.singleton_append] using shape) actual.2⟩
      cases current with
      | application => exact selected_primitive_action_authority journal selected
      | launch | ordinary | native | retiring => trivial
      | child => exact actual.1
  exact follow recording [] (by simp) backend

end LeanCage.Host.Kernel
