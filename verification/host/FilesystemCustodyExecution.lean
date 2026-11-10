import FilesystemRegisteredCustody

namespace LeanCage.Host.Kernel

-- §FS-host-boundary.ownership: Retain the application-constructed custody snapshot
-- before every exact head of the SAME native/child/source recording. This is an
-- induction result, not a primitive assertion about a complete caller or callback.
inductive RegisteredCustodyExecution {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    (initial : World) (all : List (ActorTick runtime)) (hostUid : Nat)
    (dataObjects directories : ObjectId → Prop) (semantics : NameSemanticsView) :
    {before after : Processes} → {first last : NativeProcesses} → {ticks : List (ActorTick runtime)} →
    NativeExternalJournal process child native hostUid before first ticks after last →
    List (ActorTick runtime) → Population → Population → Type 1 where
  | nil {processes : Processes} {callers : NativeProcesses} {processed : List (ActorTick runtime)}
      {population : Population} {foreignReferences : ForeignReferences}
      (state : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
        foreignReferences processed population callers) :
      RegisteredCustodyExecution runtime initial all hostUid dataObjects directories semantics
        (.nil processes callers) processed population population
  | cons {before middle after : Processes} {first next last : NativeProcesses}
      {tick : ActorTick runtime} {ticks processed : List (ActorTick runtime)} {final : Population}
      {foreignReferences : ForeignReferences}
      (current : NativeExternalStep process child native hostUid before first tick middle next)
      (rest : NativeExternalJournal process child native hostUid middle next ticks after last)
      (state : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
        foreignReferences processed tick.before first)
      (tail : RegisteredCustodyExecution runtime initial all hostUid dataObjects directories semantics rest
        (processed ++ [tick]) tick.after final) :
      RegisteredCustodyExecution runtime initial all hostUid dataObjects directories semantics
        (.cons current rest) processed tick.before final

def RegisteredCustodyExecution.before {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {initial : World} {all : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {before after : Processes} {first last : NativeProcesses} {ticks processed : List (ActorTick runtime)}
    {start final : Population}
    {recording : NativeExternalJournal process child native hostUid before first ticks after last}
    (source : RegisteredCustodyExecution runtime initial all hostUid dataObjects directories semantics recording
      processed start final) :
    Sigma (fun foreignReferences => RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed start first) :=
  match source with
  | .nil state => ⟨_, state⟩
  | .cons _ _ state _ => ⟨_, state⟩

-- §FS-host-boundary.ownership: Every snapshot lies on the original connected physical
-- journal. Lost calls and retirement rows are retained by their actual recording head.
theorem RegisteredCustodyExecution.actual {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {initial : World} {all : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {before after : Processes} {first last : NativeProcesses} {ticks processed : List (ActorTick runtime)}
    {start final : Population}
    {recording : NativeExternalJournal process child native hostUid before first ticks after last}
    (source : RegisteredCustodyExecution runtime initial all hostUid dataObjects directories semantics recording
      processed start final) : ActorJournal runtime start ticks final := by
  induction source with
  | nil => exact .nil _
  | cons current rest state tail ih => exact .cons ih

noncomputable def RegisteredCustodyExecution.final {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {initial : World} {all : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {before after : Processes} {first last : NativeProcesses} {ticks processed : List (ActorTick runtime)}
    {start finish : Population}
    {recording : NativeExternalJournal process child native hostUid before first ticks after last}
    (source : RegisteredCustodyExecution runtime initial all hostUid dataObjects directories semantics recording
      processed start finish) :
    Sigma (fun foreignReferences => RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ ticks) finish last) := by
  induction source with
  | nil state => exact ⟨_, by simpa only [List.append_nil] using state⟩
  | @cons before middle after first next last tick ticks processed final foreign current rest state tail ih =>
    obtain ⟨foreignReferences, result⟩ := ih
    exact ⟨foreignReferences, by simpa only [List.append_assoc, List.singleton_append] using result⟩

end LeanCage.Host.Kernel
