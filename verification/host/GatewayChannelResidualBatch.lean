import GatewayChannelResidualEffects

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)} {pair : Pair} {Token : Type}

-- §AR-host-boundary.primitives: The direct native receive is processed once
-- by NativeReadRow. This records the other real operations of its interval;
-- residual actor/filesystem reads and all discards are still permitted here.
def ResidualStep
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {initial final : PhysicalState} {record : Record}
    (step : ObservedStep primitive initial record final) : Prop :=
  match step with
  | .read .. => False
  | _ => True

inductive ResidualJournal
    (primitive : Primitive process child native hostUid before after callers next ticks pair Token) :
    Nat → PhysicalState → List Record → PhysicalState → Type 1 where
  | nil (boundary : Nat) (state : PhysicalState) : ResidualJournal primitive boundary state [] state
  | cons {boundary : Nat} {initial middle final : PhysicalState} {record : Record} {records : List Record}
      (order : boundary ≤ record.position) (step : ObservedStep primitive initial record middle)
      (residual : ResidualStep step) (tail : ResidualJournal primitive record.position middle records final) :
      ResidualJournal primitive boundary initial (record :: records) final

noncomputable def ResidualJournal.erase
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {boundary : Nat} {initial final : PhysicalState} {records : List Record}
    (journal : ResidualJournal primitive boundary initial records final) :
    ObservedJournal primitive boundary initial records final := by
  induction journal with
  | nil => exact .nil _ _
  | cons order step residual tail ih => exact .cons order step ih

theorem residual_step_no_caller_read
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {support : Nat → NativeToken → UInt64 → Option Handle} {additional : Nat → ObjectId → Prop}
    (effects : ResidualKernelEffects journal primitive support additional)
    {position : Nat}
    (point : SelectedNativeCut process child native hostUid before after callers next ticks position)
    (selected : selectNativeCut journal position = some point)
    (source : ¬ Nonempty (ResidualReadOrigin point.cut.current (additional position pair.caller) pair.caller))
    {initial final : PhysicalState} {record : Record}
    (step : ObservedStep primitive initial record final) (residual : ResidualStep step)
    (atPosition : record.position = position) :
    ∀ bytes, Action.read .caller bytes ∉ record.actions := by
  cases step with
  | engine | native | observation => simp
  | commit => simp
  | birth => simp
  | read => exact False.elim residual
  | other actualPosition inside state action final actual =>
    have identity : actualPosition = position := atPosition
    subst actualPosition
    intro bytes member
    have identity : action = .read .caller bytes := (List.mem_singleton.mp member).symm
    subst action
    exact source (effects.read position point selected bytes _ final actual)

-- The old ChannelJournal.otherReads field is produced from actual source
-- operand exclusions and a per-op observer, rather than assumed for a batch.
theorem ResidualJournal.no_caller_reads
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {support : Nat → NativeToken → UInt64 → Option Handle} {additional : Nat → ObjectId → Prop}
    (effects : ResidualKernelEffects journal primitive support additional)
    {position : Nat}
    (point : SelectedNativeCut process child native hostUid before after callers next ticks position)
    (selected : selectNativeCut journal position = some point)
    (source : ¬ Nonempty (ResidualReadOrigin point.cut.current (additional position pair.caller) pair.caller))
    {boundary : Nat} {initial final : PhysicalState} {records : List Record}
    (actual : ResidualJournal primitive boundary initial records final)
    (positions : ∀ record ∈ records, record.position = position) :
    ∀ record ∈ records, ∀ bytes, Action.read .caller bytes ∉ record.actions := by
  induction actual with
  | nil => simp
  | cons order step residual tail ih =>
    intro record member
    rcases List.mem_cons.mp member with same | later
    · subst record
      exact residual_step_no_caller_read journal effects point selected source step residual (positions _ (by simp))
    · exact ih (fun record member => positions record (by simp [member])) record later

-- Only residual "other" effects can discard bytes. A canonical receive
-- consumes exactly its product and cannot justify a second hidden consume.
theorem observed_step_no_discard
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {support : Nat → NativeToken → UInt64 → Option Handle} {additional : Nat → ObjectId → Prop}
    (effects : ResidualKernelEffects journal primitive support additional)
    {position : Nat}
    (point : SelectedNativeCut process child native hostUid before after callers next ticks position)
    (selected : selectNativeCut journal position = some point)
    (source : ¬ Nonempty (ResidualDiscardOrigin point.cut.current (support position) (additional position pair.caller) pair.caller))
    {initial final : PhysicalState} {record : Record}
    (step : ObservedStep primitive initial record final) (atPosition : record.position = position) :
    ∀ action ∈ record.actions, preservesReceivedBytes .caller action := by
  cases step with
  | engine | native | observation => simp
  | commit | birth | read => simp [preservesReceivedBytes]
  | other actualPosition inside state action final actual =>
    have identity : actualPosition = position := atPosition
    subst actualPosition
    intro chosen member
    cases List.mem_singleton.mp member
    cases action with
    | discard side bytes =>
      cases side with
      | caller => exact False.elim (source (effects.discard position point selected bytes _ final actual))
      | engine => exact .inl (by intro impossible; cases impossible)
    | born | write | read | closeWrite | eof | quiet => trivial

end LeanCage.Host.PrivateStreams
