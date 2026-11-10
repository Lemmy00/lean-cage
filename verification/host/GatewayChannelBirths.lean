import GatewayChannelHistory
import FilesystemNativeNamespace

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)} {pair : Pair}

-- §FS-host-boundary.ownership: The actual post-socketpair handles establish
-- allocated object lifetimes on that same global boundary.
theorem pair_birth_allocated (namespaceLaws : NativeNamespaceContract native)
    (entry : PairBirthEntry process child native hostUid before after callers next ticks pair) :
    ∀ side, entry.tick.after.shared.allocated (pair.endpoint side) = true := by
  intro side
  have live := namespaceLaws.references_live entry.call
  cases side with
  | caller =>
    apply live
    exact .inl ⟨entry.call.token, entry.call.afterReferences, entry.call.outputTable,
      .inl ⟨entry.first, entry.firstHandle, entry.firstInput, entry.callerObject⟩⟩
  | engine =>
    apply live
    exact .inl ⟨entry.call.token, entry.call.afterReferences, entry.call.outputTable,
      .inl ⟨entry.second, entry.secondHandle, entry.secondInput, entry.engineObject⟩⟩

theorem selected_allocation_before (lifetimes : LifetimeContract runtime)
    {initial final : Population} (journal : ActorJournal runtime initial ticks final)
    {first last : Nat} {earlier later : ActorTick runtime}
    (ordered : first < last) (atFirst : ticks[first]? = some earlier) (atLast : ticks[last]? = some later)
    (object : ObjectId) (allocated : earlier.after.shared.allocated object = true) :
    later.before.shared.allocated object = true := by
  induction first generalizing ticks initial last with
  | zero =>
    cases journal with
    | nil => cases atFirst
    | @cons tick rest final tail =>
      have same := Option.some.inj atFirst
      subst earlier
      cases last with
      | zero => omega
      | succ last =>
        obtain ⟨leading, preceding⟩ := journal_to_selected tail atLast
        exact actor_journal_allocated lifetimes preceding object allocated
  | succ first ih =>
    cases last with
    | zero => omega
    | succ last =>
      cases journal with
      | nil => cases atFirst
      | cons tail => exact ih tail (by omega) atFirst atLast

theorem pair_birth_selected
    (entry : PairBirthEntry process child native hostUid before after callers next ticks pair) :
    ticks[entry.position]? = some entry.tick := by
  have shape := congrArg (fun items : List (ActorTick runtime) => items[entry.position]?) entry.cut.shape
  have inside : (entry.cut.leading ++ entry.tick :: entry.cut.trailing)[entry.position]? = some entry.tick := by
    simp [entry.cut.count]
  exact shape.trans inside

noncomputable def selectedPairObjects
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    (position : Nat) : Option (ObjectId × ObjectId) :=
  match selectNativeCut journal position with
  | none => none
  | some selected =>
    match embeddedNative selected.cut.current with
    | none => none
    | some call =>
      match call.product with
      | .socketPair first second => do
        let left ← call.afterReferences.handles first
        let right ← call.afterReferences.handles second
        return (left.object, right.object)
      | _ => none

-- §AR-host-boundary.interfaces.gateway: Equal global positions use the exact
-- stored call, so an alternate valid witness cannot mint a second pair.
theorem actual_pair_objects
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    (entry : PairBirthEntry process child native hostUid before after callers next ticks pair)
    (actual : ActualPairBirth journal entry) :
    selectedPairObjects journal entry.position = some (pair.caller, pair.engine) := by
  change selectNativeCut journal entry.position = some ⟨entry.tick, entry.cut⟩ at actual
  simp only [selectedPairObjects, actual, entry.embedded, entry.product,
    entry.firstInput, entry.secondInput, bind, Option.bind, pure, entry.callerObject, entry.engineObject]

theorem actual_same_position_pair
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    {other : Pair}
    (first : PairBirthEntry process child native hostUid before after callers next ticks pair)
    (last : PairBirthEntry process child native hostUid before after callers next ticks other)
    (left : ActualPairBirth journal first) (right : ActualPairBirth journal last)
    (same : first.position = last.position) :
    pair.caller = other.caller ∧ pair.engine = other.engine := by
  have initial := actual_pair_objects journal first left
  have final := actual_pair_objects journal last right
  rw [same] at initial
  exact Prod.mk.inj (Option.some.inj (initial.symm.trans final))

-- §FS-host-boundary.ownership: Freshness separates object incarnations across
-- actual global pair births; neither descriptor numbers nor inode guesses do so.
theorem ordered_pair_endpoints_separate (lifetimes : LifetimeContract runtime)
    (namespaceLaws : NativeNamespaceContract native)
    {initial final : Population} (journal : ActorJournal runtime initial ticks final)
    {other : Pair}
    (first : PairBirthEntry process child native hostUid before after callers next ticks pair)
    (last : PairBirthEntry process child native hostUid before after callers next ticks other)
    (ordered : first.position < last.position) (left right : Side) :
    pair.endpoint left ≠ other.endpoint right := by
  intro same
  have old := selected_allocation_before lifetimes journal ordered
    (pair_birth_selected first) (pair_birth_selected last) _ (pair_birth_allocated namespaceLaws first left)
  have fresh : last.tick.before.shared.allocated (other.endpoint right) = false := by
    cases right with
    | caller => exact last.callerFresh
    | engine => exact last.engineFresh
  rw [same, fresh] at old
  cases old

theorem distinct_pair_endpoints_separate (lifetimes : LifetimeContract runtime)
    (namespaceLaws : NativeNamespaceContract native)
    {initial final : Population} (journal : ActorJournal runtime initial ticks final)
    {other : Pair}
    (first : PairBirthEntry process child native hostUid before after callers next ticks pair)
    (last : PairBirthEntry process child native hostUid before after callers next ticks other)
    (different : first.position ≠ last.position) (left right : Side) :
    pair.endpoint left ≠ other.endpoint right := by
  rcases Nat.lt_or_gt_of_ne different with ordered | ordered
  · exact ordered_pair_endpoints_separate lifetimes namespaceLaws journal first last ordered left right
  · exact Ne.symm (ordered_pair_endpoints_separate lifetimes namespaceLaws journal last first ordered right left)

end LeanCage.Host.PrivateStreams
