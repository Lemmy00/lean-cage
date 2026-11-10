import FilesystemPublicationProgress

namespace LeanCage.Host.Kernel

-- §FS-host-boundary.ownership: Ownership and label retention share every
-- intermediate family in this application-built prefix. Independent equal
-- endpoint witnesses cannot supply those intermediate labels.
structure RetainedOwnershipStep {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {all : List (ActorTick runtime)} (catalogue : Catalogue runtime all)
    (tick : ActorTick runtime) (first final : Family) : Prop where
  ownership : CustodyOwnershipStep catalogue tick first final
  labels : ExistingLabels tick.before.shared tick.after.shared first final

inductive RetainedOwnershipJournal {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    {all : List (ActorTick runtime)} (catalogue : Catalogue runtime all) :
    Population → Family → List (ActorTick runtime) → Population → Family → Prop where
  | nil (population : Population) (family : Family) :
      RetainedOwnershipJournal runtime catalogue population family [] population family
  | cons {tick : ActorTick runtime} {ticks : List (ActorTick runtime)} {after : Population}
      {first middle final : Family} (step : RetainedOwnershipStep catalogue tick first middle)
      (tail : RetainedOwnershipJournal runtime catalogue tick.after middle ticks after final) :
      RetainedOwnershipJournal runtime catalogue tick.before first (tick :: ticks) after final

theorem RetainedOwnershipJournal.weaken {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {all : List (ActorTick runtime)} {oldCatalogue newCatalogue : Catalogue runtime all}
    (included : ∀ record ∈ oldCatalogue, record ∈ newCatalogue)
    {before after : Population} {first final : Family} {ticks : List (ActorTick runtime)}
    (source : RetainedOwnershipJournal runtime oldCatalogue before first ticks after final) :
    RetainedOwnershipJournal runtime newCatalogue before first ticks after final := by
  induction source with
  | nil => exact .nil _ _
  | cons current tail ih => exact .cons ⟨current.ownership.weaken included, current.labels⟩ ih

theorem RetainedOwnershipJournal.append {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {all : List (ActorTick runtime)} {catalogue : Catalogue runtime all}
    {before middle after : Population} {first between final : Family} {leading trailing : List (ActorTick runtime)}
    (source : RetainedOwnershipJournal runtime catalogue before first leading middle between)
    (tail : RetainedOwnershipJournal runtime catalogue middle between trailing after final) :
    RetainedOwnershipJournal runtime catalogue before first (leading ++ trailing) after final := by
  induction source with
  | nil => exact tail
  | cons current rest ih => exact .cons current (ih tail)

theorem RetainedOwnershipJournal.ownership {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {all : List (ActorTick runtime)} {catalogue : Catalogue runtime all}
    {before after : Population} {first final : Family} {ticks : List (ActorTick runtime)}
    (source : RetainedOwnershipJournal runtime catalogue before first ticks after final) :
    OwnershipJournal runtime catalogue before first ticks after final := by
  induction source with
  | nil => exact .nil _ _
  | cons current tail ih => exact .cons current.ownership ih

-- §FS-host-boundary.ownership: A current private label cannot have been
-- cleared and later reassigned to the old lifetime. This backward fact uses
-- every SAME per-operation label update and genuine allocation monotonicity.
theorem RetainedOwnershipJournal.before_label {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (lifetimes : LifetimeContract runtime) {all : List (ActorTick runtime)} {catalogue : Catalogue runtime all}
    {before after : Population} {first final : Family} {ticks : List (ActorTick runtime)}
    (source : RetainedOwnershipJournal runtime catalogue before first ticks after final)
    {object scope : ObjectId} (old : before.shared.allocated object = true) (label : final object = some scope) :
    first object = some scope := by
  induction source with
  | nil => exact label
  | @cons tick ticks after first middle final current tail ih =>
    have middle := ih (actor_step_allocated lifetimes tick.operation object old) label
    rcases current.labels object old with same | publicAfter
    · exact same.symm.trans middle
    · have impossible := publicAfter.symm.trans middle
      cases impossible

-- §FS-host-boundary.ownership: Only the actual owner's destructive call may
-- remove the private binding; that source call must additionally touch this
-- directory/name. Inner child removals are admitted through their real frame.
theorem RetainedOwnershipJournal.private_binding {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (lifetimes : LifetimeContract runtime) {all : List (ActorTick runtime)} {catalogue : Catalogue runtime all}
    {before after : Population} {first final : Family} {ticks : List (ActorTick runtime)}
    (source : RetainedOwnershipJournal runtime catalogue before first ticks after final)
    {observedWorld : World} (valid : catalogue.Valid observedWorld)
    {actor : ActorId} {parent object scope : ObjectId} {name : ByteArray}
    (owned : catalogue.Owns actor scope) (old : before.shared.allocated object = true)
    (label : final object = some scope) (bound : before.shared.entries parent name = some object)
    (sourceFrames : ∀ tick ∈ ticks, ∀ request observed,
      tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)) →
      DestructiveRequest request → tick.before.shared.entries parent name = some object →
      tick.after.shared.entries parent name = some object) :
    after.shared.entries parent name = some object := by
  induction source with
  | nil => exact bound
  | @cons tick ticks after first middle final current tail ih =>
    have middleLabel := tail.before_label lifetimes (actor_step_allocated lifetimes tick.operation object old) label
    have firstLabel := (RetainedOwnershipJournal.cons current (.nil _ _)).before_label lifetimes old middleLabel
    have nextBound : tick.after.shared.entries parent name = some object := by
      by_cases kept : tick.after.shared.entries parent name = some object
      · exact kept
      · obtain ⟨owner, request, observed, action, destructive, ownerScope⟩ :=
          current.ownership.removed parent name object scope bound firstLabel kept
        have same := catalogue_unique_owner valid ownerScope owned
        subst owner
        exact False.elim (kept (sourceFrames tick (by simp) request observed action destructive bound))
    exact ih (actor_step_allocated lifetimes tick.operation object old) label nextBound
      (by intro row member request observed action destructive binding
          exact sourceFrames row (List.mem_cons_of_mem _ member) request observed action destructive binding)

structure RetainedOwnershipCut {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    {all : List (ActorTick runtime)} (catalogue : Catalogue runtime all)
    (before : Population) (first : Family) (ticks : List (ActorTick runtime))
    (after : Population) (final : Family) (position : Nat) (tick : ActorTick runtime) where
  leading : List (ActorTick runtime)
  trailing : List (ActorTick runtime)
  beforeFamily : Family
  afterFamily : Family
  trace : ticks = leading ++ tick :: trailing
  count : leading.length = position
  current : RetainedOwnershipStep catalogue tick beforeFamily afterFamily
  remaining : RetainedOwnershipJournal runtime catalogue tick.after afterFamily trailing after final

theorem RetainedOwnershipJournal.selected_cut {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {all : List (ActorTick runtime)} {catalogue : Catalogue runtime all}
    {before after : Population} {first final : Family} {ticks : List (ActorTick runtime)}
    (source : RetainedOwnershipJournal runtime catalogue before first ticks after final)
    {position : Nat} {tick : ActorTick runtime} (selected : ticks[position]? = some tick) :
    Nonempty (RetainedOwnershipCut runtime catalogue before first ticks after final position tick) := by
  induction source generalizing position with
  | nil => cases selected
  | @cons current ticks after first middle final step tail ih =>
    cases position with
    | zero =>
      have same := Option.some.inj selected
      subst tick
      exact ⟨⟨[], ticks, first, middle, rfl, rfl, step, tail⟩⟩
    | succ position =>
      obtain ⟨cut⟩ := ih selected
      exact ⟨{ cut with
        leading := current :: cut.leading
        trace := by simp only [cut.trace, List.cons_append]
        count := by simp only [List.length_cons, cut.count] }⟩

structure JointPublicationPrefix {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignReferences : ForeignReferences} {population : Population} {native : NativeProcesses}
    (state : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed population native) : Prop where
  history : RetainedOwnershipJournal runtime state.custody.current.source.custody.catalogue
    (Population.empty initial) Capabilities.empty.family processed population state.custody.current.source.custody.caps.family

theorem JointPublicationPrefix.advance {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignBefore foreignAfter : ForeignReferences} {tick : ActorTick runtime} {before after : NativeProcesses}
    {prior : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignBefore processed tick.before before}
    (source : JointPublicationPrefix prior)
    (next : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignAfter (processed ++ [tick]) tick.after after)
    (included : ∀ record ∈ prior.custody.current.source.custody.catalogue,
      record ∈ next.custody.current.source.custody.catalogue)
    (step : RetainedOwnershipStep next.custody.current.source.custody.catalogue tick
      prior.custody.current.source.custody.caps.family next.custody.current.source.custody.caps.family) :
    JointPublicationPrefix next :=
  ⟨(source.history.weaken included).append (.cons step (.nil _ _))⟩

-- §AR-host-boundary.interfaces: A retained-catalogue source case contributes
-- its actual ownership row to the SAME joint prefix; no row is reconstructed
-- from an independently chosen family history.
theorem JointPublicationPrefix.preserved {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignBefore foreignAfter : ForeignReferences} {tick : ActorTick runtime} {before after : NativeProcesses}
    {prior : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignBefore processed tick.before before}
    (joint : JointPublicationPrefix prior)
    (next : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignAfter (processed ++ [tick]) tick.after after)
    (catalogue : next.current.source.custody.catalogue = prior.custody.current.source.custody.catalogue)
    (labels : ∀ object, tick.before.shared.allocated object = true →
      next.current.source.custody.caps.family object = prior.custody.current.source.custody.caps.family object)
    (ownership : CustodyOwnershipStep next.current.source.custody.catalogue tick
      prior.custody.current.source.custody.caps.family next.current.source.custody.caps.family) :
    JointPublicationPrefix (prior.preserved next catalogue labels) := by
  apply joint.advance
  · change ∀ record ∈ prior.custody.current.source.custody.catalogue, record ∈ next.current.source.custody.catalogue
    rw [catalogue]
    exact fun _ member => member
  · exact ⟨ownership, fun object allocated => .inl (labels object allocated)⟩

end LeanCage.Host.Kernel
