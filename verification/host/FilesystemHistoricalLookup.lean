import FilesystemScopeJournal
import FilesystemDirectoryAliases

namespace LeanCage.Host.Kernel
open Filesystem

private theorem earlier_private {before after : World} {first final : Family}
    (flow : ExistingLabels before after first final) {object scope : ObjectId}
    (allocated : before.allocated object = true) (label : final object = some scope) : first object = some scope := by
  rcases flow object allocated with same | released
  · exact same.symm.trans label
  · rw [label] at released
    cases released

private theorem private_equals_public {before : World} {first final : Family}
    (flow : EqualExistingLabels before first final) {parent child scope : ObjectId}
    (parentLive : before.allocated parent = true) (childLive : before.allocated child = true)
    (parentLabel : first parent = some scope) (childLabel : first child = some scope)
    (publicParent : final parent = none) (privateChild : final child = some scope) : False := by
  have equal := flow parent child parentLive childLive (parentLabel.trans childLabel.symm)
  rw [publicParent, privateChild] at equal
  cases equal

-- §FS-host-boundary.ownership: Interleaved publication declassifies an entire scope. It cannot
-- make a parent public while keeping its old child private, even if the name later changes.
theorem historical_public_directory_open {kernel : Contract} {semantics : NameSemanticsView}
    {initialObjects : ObjectId → Bool} {dataObjects : ObjectId → Prop}
    (descriptors : DescriptorContract kernel) (aliases : DirectoryAliasContract kernel)
    (lookup : DynamicDataLookupContract kernel semantics initialObjects dataObjects)
    {before opened finalWorld : World} {first final : Family}
    (beforeGraph : FamilyGraph before first initialObjects dataObjects)
    (finalGraph : FamilyGraph finalWorld final initialObjects dataObjects)
    (wellFormed : NamespaceWellFormed before) (boundaries : ExactPrivateBoundaries semantics before first)
    (labels : ExistingLabels before finalWorld first final) (equalLabels : EqualExistingLabels before first final)
    {request : Request} {reply : Reply} {parent handle : Handle} {fd : UInt64}
    (actual : kernel.step before request (some reply) opened) (opening : request.op = .openAt)
    (flags : request.second = directoryFlags) (parentLive : before.handles request.first = some parent)
    (recognized : descriptor reply = some fd) (live : opened.handles fd = some handle)
    (component : Directories.component request.left = true) (publicParent : final parent.object = none)
    (publicName : PrivateNames.reservedBytes request.left = false) : final handle.object = none := by
  by_cases dot : request.left = ".".toUTF8
  · obtain ⟨aliasHandle, aliasLive, sameObject⟩ := aliases.dot _ _ _ _ _ _ actual opening flags parentLive dot recognized
    have same := Option.some.inj (live.symm.trans aliasLive)
    subst aliasHandle
    rw [sameObject]
    exact publicParent
  · cases privateChild : final handle.object with
    | none => rfl
    | some scope =>
      have data := finalGraph.data handle.object scope privateChild
      have parentAllocated := descriptors.reference_allocated _ _ _ _ _ _ actual parentLive
      by_cases up : request.left = "..".toUTF8
      · rcases lookup.parent _ _ _ _ _ _ _ actual opening flags parentLive up recognized live data with
          sameObject | mounted | ⟨name, binding⟩
        · rw [sameObject, publicParent] at privateChild
          cases privateChild
        · have young := finalGraph.young _ _ privateChild
          rw [mounted] at young
          cases young
        · have childAllocated := (wellFormed _ _ _ binding).1
          have childLabel := earlier_private labels childAllocated privateChild
          have parentLabel := beforeGraph.descendants _ _ _ _ binding childLabel
          exact False.elim (private_equals_public equalLabels parentAllocated childAllocated
            parentLabel childLabel publicParent privateChild)
      · rcases lookup.child _ _ _ _ _ _ _ actual opening (.inl flags) parentLive recognized live component dot up data with
          ⟨storedName, binding, sameName⟩ | mounted
        · have childAllocated := (wellFormed _ _ _ binding).2
          have childLabel := earlier_private labels childAllocated privateChild
          rcases beforeGraph.border _ _ _ _ binding childLabel with privateParent | reserved
          · exact False.elim (private_equals_public equalLabels parentAllocated childAllocated
              privateParent childLabel publicParent privateChild)
          · cases parentLabel : first parent.object with
            | some owner =>
              have descendant := beforeGraph.descendants _ _ _ _ binding parentLabel
              have sameScope := Option.some.inj (descendant.symm.trans childLabel)
              subst owner
              exact False.elim (private_equals_public equalLabels parentAllocated childAllocated
                parentLabel childLabel publicParent privateChild)
            | none =>
              have exactNames := boundaries _ _ _ _ binding childLabel parentLabel
              have same := sameName exactNames
              rw [same, publicName] at reserved
              cases reserved.1
        · have young := finalGraph.young _ _ privateChild
          rw [mounted] at young
          cases young

def PublicDirectoryOpens (kernel : Contract) (origin : FilesystemOrigin) (family : Family) : Prop :=
  ∀ ordinal before after request reply parent fd handle,
    origin ordinal request reply before after → kernel.step before request (some reply) after →
    request.op = .openAt → request.second = directoryFlags → before.handles request.first = some parent →
    descriptor reply = some fd → after.handles fd = some handle →
    Directories.component request.left = true → PrivateNames.reservedBytes request.left = false →
    family parent.object = none → family handle.object = none

-- §FS-host-boundary.ownership: Every source-used open is sampled at its actual global index.
-- The completed application induction prefix supplies its graph, comparisons and scope flow.
theorem actual_public_directory_opens {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {semantics : NameSemanticsView}
    {initialObjects : ObjectId → Bool} {dataObjects : ObjectId → Prop}
    (descriptors : DescriptorContract kernel) (aliases : DirectoryAliasContract kernel)
    (lifetimes : LifetimeContract runtime)
    (lookup : DynamicDataLookupContract kernel semantics initialObjects dataObjects)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    (selected : ticks[position]? = some tick) (present : tick.before.actors actor = some engine)
    {leading trailing : List (ActorTick runtime)} {first family : Family}
    (shape : ticks = leading ++ tick :: trailing) (count : leading.length = position)
    (prefixLabels : ScopeJournal runtime initialObjects dataObjects semantics
      (Population.empty initial) first leading tick.before family) :
    PublicDirectoryOpens kernel (fun ordinal request reply before after =>
      SourceReturnAt runtime ticks actor ordinal Reply (.filesystem request) reply before after ∧
        ordinal < engine.events.length) family := by
  intro ordinal before after request reply parent fd handle sampled actual opening flags parentLive
    recognized live component publicName publicParent
  obtain ⟨sourcePosition, sourceTick, sourceEngine, afterEngine, sourceAt, action, sourcePresent,
    afterPresent, sourceCount, beforeShape, afterShape⟩ := sampled.1
  have beforeSource : sourceEngine.events.length < engine.events.length := sourceCount ▸ sampled.2
  have earlier := source_ordinal_orders_positions journal sourceAt selected actor sourceEngine engine
    sourcePresent present beforeSource
  have inLeading : sourcePosition < leading.length := by omega
  have selectedBefore : leading[sourcePosition]? = some sourceTick := by
    simpa only [shape, List.getElem?_append_left inLeading] using sourceAt
  obtain ⟨beforeFamily, remaining, graph, wellFormed, boundaries, suffix⟩ := prefixLabels.selected selectedBefore
  have actualGraph : FamilyGraph before beforeFamily initialObjects dataObjects := by
    rw [beforeShape]
    exact ⟨graph.live, graph.young, graph.data, graph.border, graph.descendants⟩
  have actualWellFormed : NamespaceWellFormed before := by
    simpa only [beforeShape, NamespaceWellFormed, Population.project] using wellFormed
  have actualBoundaries : ExactPrivateBoundaries semantics before beforeFamily := by
    simpa only [beforeShape, ExactPrivateBoundaries, NameSemanticsView.at, Population.project] using boundaries
  have labels : ExistingLabels before tick.before.shared beforeFamily family := by
    simpa only [beforeShape, ExistingLabels, Population.project] using family_journal_existing lifetimes suffix.family
  have equalLabels : EqualExistingLabels before beforeFamily family := by
    simpa only [beforeShape, EqualExistingLabels, Population.project] using suffix.equal lifetimes
  exact historical_public_directory_open descriptors aliases lookup actualGraph (family_journal_graph prefixLabels.family).2
    actualWellFormed actualBoundaries labels equalLabels actual opening flags parentLive recognized live component
    publicParent publicName

end LeanCage.Host.Kernel
