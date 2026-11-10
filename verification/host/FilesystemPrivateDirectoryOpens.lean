import FilesystemHistoricalLookup
import FilesystemOpenTargets

namespace LeanCage.Host.Kernel
open Filesystem

private theorem earlier_private {before after : World} {first final : Family}
    (flow : ExistingLabels before after first final) {object scope : ObjectId}
    (allocated : before.allocated object = true) (label : final object = some scope) : first object = some scope := by
  rcases flow object allocated with same | released
  · exact same.symm.trans label
  · rw [label] at released
    cases released

-- §FS-host-boundary.ownership: An actual young parent's child lookup has the same
-- scope after every intervening row. Scope publication changes both old labels;
-- it cannot leave a private parent with a differently labelled old descendant.
theorem historical_private_directory_open {kernel : Contract} {semantics : NameSemanticsView}
    {initialObjects : ObjectId → Bool} {dataObjects : ObjectId → Prop}
    (descriptors : DescriptorContract kernel)
    (targets : OpenTargetContract kernel semantics initialObjects dataObjects)
    {before opened finalWorld : World} {first final : Family}
    (graph : FamilyGraph before first initialObjects dataObjects)
    (wellFormed : NamespaceWellFormed before)
    (labels : ExistingLabels before finalWorld first final)
    (equalLabels : EqualExistingLabels before first final)
    {request : Request} {reply : Reply} {parent handle : Handle} {fd : UInt64} {scope : ObjectId}
    (actual : kernel.step before request (some reply) opened) (opening : request.op = .openAt)
    (flags : request.second = directoryFlags) (parentLive : before.handles request.first = some parent)
    (recognized : descriptor reply = some fd) (live : opened.handles fd = some handle)
    (component : Directories.component request.left = true)
    (notDot : request.left ≠ ".".toUTF8) (notUp : request.left ≠ "..".toUTF8)
    (privateParent : final parent.object = some scope) : final handle.object = some scope := by
  have parentAllocated := descriptors.reference_allocated _ _ _ _ _ _ actual parentLive
  have oldParent := earlier_private labels parentAllocated privateParent
  have target := targets.acknowledged descriptors actual opening recognized live
  obtain ⟨storedName, bound, comparison⟩ := targets.young_child _ _ _ _ _ _ actual target opening (.inl flags)
    parentLive component notDot notUp (graph.young _ _ oldParent) (graph.data _ _ oldParent)
  have oldChild := graph.descendants _ _ _ _ bound oldParent
  have childAllocated := (wellFormed _ _ _ bound).2
  exact (equalLabels parent.object handle.object parentAllocated childAllocated
    (oldParent.trans oldChild.symm)).symm.trans privateParent

def PrivateDirectoryOpens (kernel : Contract) (origin : FilesystemOrigin) (family : Family) : Prop :=
  ∀ ordinal before after request reply parent fd handle scope,
    origin ordinal request reply before after → kernel.step before request (some reply) after →
    request.op = .openAt → request.second = directoryFlags → before.handles request.first = some parent →
    descriptor reply = some fd → after.handles fd = some handle →
    Directories.component request.left = true → request.left ≠ ".".toUTF8 → request.left ≠ "..".toUTF8 →
    family parent.object = some scope → family handle.object = some scope

-- §FS-host-boundary.ownership: Sample the exact earlier source ordinal in the
-- constructed global prefix. No independent open, final pathname or helper
-- footprint is used to give the nested descriptor its current private scope.
theorem actual_private_directory_opens {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {semantics : NameSemanticsView}
    {initialObjects : ObjectId → Bool} {dataObjects : ObjectId → Prop}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (targets : OpenTargetContract kernel semantics initialObjects dataObjects)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    (selected : ticks[position]? = some tick) (present : tick.before.actors actor = some engine)
    {leading trailing : List (ActorTick runtime)} {first family : Family}
    (shape : ticks = leading ++ tick :: trailing) (count : leading.length = position)
    (prefixLabels : ScopeJournal runtime initialObjects dataObjects semantics
      (Population.empty initial) first leading tick.before family) :
    PrivateDirectoryOpens kernel (fun ordinal request reply before after =>
      SourceReturnAt runtime ticks actor ordinal Reply (.filesystem request) reply before after ∧
        ordinal < engine.events.length) family := by
  intro ordinal before after request reply parent fd handle scope sampled actual opening flags parentLive
    recognized live component notDot notUp privateParent
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
  have labels : ExistingLabels before tick.before.shared beforeFamily family := by
    simpa only [beforeShape, ExistingLabels, Population.project] using family_journal_existing lifetimes suffix.family
  have equalLabels : EqualExistingLabels before beforeFamily family := by
    simpa only [beforeShape, EqualExistingLabels, Population.project] using suffix.equal lifetimes
  exact historical_private_directory_open descriptors targets actualGraph actualWellFormed labels equalLabels
    actual opening flags parentLive recognized live component notDot notUp privateParent

end LeanCage.Host.Kernel
