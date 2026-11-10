import FilesystemRemovalJournal
import FilesystemCustodyPrefix
import FilesystemDescendantPrefix

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

-- §FS-host-boundary.ownership: The custody and removal histories are produced together.
-- Each field concerns the same processed prefix and the same current physical population.
structure OwnershipPrefix {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram)
    (initial : World) (ticks : List (ActorTick runtime)) (hostUid : Nat)
    (dataObjects directories : ObjectId → Prop) (semantics : NameSemanticsView)
    (foreignReferences : ForeignReferences) (processed : List (ActorTick runtime)) (population : Population) where
  custody : CustodyPrefix runtime initial ticks hostUid dataObjects directories semantics
    foreignReferences processed population
  ownership : OwnershipJournal runtime custody.catalogue (Population.empty initial)
    Capabilities.empty.family processed population custody.caps.family

def initial_ownership_prefix {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram)
    (initial : World) (ticks : List (ActorTick runtime)) (hostUid : Nat)
    (dataObjects directories : ObjectId → Prop) (semantics : NameSemanticsView)
    (foreignReferences : ForeignReferences) (wellFormed : NamespaceWellFormed initial)
    (live : ∀ object, foreignReferences object = true → initial.allocated object = true) :
    OwnershipPrefix runtime initial ticks hostUid dataObjects directories semantics foreignReferences [] (Population.empty initial) :=
  ⟨initial_custody_prefix runtime initial ticks hostUid dataObjects directories semantics foreignReferences wellFormed live,
    .nil _ _⟩

-- §FS-host-boundary.ownership: This joins already-proved local source cases, without supplying
-- a private-region frame as a primitive assumption. Catalogue ownership cannot transfer.
def OwnershipPrefix.advance {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {initial : World} {ticks processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignBefore foreignAfter : ForeignReferences} {tick : ActorTick runtime}
    (prior : OwnershipPrefix runtime initial ticks hostUid dataObjects directories semantics
      foreignBefore processed tick.before)
    (next : CustodyPrefix runtime initial ticks hostUid dataObjects directories semantics
      foreignAfter (processed ++ [tick]) tick.after)
    (included : ∀ record ∈ prior.custody.catalogue, record ∈ next.catalogue)
    (source : CustodyOwnershipStep next.catalogue tick prior.custody.caps.family next.caps.family) :
    OwnershipPrefix runtime initial ticks hostUid dataObjects directories semantics
      foreignAfter (processed ++ [tick]) tick.after :=
  ⟨next, (prior.ownership.weaken included).append (.cons source (.nil _ _))⟩

theorem fresh_existing_labels_equal {before : World} {family : Family} {object scope : ObjectId}
    (fresh : before.allocated object = false) :
    ∀ query, before.allocated query = true → setFamily family object scope query = family query := by
  intro query allocated
  have different : query ≠ object := by intro same; rw [same, fresh] at allocated; cases allocated
  simp only [setFamily, ite_eq_right different]

-- §FS-host-boundary.ownership: The source producer retains the SAME birth tick. Merely
-- possessing some historical RootBirth would not establish freshness at this current call.
theorem current_root_creation_labels {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {all : List (ActorTick runtime)} {tick : ActorTick runtime} {position : Nat}
    {before after : Capabilities} {catalogue : Catalogue runtime all}
    (choice : after = before.retain tick.after.shared ∨
      ∃ (root : PrivateRoot) (birth : RootBirth runtime all root),
        birth.tick = tick ∧ birth.position = position ∧ Sigma.mk root birth ∈ catalogue ∧ after = before.addRoot root) :
    ∀ object, tick.before.shared.allocated object = true → after.family object = before.family object := by
  rcases choice with retained | ⟨root, birth, sameTick, samePosition, member, created⟩
  · rw [retained]
    exact fun _ _ => rfl
  · have fresh : tick.before.shared.allocated root.object = false := by rw [← sameTick]; exact birth.fresh.1
    rw [created]
    exact fresh_existing_labels_equal fresh

theorem creation_retains_bindings {dataObjects : ObjectId → Prop} {request : Request} {before after : World}
    (change : DataChange dataObjects request before after)
    (operation : request.op = .mkdirAt ∨ (request.op = .openAt ∧ request.second = newFileFlags)) :
    ∀ parent name object, before.entries parent name = some object → after.entries parent name = some object := by
  rcases entry_delta_cases change operation with unchanged | committed
  · intro parent name object bound
    rw [unchanged]
    exact bound
  · obtain ⟨delta⟩ := committed
    exact fun _ _ _ bound => delta.preserves_binding bound

-- §FS-host-boundary.ownership: An earlier actual root birth and a source read-only interval
-- yield its current binding and private label, including all interleaved verified callers.
theorem ownership_interval_root_binding {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (lifetimes : LifetimeContract runtime) {all : List (ActorTick runtime)} {catalogue : Catalogue runtime all}
    {root : PrivateRoot} (birth : RootBirth runtime all root) (member : Sigma.mk root birth ∈ catalogue)
    {before after : Population} {first final : Family} {ticks : List (ActorTick runtime)}
    (journal : OwnershipJournal runtime catalogue before first ticks after final)
    (valid : catalogue.Valid after.shared) (allocated : before.shared.allocated root.object = true)
    (label : first root.object = some root.object) (bound : before.shared.entries root.parent root.name = some root.object)
    (quiet : ∀ tick ∈ ticks, ∀ request observed,
      tick.action.eventFor root.actor = some (Program.filesystemPrefixEvent (request, observed)) → NamespacePassive request) :
    after.shared.entries root.parent root.name = some root.object ∧ final root.object = some root.object :=
  journal.private_binding_retained lifetimes valid ⟨⟨root, birth⟩, member, rfl, rfl⟩ allocated label bound quiet

end LeanCage.Host.Kernel
