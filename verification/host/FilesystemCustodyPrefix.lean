import FilesystemReferenceCustody
import FilesystemScopeJournal
import FilesystemNamespaceState
import FilesystemBoundaryComparison

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

-- §FS-host-boundary.ownership: These are produced application induction facts over the SAME
-- processed global prefix. No field is a kernel or runtime whole-program safety assumption.
structure CustodyPrefix {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram)
    (initial : World) (ticks : List (ActorTick runtime)) (hostUid : Nat)
    (dataObjects directories : ObjectId → Prop) (semantics : NameSemanticsView)
    (foreignReferences : ForeignReferences) (processed : List (ActorTick runtime)) (population : Population) where
  caps : Capabilities
  catalogue : Catalogue runtime ticks
  namespaceState : NamespaceCustody population.shared caps hostUid initial.allocated dataObjects directories foreignReferences
  names : RegisteredRootNames caps semantics population.shared
  coverage : catalogue.Covers caps
  valid : catalogue.Valid population.shared
  consistent : population.Consistent
  references : EngineReferencesOwned runtime ticks population caps.family catalogue
  history : ScopeJournal runtime initial.allocated dataObjects semantics
    (Population.empty initial) Capabilities.empty.family processed population caps.family

def initial_custody_prefix {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram)
    (initial : World) (ticks : List (ActorTick runtime)) (hostUid : Nat)
    (dataObjects directories : ObjectId → Prop) (semantics : NameSemanticsView)
    (foreignReferences : ForeignReferences) (wellFormed : NamespaceWellFormed initial)
    (live : ∀ object, foreignReferences object = true → initial.allocated object = true) :
    CustodyPrefix runtime initial ticks hostUid dataObjects directories semantics foreignReferences [] (Population.empty initial) := by
  let state := initial_namespace_custody initial hostUid dataObjects directories foreignReferences wellFormed live
  exact {
    caps := .empty
    catalogue := []
    namespaceState := state
    names := empty_registered_root_names semantics initial
    coverage := catalogue_empty_covers runtime ticks
    valid := catalogue_empty_valid runtime ticks initial
    consistent := empty_population_consistent initial
    references := empty_engine_references_owned runtime ticks initial _ []
    history := .nil _ _ state.graph state.wellFormed (registered_boundaries_exact state.boundaries
      (empty_registered_root_names semantics initial)) }

-- §FS-host-boundary.ownership: Actual local source/primitive cases supply the next namespace
-- and exact label update; this joins them with retained birth ownership and reference validity.
def CustodyPrefix.advance {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (referenceLaws : ReferenceContract runtime)
    {initial : World} {ticks processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignBefore foreignAfter : ForeignReferences} {tick : ActorTick runtime}
    (prior : CustodyPrefix runtime initial ticks hostUid dataObjects directories semantics foreignBefore processed tick.before)
    (afterCaps : Capabilities) (afterCatalogue : Catalogue runtime ticks)
    (state : NamespaceCustody tick.after.shared afterCaps hostUid initial.allocated dataObjects directories foreignAfter)
    (names : RegisteredRootNames afterCaps semantics tick.after.shared)
    (coverage : afterCatalogue.Covers afterCaps) (valid : afterCatalogue.Valid tick.after.shared)
    (references : EngineReferencesOwned runtime ticks tick.after afterCaps.family afterCatalogue)
    (update : FamilyUpdate tick.before.shared prior.caps.family afterCaps.family) :
    CustodyPrefix runtime initial ticks hostUid dataObjects directories semantics foreignAfter (processed ++ [tick]) tick.after := {
  caps := afterCaps
  catalogue := afterCatalogue
  namespaceState := state
  names
  coverage
  valid
  consistent := actor_step_consistent descriptors lifetimes referenceLaws tick.operation prior.consistent
  references
  history := prior.history.extend prior.namespaceState.graph prior.namespaceState.wellFormed
    (registered_boundaries_exact prior.namespaceState.boundaries prior.names) update state.graph state.wellFormed
    (registered_boundaries_exact state.boundaries names) }

-- §FS-host-boundary.ownership: A retained-call source case derives all raw-reference custody
-- from the exact selected call. Lost replies and orphaned-but-owned roots remain represented.
def CustodyPrefix.advance_retained {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (referenceLaws : ReferenceContract runtime)
    {initial : World} {ticks processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignBefore foreignAfter : ForeignReferences} {tick : ActorTick runtime}
    (prior : CustodyPrefix runtime initial ticks hostUid dataObjects directories semantics foreignBefore processed tick.before)
    (afterCaps : Capabilities) (afterCatalogue : Catalogue runtime ticks)
    (state : NamespaceCustody tick.after.shared afterCaps hostUid initial.allocated dataObjects directories foreignAfter)
    (names : RegisteredRootNames afterCaps semantics tick.after.shared)
    (coverage : afterCatalogue.Covers afterCaps) (valid : afterCatalogue.Valid tick.after.shared)
    (update : FamilyUpdate tick.before.shared prior.caps.family afterCaps.family)
    (included : ∀ record ∈ prior.catalogue, record ∈ afterCatalogue)
    {actor : ActorId} {request : Request} {observed : Option Reply}
    (selected : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (retaining : RetainsDescriptors request.op) :
    CustodyPrefix runtime initial ticks hostUid dataObjects directories semantics foreignAfter (processed ++ [tick]) tick.after :=
  prior.advance descriptors lifetimes referenceLaws afterCaps afterCatalogue state names coverage valid
    (retained_filesystem_references_owned descriptors selected retaining prior.consistent update.existing included prior.references)
    update

end LeanCage.Host.Kernel
