import FilesystemPublicationRelease

namespace LeanCage.Host.Kernel

-- §FS-host-boundary.ownership: Keep the actual birth cut and every subsequent
-- source/native/interference row. Ordinary child unlinks cannot publish a scope.
structure ReleaseBirthScopeAt {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    {all : List (ActorTick runtime)} (catalogue : Catalogue runtime all)
    (processed : List (ActorTick runtime)) (population : Population) (family : Family)
    (record : Sigma (RootBirth runtime all)) where
  leading : List (ActorTick runtime)
  trailing : List (ActorTick runtime)
  middle : Family
  trace : processed = leading ++ record.2.tick :: trailing
  count : leading.length = record.2.position
  privateRoot : middle record.1.object = some record.1.object
  release : PublicationReleaseJournal runtime catalogue record.2.tick.after middle trailing population family

def CatalogueReleaseScopes {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    {all : List (ActorTick runtime)} (catalogue : Catalogue runtime all)
    (processed : List (ActorTick runtime)) (population : Population) (family : Family) : Prop :=
  ∀ record ∈ catalogue, Nonempty (ReleaseBirthScopeAt runtime catalogue processed population family record)

theorem PublicationReleaseJournal.append {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {all : List (ActorTick runtime)} {catalogue : Catalogue runtime all}
    {before middle after : Population} {first next final : Family} {leading trailing : List (ActorTick runtime)}
    (initial : PublicationReleaseJournal runtime catalogue before first leading middle next)
    (last : PublicationReleaseJournal runtime catalogue middle next trailing after final) :
    PublicationReleaseJournal runtime catalogue before first (leading ++ trailing) after final := by
  induction initial with
  | nil => exact last
  | cons current tail ih => exact .cons current (ih last)

def ReleaseBirthScopeAt.advance {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {all : List (ActorTick runtime)} {oldCatalogue newCatalogue : Catalogue runtime all}
    {processed : List (ActorTick runtime)} {tick : ActorTick runtime} {first final : Family}
    {record : Sigma (RootBirth runtime all)}
    (prior : ReleaseBirthScopeAt runtime oldCatalogue processed tick.before first record)
    (included : ∀ record ∈ oldCatalogue, record ∈ newCatalogue)
    (current : PublicationReleaseStep newCatalogue tick first final) :
    ReleaseBirthScopeAt runtime newCatalogue (processed ++ [tick]) tick.after final record := {
  leading := prior.leading
  trailing := prior.trailing ++ [tick]
  middle := prior.middle
  trace := by simp only [prior.trace, List.append_assoc, List.cons_append]
  count := prior.count
  privateRoot := prior.privateRoot
  release := (prior.release.weaken included).append (.cons current (.nil _ _)) }

theorem catalogue_release_scopes_advance {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {all : List (ActorTick runtime)} {oldCatalogue newCatalogue : Catalogue runtime all}
    {processed : List (ActorTick runtime)} {tick : ActorTick runtime} {first final : Family}
    (prior : CatalogueReleaseScopes runtime oldCatalogue processed tick.before first)
    (included : ∀ record ∈ oldCatalogue, record ∈ newCatalogue)
    (newRecords : ∀ record ∈ newCatalogue, record ∈ oldCatalogue ∨
      (record.2.tick = tick ∧ record.2.position = processed.length ∧ final record.1.object = some record.1.object))
    (current : PublicationReleaseStep newCatalogue tick first final) :
    CatalogueReleaseScopes runtime newCatalogue (processed ++ [tick]) tick.after final := by
  intro record member
  rcases newRecords record member with old | ⟨sameTick, position, privateRoot⟩
  · obtain ⟨scope⟩ := prior record old
    exact ⟨scope.advance included current⟩
  · exact ⟨{
      leading := processed
      trailing := []
      middle := final
      trace := by simp only [sameTick]
      count := position.symm
      privateRoot
      release := by rw [sameTick]; exact .nil _ _ }⟩

structure RegisteredPublicationState {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    (initial : World) (all : List (ActorTick runtime)) (hostUid : Nat)
    (dataObjects directories : ObjectId → Prop) (semantics : NameSemanticsView)
    (foreignReferences : ForeignReferences) (processed : List (ActorTick runtime))
    (population : Population) (native : NativeProcesses) where
  custody : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
    foreignReferences processed population native
  releases : CatalogueReleaseScopes runtime custody.current.source.custody.catalogue
    processed population custody.current.source.custody.caps.family

def initial_registered_publication {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    (initial : World) (all : List (ActorTick runtime)) (hostUid : Nat)
    (dataObjects directories : ObjectId → Prop) (semantics : NameSemanticsView)
    (foreignReferences : ForeignReferences) (native : NativeProcesses)
    (wellFormed : NamespaceWellFormed initial)
    (live : ∀ object, foreignReferences object = true → initial.allocated object = true)
    (nativeLive : NativeReferencesLive native initial) :
    RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics foreignReferences []
      (Population.empty initial) native := {
  custody := initial_registered_custody runtime initial all hostUid dataObjects directories semantics foreignReferences native
    wellFormed live nativeLive
  releases := by intro record impossible; cases impossible }

def RegisteredPublicationState.advance {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignBefore foreignAfter : ForeignReferences} {tick : ActorTick runtime} {before after : NativeProcesses}
    (prior : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignBefore processed tick.before before)
    (next : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignAfter (processed ++ [tick]) tick.after after)
    (included : ∀ record ∈ prior.custody.current.source.custody.catalogue, record ∈ next.current.source.custody.catalogue)
    (newRecords : ∀ record ∈ next.current.source.custody.catalogue,
      record ∈ prior.custody.current.source.custody.catalogue ∨
      (record.2.tick = tick ∧ record.2.position = processed.length ∧
        next.current.source.custody.caps.family record.1.object = some record.1.object))
    (release : PublicationReleaseStep next.current.source.custody.catalogue tick
      prior.custody.current.source.custody.caps.family next.current.source.custody.caps.family) :
    RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignAfter (processed ++ [tick]) tick.after after :=
  ⟨next, catalogue_release_scopes_advance prior.releases included newRecords release⟩

def RegisteredPublicationState.preserved {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignBefore foreignAfter : ForeignReferences} {tick : ActorTick runtime} {before after : NativeProcesses}
    (prior : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignBefore processed tick.before before)
    (next : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignAfter (processed ++ [tick]) tick.after after)
    (catalogue : next.current.source.custody.catalogue = prior.custody.current.source.custody.catalogue)
    (labels : ∀ object, tick.before.shared.allocated object = true →
      next.current.source.custody.caps.family object = prior.custody.current.source.custody.caps.family object) :
    RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignAfter (processed ++ [tick]) tick.after after :=
  prior.advance next (by rw [catalogue]; exact fun _ member => member)
    (by intro record member; exact .inl (by rwa [catalogue] at member))
    (publication_release_unchanged _ labels)

def RegisteredPublicationState.creation {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignBefore foreignAfter : ForeignReferences} {tick : ActorTick runtime} {before after : NativeProcesses}
    (prior : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignBefore processed tick.before before)
    (next : CustodyState runtime initial all hostUid dataObjects directories semantics
      foreignAfter (processed ++ [tick]) tick.after after)
    (choice : CurrentRootCreation prior.custody.current.source.custody.caps prior.custody.current.source.custody.catalogue
      next.source.custody.caps next.source.custody.catalogue tick processed.length) :
    RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignAfter (processed ++ [tick]) tick.after after := by
  let registered := prior.custody.creation next choice
  refine prior.advance registered choice.included ?_ (publication_release_unchanged _ choice.labels)
  intro record member
  rcases choice.catalogue_members rfl next.source.custody.namespaceState.registry record member with old | created
  · exact .inl old
  · exact .inr ⟨created.1, created.2.1, created.2.2.1⟩

-- §FS-host-boundary.ownership: Cleanup may unlink children while the actual
-- owner has not published. Derive its current private label from that SAME birth,
-- without a nondestructive-cleanup or current-label premise.
theorem RegisteredPublicationState.unpublished_root {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (lifetimes : LifetimeContract runtime)
    {initial : World} {all processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignReferences : ForeignReferences} {population : Population} {native : NativeProcesses}
    (state : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed population native)
    (record : Sigma (RootBirth runtime all)) (member : record ∈ state.custody.current.source.custody.catalogue)
    (source : ∀ tick ∈ processed, ∀ request observed,
      tick.action.eventFor record.1.actor = some (Program.filesystemPrefixEvent (request, observed)) →
      request.op ≠ .renameNew) :
    state.custody.current.source.custody.caps.family record.1.object = some record.1.object := by
  obtain ⟨scope⟩ := state.releases record member
  apply scope.release.private_label_retained lifetimes state.custody.current.source.custody.valid
    ⟨record, member, rfl, rfl⟩ record.2.fresh.2 scope.privateRoot
  intro tick occurs request observed action
  apply source tick ?_ request observed action
  rw [scope.trace]
  exact List.mem_append.mpr (.inr (List.mem_cons_of_mem _ occurs))

end LeanCage.Host.Kernel
