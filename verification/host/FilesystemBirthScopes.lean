import FilesystemOwnershipPrefix
import FilesystemCurrentBirth

namespace LeanCage.Host.Kernel

variable {sourceProgram : Program UInt32}

-- §FS-host-boundary.ownership: Retain the source-created scope at the exact birth point,
-- then the SAME global suffix. Finite inode observations do not identify this lifetime.
structure BirthScopeAt {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram)
    {all : List (ActorTick runtime)} (catalogue : Catalogue runtime all)
    (processed : List (ActorTick runtime)) (population : Population) (family : Family)
    (record : Sigma (RootBirth runtime all)) where
  leading : List (ActorTick runtime)
  trailing : List (ActorTick runtime)
  middle : Family
  trace : processed = leading ++ record.2.tick :: trailing
  count : leading.length = record.2.position
  privateRoot : middle record.1.object = some record.1.object
  parentLive : population.shared.allocated record.1.parent = true
  parentPublic : family record.1.parent = none
  ownership : OwnershipJournal runtime catalogue record.2.tick.after middle trailing population family

def CatalogueBirthScopes {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram)
    {all : List (ActorTick runtime)} (catalogue : Catalogue runtime all)
    (processed : List (ActorTick runtime)) (population : Population) (family : Family) : Prop :=
  ∀ record ∈ catalogue, Nonempty (BirthScopeAt runtime catalogue processed population family record)

def BirthScopeAt.advance {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {all : List (ActorTick runtime)} {oldCatalogue newCatalogue : Catalogue runtime all}
    {processed : List (ActorTick runtime)} {tick : ActorTick runtime} {first final : Family}
    {record : Sigma (RootBirth runtime all)}
    (prior : BirthScopeAt runtime oldCatalogue processed tick.before first record)
    (included : ∀ record ∈ oldCatalogue, record ∈ newCatalogue)
    (step : CustodyOwnershipStep newCatalogue tick first final)
    (labels : ExistingLabels tick.before.shared tick.after.shared first final)
    (allocation : ∀ object, tick.before.shared.allocated object = true → tick.after.shared.allocated object = true) :
    BirthScopeAt runtime newCatalogue (processed ++ [tick]) tick.after final record := {
  leading := prior.leading
  trailing := prior.trailing ++ [tick]
  middle := prior.middle
  trace := by simp only [prior.trace, List.append_assoc, List.cons_append]
  count := prior.count
  privateRoot := prior.privateRoot
  parentLive := allocation _ prior.parentLive
  parentPublic := by
    rcases labels _ prior.parentLive with same | released
    · exact same.trans prior.parentPublic
    · exact released
  ownership := (prior.ownership.weaken included).append (.cons step (.nil _ _)) }

theorem empty_catalogue_birth_scopes {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram)
    (all : List (ActorTick runtime)) (initial : World) :
    CatalogueBirthScopes runtime ([] : Catalogue runtime all) [] (Population.empty initial) Capabilities.empty.family := by
  intro record impossible
  cases impossible

-- §FS-host-boundary.ownership: Every catalogue record keeps its original source birth cut.
-- The exact current insertion choice excludes invented or unrelated extra records.
theorem catalogue_birth_scopes_root_creation {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {all : List (ActorTick runtime)} {oldCatalogue newCatalogue : Catalogue runtime all}
    {before after : Capabilities} {processed : List (ActorTick runtime)} {tick : ActorTick runtime} {position : Nat}
    (choice : CurrentRootCreation before oldCatalogue after newCatalogue tick position)
    (count : processed.length = position)
    (prior : CatalogueBirthScopes runtime oldCatalogue processed tick.before before.family)
    (step : CustodyOwnershipStep newCatalogue tick before.family after.family)
    (valid : after.Valid tick.after.shared)
    (labels : ExistingLabels tick.before.shared tick.after.shared before.family after.family)
    (allocation : ∀ object, tick.before.shared.allocated object = true → tick.after.shared.allocated object = true) :
    CatalogueBirthScopes runtime newCatalogue (processed ++ [tick]) tick.after after.family := by
  cases choice with
  | retained caps catalogue =>
    subst newCatalogue
    intro record member
    obtain ⟨birth⟩ := prior record member
    exact ⟨birth.advance (by intro record member; exact member) step labels allocation⟩
  | created root birth current ordinal caps catalogue =>
    have included : ∀ record ∈ oldCatalogue, record ∈ newCatalogue := by
      intro record member
      rw [catalogue]
      exact List.mem_cons_of_mem _ member
    intro record member
    rw [catalogue] at member
    rcases List.mem_cons.mp member with rfl | old
    · exact ⟨{
        leading := processed
        trailing := []
        middle := after.family
        trace := by rw [current]
        count := count.trans ordinal.symm
        privateRoot := by simp only [caps, Capabilities.addRoot, ite_eq_left]
        parentLive := (valid.1 root (by simp only [caps, Capabilities.addRoot]; exact List.mem_cons_self)).2.1
        parentPublic := (valid.1 root (by simp only [caps, Capabilities.addRoot]; exact List.mem_cons_self)).2.2.2.2
        ownership := by rw [current]; exact .nil _ _ }⟩
    · obtain ⟨earlier⟩ := prior record old
      exact ⟨earlier.advance included step labels allocation⟩

theorem catalogue_birth_scopes_existing {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {all : List (ActorTick runtime)} {oldCatalogue newCatalogue : Catalogue runtime all}
    {processed : List (ActorTick runtime)} {tick : ActorTick runtime} {first final : Family}
    (included : ∀ record ∈ oldCatalogue, record ∈ newCatalogue)
    (old : ∀ record ∈ newCatalogue, record ∈ oldCatalogue)
    (prior : CatalogueBirthScopes runtime oldCatalogue processed tick.before first)
    (step : CustodyOwnershipStep newCatalogue tick first final)
    (labels : ExistingLabels tick.before.shared tick.after.shared first final)
    (allocation : ∀ object, tick.before.shared.allocated object = true → tick.after.shared.allocated object = true) :
    CatalogueBirthScopes runtime newCatalogue (processed ++ [tick]) tick.after final := by
  intro record member
  obtain ⟨birth⟩ := prior record (old record member)
  exact ⟨birth.advance included step labels allocation⟩

-- §FS-host-boundary.ownership: A local source transition accounts for every catalogue entry.
-- New records name THIS source position and its actual private root; old cuts extend unchanged.
theorem catalogue_birth_scopes_advance {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {all : List (ActorTick runtime)} {oldCatalogue newCatalogue : Catalogue runtime all}
    {processed : List (ActorTick runtime)} {tick : ActorTick runtime} {first final : Family}
    (included : ∀ record ∈ oldCatalogue, record ∈ newCatalogue)
    (records : ∀ record ∈ newCatalogue, record ∈ oldCatalogue ∨
      (record.2.tick = tick ∧ record.2.position = processed.length ∧ final record.1.object = some record.1.object ∧
        tick.after.shared.allocated record.1.parent = true ∧ final record.1.parent = none))
    (prior : CatalogueBirthScopes runtime oldCatalogue processed tick.before first)
    (step : CustodyOwnershipStep newCatalogue tick first final)
    (labels : ExistingLabels tick.before.shared tick.after.shared first final)
    (allocation : ∀ object, tick.before.shared.allocated object = true → tick.after.shared.allocated object = true) :
    CatalogueBirthScopes runtime newCatalogue (processed ++ [tick]) tick.after final := by
  intro record member
  rcases records record member with old | ⟨current, ordinal, label, parentLive, parentPublic⟩
  · obtain ⟨birth⟩ := prior record old
    exact ⟨birth.advance included step labels allocation⟩
  · exact ⟨{
      leading := processed
      trailing := []
      middle := final
      trace := by rw [current]
      count := ordinal.symm
      privateRoot := label
      parentLive
      parentPublic
      ownership := by rw [current]; exact .nil _ _ }⟩

theorem CurrentRootCreation.catalogue_members {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {all : List (ActorTick runtime)} {oldCatalogue newCatalogue : Catalogue runtime all}
    {before after : Capabilities} {processed : List (ActorTick runtime)} {tick : ActorTick runtime} {position : Nat}
    (choice : CurrentRootCreation before oldCatalogue after newCatalogue tick position)
    (count : processed.length = position) (valid : after.Valid tick.after.shared) :
    ∀ record ∈ newCatalogue, record ∈ oldCatalogue ∨
      (record.2.tick = tick ∧ record.2.position = processed.length ∧ after.family record.1.object = some record.1.object ∧
        tick.after.shared.allocated record.1.parent = true ∧ after.family record.1.parent = none) := by
  cases choice with
  | retained caps catalogue => intro record member; exact .inl (catalogue ▸ member)
  | created root birth current ordinal caps catalogue =>
    intro record member
    rw [catalogue] at member
    rcases List.mem_cons.mp member with rfl | old
    · have member : root ∈ after.roots := by rw [caps]; exact List.mem_cons_self
      exact .inr ⟨current, ordinal.trans count.symm, by simp only [caps, Capabilities.addRoot, ite_eq_left],
        (valid.1 root member).2.1, (valid.1 root member).2.2.2.2⟩
    · exact .inl old

end LeanCage.Host.Kernel
