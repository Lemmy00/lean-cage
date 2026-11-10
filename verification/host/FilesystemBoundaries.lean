import FilesystemForeignNamespace
import FilesystemRootRegistration

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: Every live private boundary names its actual registered birth.
def RootBoundaries (caps : Capabilities) (world : World) : Prop :=
  ∀ parent name object scope, world.entries parent name = some object →
    caps.family object = some scope → caps.family parent = none →
    ∃ root ∈ caps.roots, root.parent = parent ∧ root.name = name ∧ root.object = object

theorem empty_root_boundaries (world : World) : RootBoundaries Capabilities.empty world := by
  intro parent name object scope binding impossible
  cases impossible

-- §FS-host-boundary.ownership: The boundary's authority comes from that same birth registry.
theorem root_boundaries_authority {caps : Capabilities} {world : World} {hostUid : Nat}
    (boundaries : RootBoundaries caps world) (authorities : RootAuthorities caps world hostUid) :
    PrivateBoundaryAuthority world caps.family hostUid := by
  intro parent name object scope entry label publicParent
  obtain ⟨root, member, parentSame, nameSame, objectSame⟩ := boundaries _ _ _ _ entry label publicParent
  obtain ⟨childInfo, parentInfo, childKnown, parentKnown, owner, mode, directory, trusted⟩ := authorities root member
  exact ⟨parentInfo, childInfo, parentSame ▸ parentKnown, objectSame ▸ childKnown, trusted, owner⟩

-- §FS-host-boundary.ownership: Retire absent bindings and retain each live boundary record.
theorem root_boundaries_retain {caps : Capabilities} {before after : World}
    (boundaries : RootBoundaries caps before)
    (earlier : ∀ parent name object scope, after.entries parent name = some object →
      caps.family object = some scope → before.entries parent name = some object) :
    RootBoundaries (caps.retain after) after := by
  intro parent name object scope entry label publicParent
  obtain ⟨root, member, parentSame, nameSame, objectSame⟩ := boundaries _ _ _ _
    (earlier _ _ _ _ entry label) label publicParent
  refine ⟨root, List.mem_filter.mpr ⟨member, ?_⟩, parentSame, nameSame, objectSame⟩
  have binding : after.entries root.parent root.name = some root.object := by
    rw [parentSame, nameSame, objectSame]
    exact entry
  simpa using binding

-- §FS-host-boundary.ownership: A newly created private root has exactly its own checked binding.
theorem root_boundaries_adjoin {caps : Capabilities} {before after : World} {root : PrivateRoot}
    (boundaries : RootBoundaries caps before) (wellFormed : NamespaceWellFormed before)
    (fresh : before.allocated root.object = false)
    (entries : after.entries = putBinding before.entries root.parent root.name root.object) :
    RootBoundaries (caps.addRoot root) after := by
  classical
  intro parent name object scope entry label publicParent
  rw [entries] at entry
  unfold putBinding at entry
  split at entry
  · rename_i selected
    have same := Option.some.inj entry
    subst object
    exact ⟨root, by simp [Capabilities.addRoot], selected.1.symm, selected.2.symm, rfl⟩
  · have old := wellFormed _ _ _ entry
    have parentDifferent : parent ≠ root.object := by
      intro same
      rw [same, fresh] at old
      cases old.1
    have objectDifferent : object ≠ root.object := by
      intro same
      rw [same, fresh] at old
      cases old.2
    have oldLabel : caps.family object = some scope := by
      simpa only [Capabilities.addRoot, ite_eq_right objectDifferent] using label
    have oldParent : caps.family parent = none := by
      simpa only [Capabilities.addRoot, ite_eq_right parentDifferent] using publicParent
    obtain ⟨existing, member, parents, names, objects⟩ := boundaries _ _ _ _ entry oldLabel oldParent
    exact ⟨existing, by simp [Capabilities.addRoot, member], parents, names, objects⟩

theorem root_boundaries_descendant {caps : Capabilities} {before after : World}
    {object scope parent : ObjectId} {name : ByteArray}
    (boundaries : RootBoundaries caps before) (wellFormed : NamespaceWellFormed before)
    (fresh : before.allocated object = false) (parentAllocated : before.allocated parent = true)
    (privateParent : caps.family parent = some scope)
    (entries : after.entries = putBinding before.entries parent name object) :
    RootBoundaries (caps.addDescendant object scope) after := by
  classical
  have parentDifferent : parent ≠ object := by
    intro same
    rw [same, fresh] at parentAllocated
    cases parentAllocated
  intro query component child owner entry label publicParent
  rw [entries] at entry
  unfold putBinding at entry
  split at entry
  · rename_i selected
    have parentPublic : caps.family parent = none := by
      simpa only [Capabilities.addDescendant, setFamily, selected.1,
        ite_eq_right parentDifferent] using publicParent
    rw [privateParent] at parentPublic
    cases parentPublic
  · have old := wellFormed _ _ _ entry
    have queryDifferent : query ≠ object := by
      intro same
      rw [same, fresh] at old
      cases old.1
    have childDifferent : child ≠ object := by
      intro same
      rw [same, fresh] at old
      cases old.2
    apply boundaries _ _ _ _ entry
    · simpa only [Capabilities.addDescendant, setFamily, ite_eq_right childDifferent] using label
    · simpa only [Capabilities.addDescendant, setFamily, ite_eq_right queryDifferent] using publicParent

theorem root_boundaries_public_birth {caps : Capabilities} {before after : World}
    {initialObjects : ObjectId → Bool} {dataObjects : ObjectId → Prop} {object parent : ObjectId}
    {name : ByteArray} (boundaries : RootBoundaries caps before)
    (graph : FamilyGraph before caps.family initialObjects dataObjects)
    (fresh : before.allocated object = false)
    (entries : after.entries = putBinding before.entries parent name object) :
    RootBoundaries caps after := by
  classical
  intro query component child scope entry label publicParent
  rw [entries] at entry
  unfold putBinding at entry
  split at entry
  · have same := Option.some.inj entry
    subst child
    have allocated := graph.live object scope label
    rw [fresh] at allocated
    cases allocated
  · exact boundaries _ _ _ _ entry label publicParent

-- §FS-host-boundary.publication: The actual move releases that scope, including committed loss.
theorem root_boundaries_published {caps : Capabilities} {before after : World}
    {initialObjects : ObjectId → Bool} {dataObjects : ObjectId → Prop} {root target : ObjectId}
    {name : ByteArray} (boundaries : RootBoundaries caps before)
    (graph : FamilyGraph before caps.family initialObjects dataObjects)
    (rootLabel : caps.family root = some root)
    (entries : ∀ parent component child, after.entries parent component = some child →
      (parent = target ∧ component = name ∧ child = root) ∨ before.entries parent component = some child) :
    RootBoundaries (caps.published after root) after := by
  intro parent component child scope entry label publicParent
  have childLabel := clear_family_some label
  rcases entries _ _ _ entry with moved | previous
  · rw [moved.2.2, rootLabel] at childLabel
    exact False.elim (childLabel.2 (Option.some.inj childLabel.1).symm)
  · have parentBefore : caps.family parent = none := by
      cases earlier : caps.family parent with
      | none => rfl
      | some parentScope =>
        have sameScope : parentScope = scope := Option.some.inj
          ((graph.descendants _ _ _ _ previous earlier).symm.trans childLabel.1)
        have notRoot : parentScope ≠ root := by rw [sameScope]; exact childLabel.2
        have retained : clearFamily caps.family root parent = some parentScope := by
          simp only [clearFamily, earlier, Option.some.injEq, ite_eq_right notRoot]
        have parentNone : clearFamily caps.family root parent = none := publicParent
        rw [retained] at parentNone
        cases parentNone
    obtain ⟨record, member, parents, names, objects⟩ :=
      boundaries _ _ _ _ previous childLabel.1 parentBefore
    refine ⟨record, List.mem_filter.mpr ⟨member, ?_⟩, parents, names, objects⟩
    have binding : after.entries record.parent record.name = some record.object := by
      rw [parents, names, objects]
      exact entry
    simpa using binding

end LeanCage.Host.Kernel
