import FilesystemRootAuthority
import FilesystemChanges

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: Record committed private births with lost acknowledgements.
theorem register_root_at_commit {kernel : Contract} (namespaceLaws : NamespaceContract kernel)
    {caps : Capabilities} {before after : World} {root : PrivateRoot} {request : Request}
    {observed : Option Reply} (actual : kernel.step before request observed after)
    (valid : caps.Valid before) (mkdir : request.op = .mkdirAt) (component : ComponentRequest request)
    (fresh : before.allocated root.object = false) (allocated : after.allocated root.object = true)
    (parentAllocated : before.allocated root.parent = true) (publicParent : caps.family root.parent = none)
    (bound : after.entries root.parent root.name = some root.object) :
    (caps.addRoot root).Valid after := by
  have distinct := birth_outside_existing_caps caps before root.object valid fresh
  have parentDifferent : root.parent ≠ root.object := by
    intro same
    rw [same, fresh] at parentAllocated
    cases parentAllocated
  constructor
  · intro query member
    rcases List.mem_cons.mp member with rfl | old
    · refine ⟨allocated, kernel.allocation_monotone _ _ _ _ _ actual parentAllocated, bound, ?_, ?_⟩
      · simp only [Capabilities.addRoot, ite_eq_left]
      · simpa only [Capabilities.addRoot, ite_eq_right parentDifferent] using publicParent
    · obtain ⟨oldAllocated, oldParent, oldBound, oldFamily, oldOutside⟩ := valid.1 query old
      refine ⟨kernel.allocation_monotone _ _ _ _ _ actual oldAllocated,
        kernel.allocation_monotone _ _ _ _ _ actual oldParent,
        namespaceLaws.nonremoving_entry _ _ _ _ _ _ _ actual component
          (by rw [mkdir]; decide) (by rw [mkdir]; decide) oldBound, ?_, ?_⟩
      · simpa only [Capabilities.addRoot, ite_eq_right (Ne.symm (distinct query old).1)] using oldFamily
      · simpa only [Capabilities.addRoot, ite_eq_right (Ne.symm (distinct query old).2)] using oldOutside
  · intro first firstMember second secondMember sameObject
    rcases List.mem_cons.mp firstMember with rfl | firstOld
    · rcases List.mem_cons.mp secondMember with rfl | secondOld
      · rfl
      · exact False.elim ((distinct second secondOld).1 sameObject)
    · rcases List.mem_cons.mp secondMember with rfl | secondOld
      · exact False.elim ((distinct first firstOld).1 sameObject.symm)
      · exact valid.2 first firstOld second secondOld sameObject

def Capabilities.addDescendant (caps : Capabilities) (object scope : ObjectId) : Capabilities :=
  { caps with family := setFamily caps.family object scope }

-- §FS-host-boundary.ownership: A private child file does not change an older root's ownership.
theorem register_descendant_at_commit {caps : Capabilities} {before after : World}
    {object scope : ObjectId} (valid : caps.Valid before) (fresh : before.allocated object = false)
    (allocation : ∀ query, before.allocated query = true → after.allocated query = true)
    (bindings : ∀ root ∈ caps.roots, after.entries root.parent root.name = some root.object) :
    (caps.addDescendant object scope).Valid after := by
  have distinct := birth_outside_existing_caps caps before object valid fresh
  constructor
  · intro root member
    obtain ⟨rootAllocated, parentAllocated, _, family, outside⟩ := valid.1 root member
    exact ⟨allocation _ rootAllocated, allocation _ parentAllocated, bindings root member,
      by simpa only [Capabilities.addDescendant, setFamily,
        ite_eq_right (Ne.symm (distinct root member).1)] using family,
      by simpa only [Capabilities.addDescendant, setFamily,
        ite_eq_right (Ne.symm (distinct root member).2)] using outside⟩
  · exact valid.2

-- §FS-host-boundary.ownership: Lost mkdir acknowledgements preserve the same DAC-derived authority.
theorem register_root_authority_at_commit {kernel : Contract} {hostUid : Nat}
    (accounts : AccountContract kernel hostUid) (namespaceLaws : NamespaceContract kernel)
    {caps : Capabilities} {before after : World} {root : PrivateRoot} {request : Request}
    {observed : Option Reply} {parent : Handle} {parentInformation : Stat}
    (actual : kernel.step before request observed after)
    (valid : caps.Valid before) (authorities : RootAuthorities caps before hostUid)
    (mkdir : request.op = .mkdirAt) (mode : request.second = 448)
    (component : ComponentRequest request) (reference : before.handles request.first = some parent)
    (parentObject : parent.object = root.parent) (name : request.left = root.name)
    (parentKnown : before.information root.parent = some parentInformation)
    (trusted : Directories.trusted hostUid parentInformation = true)
    (fresh : before.allocated root.object = false)
    (bound : after.entries root.parent root.name = some root.object) :
    RootAuthorities (caps.addRoot root) after hostUid := by
  have safe : AuthoritySafeRequest request := by
    intro setting
    rw [mkdir] at setting
    cases setting
  have created : after.entries parent.object root.name = some root.object := by
    rw [parentObject]
    exact bound
  obtain ⟨childInformation, childKnown, owner, directory, privateMode⟩ := accounts.mkdir_owner
    _ _ _ _ _ _ actual mkdir mode reference fresh (by simpa only [name] using created)
  obtain ⟨laterParent, laterParentKnown, parentSame⟩ := accounts.authority_existing _ _ _ _ _ _
    actual safe parentKnown (.inr ⟨root.name, root.object, bound⟩)
  intro query member
  rcases List.mem_cons.mp member with rfl | old
  · exact ⟨childInformation, laterParent, childKnown, laterParentKnown, owner, privateMode,
      directory, (same_authority_trusted _ parentSame).trans trusted⟩
  · have oldBound := namespaceLaws.nonremoving_entry _ _ _ _ _ _ _ actual component
      (by rw [mkdir]; decide) (by rw [mkdir]; decide) (valid.1 query old).2.2.1
    exact root_authority_after accounts actual safe (authorities query old) oldBound

theorem retained_registry_authorities {kernel : Contract} {hostUid : Nat}
    (accounts : AccountContract kernel hostUid) {caps : Capabilities} {before after : World}
    {request : Request} {observed : Option Reply} (actual : kernel.step before request observed after)
    (safe : AuthoritySafeRequest request) (authorities : RootAuthorities caps before hostUid) :
    RootAuthorities (caps.retain after) after hostUid := by
  intro root kept
  have retained := List.mem_filter.mp kept
  exact root_authority_after accounts actual safe (authorities root retained.1)
    (by simpa using retained.2)

theorem published_registry_authorities {kernel : Contract} {hostUid : Nat}
    (accounts : AccountContract kernel hostUid) {caps : Capabilities} {before after : World}
    {request : Request} {observed : Option Reply} {object : ObjectId}
    (actual : kernel.step before request observed after) (safe : AuthoritySafeRequest request)
    (authorities : RootAuthorities caps before hostUid) :
    RootAuthorities (caps.published after object) after hostUid :=
  retained_registry_authorities accounts actual safe authorities

end LeanCage.Host.Kernel
