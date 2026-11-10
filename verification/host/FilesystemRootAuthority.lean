import FilesystemMetadata

namespace LeanCage.Host.Kernel
open Filesystem

def RootAuthorityAt (world : World) (uid : Nat) (root : PrivateRoot) : Prop :=
  ∃ child parent : Stat, world.information root.object = some child ∧
    world.information root.parent = some parent ∧ child.uid = uid ∧ child.mode &&& 63 = 0 ∧
    child.directory = true ∧ Directories.trusted uid parent = true

def RootAuthorities (caps : Capabilities) (world : World) (uid : Nat) : Prop :=
  ∀ root ∈ caps.roots, RootAuthorityAt world uid root

-- §FS-host-boundary.ownership: Parent and child liveness come from the same retained root entry.
theorem root_authority_after {kernel : Contract} {hostUid : Nat}
    (accounts : AccountContract kernel hostUid) {before after : World}
    {request : Request} {observed : Option Reply} {root : PrivateRoot}
    (actual : kernel.step before request observed after) (source : AuthoritySafeRequest request)
    (authority : RootAuthorityAt before hostUid root)
    (bound : after.entries root.parent root.name = some root.object) : RootAuthorityAt after hostUid root := by
  obtain ⟨child, parent, childKnown, parentKnown, owner, mask, directory, trusted⟩ := authority
  obtain ⟨nextChild, nextChildKnown, childSame⟩ := accounts.authority_existing _ _ _ _ _ _ actual source childKnown
    (.inl (.inr ⟨root.parent, root.name, bound⟩))
  obtain ⟨nextParent, nextParentKnown, parentSame⟩ := accounts.authority_existing _ _ _ _ _ _ actual source parentKnown
    (.inr ⟨root.name, root.object, bound⟩)
  exact ⟨nextChild, nextParent, nextChildKnown, nextParentKnown, childSame.1.trans owner,
    (same_authority_mask childSame 63 (by decide)).trans mask,
    (same_authority_directory childSame).trans directory, (same_authority_trusted _ parentSame).trans trusted⟩

theorem foreign_root_authority_after {kernel : Contract} {runtime : ActorRuntime kernel}
    (laws : ForeignAuthorityContract runtime) {hostUid : Nat} {caller : Credentials}
    {before after : World} {root : PrivateRoot} (actual : runtime.foreign caller before after)
    (ordinary : OrdinaryForeign caller hostUid) (authority : RootAuthorityAt before hostUid root)
    (bound : after.entries root.parent root.name = some root.object) : RootAuthorityAt after hostUid root := by
  obtain ⟨child, parent, childKnown, parentKnown, owner, mask, directory, trusted⟩ := authority
  obtain ⟨nextChild, nextChildKnown, childSame⟩ := foreign_host_authority_retained laws actual ordinary
    childKnown owner (.inl (.inr ⟨root.parent, root.name, bound⟩))
  have parentOwner : parent.uid = hostUid ∨ parent.uid = 0 := by
    have fields : parent.directory = true ∧ (parent.uid = hostUid ∨ parent.uid = 0) ∧
        (parent.mode &&& 18 = 0 ∨ (parent.uid = 0 ∧ parent.mode &&& 512 ≠ 0)) := by
      simpa [Directories.trusted, and_assoc] using trusted
    exact fields.2.1
  have parentForeign : caller.uid ≠ parent.uid := by
    rcases parentOwner with host | root
    · rw [host]; exact ordinary.1
    · rw [root]; exact ordinary.2.1
  obtain ⟨nextParent, nextParentKnown, parentSame⟩ := foreign_unowned_authority_retained laws actual
    parentForeign ordinary.2.2.2 parentKnown (.inr ⟨root.name, root.object, bound⟩)
  exact ⟨nextChild, nextParent, nextChildKnown, nextParentKnown, childSame.1.trans owner,
    (same_authority_mask childSame 63 (by decide)).trans mask,
    (same_authority_directory childSame).trans directory, (same_authority_trusted _ parentSame).trans trusted⟩

-- §FS-host-boundary.ownership: This is derived from real DAC/sticky checks for one foreign step.
theorem ordinary_foreign_preserves_root {kernel : Contract} {runtime : ActorRuntime kernel}
    (laws : ForeignContract runtime) {hostUid : Nat} {caller : Credentials}
    {caps : Capabilities} {before after : World} (actual : runtime.foreign caller before after)
    (ordinary : OrdinaryForeign caller hostUid) (valid : caps.Valid before)
    (authorities : RootAuthorities caps before hostUid) (root : PrivateRoot) (member : root ∈ caps.roots) :
    after.entries root.parent root.name = some root.object := by
  obtain ⟨child, parent, childKnown, parentKnown, owner, _, _, trusted⟩ := authorities root member
  exact foreign_cannot_remove_private_child laws hostUid caller actual ordinary
    (valid.1 root member).2.2.1 parentKnown childKnown trusted owner

theorem ordinary_foreign_root_authorities {kernel : Contract} {runtime : ActorRuntime kernel}
    (namespaceLaws : ForeignContract runtime) (metadata : ForeignAuthorityContract runtime)
    {hostUid : Nat} {caller : Credentials} {caps : Capabilities} {before after : World}
    (actual : runtime.foreign caller before after) (ordinary : OrdinaryForeign caller hostUid)
    (valid : caps.Valid before) (authorities : RootAuthorities caps before hostUid) :
    RootAuthorities caps after hostUid := by
  intro root member
  exact foreign_root_authority_after metadata actual ordinary (authorities root member)
    (ordinary_foreign_preserves_root namespaceLaws actual ordinary valid authorities root member)

-- §FS-host-boundary.ownership: Only metadata from the actual new mkdir enters this registry.
theorem register_actual_root_authority {kernel : Contract} {hostUid : Nat}
    (accounts : AccountContract kernel hostUid) (namespaceLaws : NamespaceContract kernel)
    {caps : Capabilities} {before after : World} {root : PrivateRoot} {request : Request}
    {reply : Reply} {parentHandle : Handle} {parentInformation : Stat}
    (actual : kernel.step before request (some reply) after) (valid : caps.Valid before)
    (authorities : RootAuthorities caps before hostUid) (mkdir : request.op = .mkdirAt)
    (mode : request.second = 448) (component : ComponentRequest request)
    (parentLive : before.handles request.first = some parentHandle) (parentObject : parentHandle.object = root.parent)
    (name : request.left = root.name) (parentKnown : before.information root.parent = some parentInformation)
    (trusted : Directories.trusted hostUid parentInformation = true)
    (fresh : before.allocated root.object = false) (bound : after.entries root.parent root.name = some root.object) :
    RootAuthorities (caps.addRoot root) after hostUid := by
  have source : AuthoritySafeRequest request := by
    intro setting
    rw [mkdir] at setting
    cases setting
  intro query member
  rcases List.mem_cons.mp member with same | old
  · subst query
    have actualBinding : after.entries parentHandle.object request.left = some root.object := by
      rw [parentObject, name]; exact bound
    obtain ⟨child, known, owner, directory, mask⟩ := accounts.mkdir_owner
      _ _ _ _ _ _ actual mkdir mode parentLive fresh actualBinding
    obtain ⟨parent, parentKnownAfter, same⟩ := accounts.authority_existing _ _ _ _ _ _ actual source parentKnown
      (.inr ⟨root.name, root.object, bound⟩)
    exact ⟨child, parent, known, parentKnownAfter, owner, mask, directory,
      (same_authority_trusted _ same).trans trusted⟩
  · have oldBound := (valid.1 query old).2.2.1
    have retained := namespaceLaws.nonremoving_entry _ _ _ _ _ _ _ actual component
      (by rw [mkdir]; decide) (by rw [mkdir]; decide) oldBound
    exact root_authority_after accounts actual source (authorities query old) retained

end LeanCage.Host.Kernel
