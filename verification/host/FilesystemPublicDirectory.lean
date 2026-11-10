import FilesystemLookups

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: Actual dot/up/ordinary lookups preserve public directory authority.
theorem public_directory_open {kernel : Contract} {initialObjects : ObjectId → Bool}
    {dataObjects : ObjectId → Prop} (namespaceLaws : NamespaceContract kernel)
    (lookup : DataLookupContract kernel initialObjects dataObjects)
    {before after : World} {family : Family} (graph : FamilyGraph before family initialObjects dataObjects)
    {request : Request} {reply : Reply} {parent handle : Handle} {fd : UInt64}
    (actual : kernel.step before request (some reply) after) (opening : request.op = .openAt)
    (flags : request.second = directoryFlags) (parentLive : before.handles request.first = some parent)
    (opened : descriptor reply = some fd) (live : after.handles fd = some handle)
    (component : Directories.component request.left = true) (publicParent : family parent.object = none)
    (publicName : PrivateNames.reservedBytes request.left = false) : family handle.object = none := by
  by_cases dot : request.left = ".".toUTF8
  · obtain ⟨aliasHandle, aliasLive, sameObject⟩ := namespaceLaws.open_dot _ _ _ _ _ _
      actual opening flags parentLive dot opened
    have same := Option.some.inj (live.symm.trans aliasLive)
    subst aliasHandle
    rw [sameObject]
    exact publicParent
  · by_cases up : request.left = "..".toUTF8
    · exact public_parent_lookup lookup graph actual opening flags parentLive up opened live publicParent
    · exact public_child_lookup lookup graph actual opening (.inl flags) parentLive opened live
        component dot up publicParent publicName

-- §FS-host-boundary.ownership: Existing data bindings and initial mount objects cover the result.
theorem public_directory_open_after {kernel : Contract} {initialObjects : ObjectId → Bool}
    {dataObjects : ObjectId → Prop} (descriptors : DescriptorContract kernel)
    (namespaceLaws : NamespaceContract kernel) (lookup : DataLookupContract kernel initialObjects dataObjects)
    {before after : World} {first final : Family}
    (beforeGraph : FamilyGraph before first initialObjects dataObjects)
    (afterGraph : FamilyGraph after final initialObjects dataObjects)
    (wellFormed : NamespaceWellFormed before)
    (publicObjects : ∀ object, before.allocated object = true → first object = none → final object = none)
    {request : Request} {reply : Reply} {parent handle : Handle} {fd : UInt64}
    (actual : kernel.step before request (some reply) after) (opening : request.op = .openAt)
    (flags : request.second = directoryFlags) (parentLive : before.handles request.first = some parent)
    (opened : descriptor reply = some fd) (live : after.handles fd = some handle)
    (component : Directories.component request.left = true) (publicParent : first parent.object = none)
    (publicName : PrivateNames.reservedBytes request.left = false) : final handle.object = none := by
  have earlier := public_directory_open namespaceLaws lookup beforeGraph actual opening flags parentLive
    opened live component publicParent publicName
  cases label : final handle.object with
  | none => rfl
  | some scope =>
    rw [← label]
    have data := afterGraph.data handle.object scope label
    have initialized : initialObjects handle.object = true → final handle.object = none :=
      family_initial_public afterGraph handle.object
    by_cases dot : request.left = ".".toUTF8
    · obtain ⟨aliasHandle, aliasLive, sameObject⟩ := namespaceLaws.open_dot _ _ _ _ _ _
        actual opening flags parentLive dot opened
      have same := Option.some.inj (live.symm.trans aliasLive)
      subst aliasHandle
      apply publicObjects _ _ earlier
      rw [sameObject]
      exact descriptors.reference_allocated _ _ _ _ _ _ actual parentLive
    · by_cases up : request.left = "..".toUTF8
      · rcases lookup.parent _ _ _ _ _ _ _ actual opening flags parentLive up opened live data with
          sameObject | mounted | ⟨name, binding⟩
        · apply publicObjects _ _ earlier
          rw [sameObject]
          exact descriptors.reference_allocated _ _ _ _ _ _ actual parentLive
        · exact initialized mounted
        · exact publicObjects _ (wellFormed _ _ _ binding).1 earlier
      · rcases lookup.child _ _ _ _ _ _ _ actual opening (.inl flags) parentLive opened live component dot up data
          with binding | mounted
        · exact publicObjects _ (wellFormed _ _ _ binding).2 earlier
        · exact initialized mounted

end LeanCage.Host.Kernel
