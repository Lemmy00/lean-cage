import FilesystemLookupSemantics
import FilesystemLookups

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.lookup: A foreign public directory may change its lookup flags after a
-- probe. The operation therefore records the actual stored name and only conditionally equates it.
structure DynamicDataLookupContract (kernel : Contract) (semantics : NameSemanticsView)
    (initialObjects : ObjectId → Bool) (dataObjects : ObjectId → Prop) : Prop where
  child : ∀ before after request reply parent fd handle,
    kernel.step before request (some reply) after → request.op = .openAt →
    (request.second = directoryFlags ∨ request.second = readFlags) →
    before.handles request.first = some parent → descriptor reply = some fd → after.handles fd = some handle →
    Directories.component request.left = true → request.left ≠ ".".toUTF8 → request.left ≠ "..".toUTF8 →
    dataObjects handle.object →
    (∃ storedName, before.entries parent.object storedName = some handle.object ∧
      ((semantics.at before parent.object).byteExact → storedName = request.left)) ∨
      initialObjects handle.object = true
  parent : ∀ before after request reply current fd handle,
    kernel.step before request (some reply) after → request.op = .openAt → request.second = directoryFlags →
    before.handles request.first = some current → request.left = "..".toUTF8 →
    descriptor reply = some fd → after.handles fd = some handle → dataObjects handle.object →
    handle.object = current.object ∨ initialObjects handle.object = true ∨
      ∃ name, before.entries handle.object name = some current.object
  root : ∀ before after request reply fd handle,
    kernel.step before request (some reply) after → request.op = .openAt → request.second = directoryFlags →
    request.first = cwd → request.left = "/".toUTF8 → descriptor reply = some fd →
    after.handles fd = some handle → initialObjects handle.object = true
  cwd : ∀ before after request reply fd handle,
    kernel.step before request (some reply) after → request.op = .openAt → request.second = directoryFlags →
    request.first = Filesystem.cwd → request.left = ".".toUTF8 → descriptor reply = some fd →
    after.handles fd = some handle → handle.object = before.workingDirectory

-- §FS-host-boundary.lookup: Only active public-to-private boundaries need current exact lookup.
-- This is a derived application invariant, not a law freezing public input directories.
def ExactPrivateBoundaries (semantics : NameSemanticsView) (world : World) (family : Family) : Prop :=
  ∀ parent name child scope, world.entries parent name = some child → family child = some scope →
    family parent = none → (semantics.at world parent).byteExact

theorem dynamic_public_child_lookup {kernel : Contract} {semantics : NameSemanticsView}
    {initialObjects : ObjectId → Bool} {dataObjects : ObjectId → Prop}
    (lookup : DynamicDataLookupContract kernel semantics initialObjects dataObjects)
    {before after : World} {family : Family} (graph : FamilyGraph before family initialObjects dataObjects)
    (boundaries : ExactPrivateBoundaries semantics before family)
    {request : Request} {reply : Reply} {parent handle : Handle} {fd : UInt64}
    (actual : kernel.step before request (some reply) after) (opening : request.op = .openAt)
    (flags : request.second = directoryFlags ∨ request.second = readFlags)
    (parentLive : before.handles request.first = some parent) (opened : descriptor reply = some fd)
    (live : after.handles fd = some handle) (component : Directories.component request.left = true)
    (notDot : request.left ≠ ".".toUTF8) (notUp : request.left ≠ "..".toUTF8)
    (publicParent : family parent.object = none) (publicName : PrivateNames.reservedBytes request.left = false) :
    family handle.object = none := by
  cases privateObject : family handle.object with
  | none => rfl
  | some scope =>
    rcases lookup.child _ _ _ _ _ _ _ actual opening flags parentLive opened live component notDot notUp
      (graph.data _ _ privateObject) with ⟨storedName, bound, exactName⟩ | mounted
    · have currentExact := boundaries _ _ _ _ bound privateObject publicParent
      have same := exactName currentExact
      rcases graph.border _ _ _ _ bound privateObject with privateParent | reserved
      · rw [publicParent] at privateParent
        cases privateParent
      · rw [same, publicName] at reserved
        cases reserved.1
    · have young := graph.young _ _ privateObject
      rw [mounted] at young
      cases young

theorem dynamic_public_parent_lookup {kernel : Contract} {semantics : NameSemanticsView}
    {initialObjects : ObjectId → Bool} {dataObjects : ObjectId → Prop}
    (lookup : DynamicDataLookupContract kernel semantics initialObjects dataObjects)
    {before after : World} {family : Family} (graph : FamilyGraph before family initialObjects dataObjects)
    {request : Request} {reply : Reply} {current handle : Handle} {fd : UInt64}
    (actual : kernel.step before request (some reply) after) (opening : request.op = .openAt)
    (flags : request.second = directoryFlags) (currentLive : before.handles request.first = some current)
    (up : request.left = "..".toUTF8) (opened : descriptor reply = some fd) (live : after.handles fd = some handle)
    (publicCurrent : family current.object = none) : family handle.object = none := by
  cases privateObject : family handle.object with
  | none => rfl
  | some scope =>
    rcases lookup.parent _ _ _ _ _ _ _ actual opening flags currentLive up opened live
      (graph.data _ _ privateObject) with same | mounted | ⟨name, entry⟩
    · rw [same, publicCurrent] at privateObject
      cases privateObject
    · have young := graph.young _ _ privateObject
      rw [mounted] at young
      cases young
    · have descendant := graph.descendants _ _ _ _ entry privateObject
      rw [publicCurrent] at descendant
      cases descendant

theorem dynamic_public_directory_open {kernel : Contract} {semantics : NameSemanticsView}
    {initialObjects : ObjectId → Bool} {dataObjects : ObjectId → Prop}
    (namespaceLaws : NamespaceContract kernel)
    (lookup : DynamicDataLookupContract kernel semantics initialObjects dataObjects)
    {before after : World} {family : Family} (graph : FamilyGraph before family initialObjects dataObjects)
    (boundaries : ExactPrivateBoundaries semantics before family)
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
    · exact dynamic_public_parent_lookup lookup graph actual opening flags parentLive up opened live publicParent
    · exact dynamic_public_child_lookup lookup graph boundaries actual opening (.inl flags) parentLive opened live
        component dot up publicParent publicName

end LeanCage.Host.Kernel
