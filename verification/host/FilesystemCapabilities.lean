import FilesystemBirths
import FilesystemForeign
import RunDirectoryProofs.Cleanup

namespace LeanCage.Host.Kernel
open Filesystem

structure PrivateRoot where
  actor : ActorId
  object : ObjectId
  parent : ObjectId
  name : ByteArray

structure Capabilities where
  roots : List PrivateRoot
  family : ObjectId → Option ObjectId

def Capabilities.empty : Capabilities := ⟨[], fun _ => none⟩

def Capabilities.addRoot (caps : Capabilities) (root : PrivateRoot) : Capabilities :=
  ⟨root :: caps.roots, fun object => if object = root.object then some root.object else caps.family object⟩

def Capabilities.retain (caps : Capabilities) (world : World) : Capabilities :=
  { caps with roots := caps.roots.filter fun root => world.entries root.parent root.name == some root.object }

-- §FS-host-boundary.ownership: These facts are maintained from actual birth and lookup operations.
def Capabilities.Valid (caps : Capabilities) (world : World) : Prop :=
  (∀ root ∈ caps.roots,
    world.allocated root.object = true ∧ world.allocated root.parent = true ∧
    world.entries root.parent root.name = some root.object ∧
    caps.family root.object = some root.object ∧ caps.family root.parent = none) ∧
  (∀ first ∈ caps.roots, ∀ second ∈ caps.roots, first.object = second.object → first = second)

theorem empty_capabilities_valid (world : World) : Capabilities.empty.Valid world := by
  constructor <;> intro root impossible <;> cases impossible

def RootEntry (world : World) (request : Request) (root : PrivateRoot) : Prop :=
  NamesEntry world request.first request.left root.parent root.name

-- §FS-host-boundary.ownership: Source producers distinguish own-root removal from own descendants.
def OwnedRemoval (caps : Capabilities) (world : World) (actor : ActorId) (request : Request) : Prop :=
  (∃ root ∈ caps.roots, root.actor = actor ∧ RootEntry world request root) ∨
  (request.op = .unlinkAt ∧ ∃ root ∈ caps.roots, root.actor = actor ∧
    ∃ handle, world.handles request.first = some handle ∧ caps.family handle.object = some root.object)

theorem own_removal_excludes_peer_root {caps : Capabilities} {world : World} {actor : ActorId}
    {request : Request} {root : PrivateRoot} (valid : caps.Valid world)
    (member : root ∈ caps.roots) (peer : root.actor ≠ actor) (owned : OwnedRemoval caps world actor request) :
    ¬ RootEntry world request root := by
  intro touches
  rcases touches with ⟨handle, reference, parent, name⟩
  rcases owned with ⟨other, otherMember, otherOwner, otherEntry⟩ |
      ⟨unlink, other, otherMember, otherOwner, descriptor, descriptorLive, family⟩
  · obtain ⟨otherHandle, otherReference, otherParent, otherName⟩ := otherEntry
    have sameHandle := Option.some.inj (reference.symm.trans otherReference)
    subst otherHandle
    have sameParent : root.parent = other.parent := parent.symm.trans otherParent
    have sameName : root.name = other.name := name.symm.trans otherName
    have firstBound := (valid.1 root member).2.2.1
    have secondBound := (valid.1 other otherMember).2.2.1
    rw [sameParent, sameName, secondBound] at firstBound
    have sameObject := (Option.some.inj firstBound).symm
    have sameRoot := valid.2 root member other otherMember sameObject
    subst other
    exact peer otherOwner
  · have sameHandle := Option.some.inj (reference.symm.trans descriptorLive)
    subst descriptor
    have publicParent := (valid.1 root member).2.2.2.2
    rw [parent, publicParent] at family
    cases family

-- §FS-host-boundary.ownership: Existing peer roots survive every actual owned syscall, including
-- loss.
theorem owned_syscall_preserves_peer_root {kernel : Contract} (laws : NamespaceContract kernel)
    {caps : Capabilities} {before after : World} {request : Request} {observed : Option Reply}
    {actor : ActorId} {root : PrivateRoot} (step : kernel.step before request observed after)
    (valid : caps.Valid before) (member : root ∈ caps.roots) (peer : root.actor ≠ actor)
    (component : ComponentRequest request)
    (source : request.op = .unlinkAt ∨ request.op = .renameNew → OwnedRemoval caps before actor request) :
    after.entries root.parent root.name = some root.object := by
  have bound := (valid.1 root member).2.2.1
  by_cases unlink : request.op = .unlinkAt
  · have notNamed := own_removal_excludes_peer_root valid member peer (source (.inl unlink))
    have untouched : ¬ TouchesEntry before request root.parent root.name := by
      simpa only [TouchesEntry, RootEntry, unlink] using notNamed
    exact untouched_entry laws step component untouched bound
  · by_cases rename : request.op = .renameNew
    · exact laws.rename_other_source _ _ _ _ _ _ _ step rename component bound
        (own_removal_excludes_peer_root valid member peer (source (.inr rename)))
    · exact laws.nonremoving_entry _ _ _ _ _ _ _ step component unlink rename bound

-- §FS-host-boundary.ownership: A fresh physical allocation is distinct from all retained
-- roots/parents.
theorem birth_outside_existing_caps (caps : Capabilities) (world : World) (object : ObjectId)
    (valid : caps.Valid world) (fresh : world.allocated object = false) :
    ∀ root ∈ caps.roots, object ≠ root.object ∧ object ≠ root.parent := by
  intro root member
  obtain ⟨allocated, parentAllocated, _⟩ := valid.1 root member
  constructor
  · intro same; rw [same, allocated] at fresh; cases fresh
  · intro same; rw [same, parentAllocated] at fresh; cases fresh

-- §FS-host-boundary.ownership: Register exactly the object produced by an actual private mkdir.
theorem register_actual_root {kernel : Contract} (namespaceLaws : NamespaceContract kernel)
    {caps : Capabilities} {before after : World} {root : PrivateRoot} {request : Request} {reply : Reply}
    (step : kernel.step before request (some reply) after) (valid : caps.Valid before)
    (mkdir : request.op = .mkdirAt) (component : ComponentRequest request)
    (fresh : before.allocated root.object = false) (allocated : after.allocated root.object = true)
    (parentAllocated : before.allocated root.parent = true) (publicParent : caps.family root.parent = none)
    (bound : after.entries root.parent root.name = some root.object) :
    (caps.addRoot root).Valid after := by
  have distinct := birth_outside_existing_caps caps before root.object valid fresh
  have parentDifferent : root.parent ≠ root.object := by
    intro same; rw [same, fresh] at parentAllocated; cases parentAllocated
  constructor
  · intro query member
    rcases List.mem_cons.mp member with rfl | old
    · refine ⟨allocated, kernel.allocation_monotone _ _ _ _ _ step parentAllocated, bound, ?_, ?_⟩
      · simp only [Capabilities.addRoot, ite_eq_left]
      · simpa only [Capabilities.addRoot, ite_eq_right parentDifferent] using publicParent
    · obtain ⟨oldAllocated, oldParent, oldBound, oldFamily, oldOutside⟩ := valid.1 query old
      refine ⟨kernel.allocation_monotone _ _ _ _ _ step oldAllocated,
        kernel.allocation_monotone _ _ _ _ _ step oldParent,
        namespaceLaws.nonremoving_entry _ _ _ _ _ _ _ step component
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

theorem retained_capabilities_valid {caps : Capabilities} {before after : World}
    (valid : caps.Valid before)
    (allocation : ∀ object, before.allocated object = true → after.allocated object = true) :
    (caps.retain after).Valid after := by
  constructor
  · intro root member
    have filtered := List.mem_filter.mp member
    obtain ⟨allocated, parentAllocated, _, family, outside⟩ := valid.1 root filtered.1
    exact ⟨allocation _ allocated, allocation _ parentAllocated, by simpa using filtered.2, family, outside⟩
  · intro first firstMember second secondMember same
    exact valid.2 first (List.mem_filter.mp firstMember).1 second (List.mem_filter.mp secondMember).1 same

-- §FS-host-boundary.ownership: A peer cannot silently retire another request's root capability.
theorem peer_root_retained {kernel : Contract} (laws : NamespaceContract kernel)
    {caps : Capabilities} {before after : World} {request : Request} {observed : Option Reply}
    {actor : ActorId} {root : PrivateRoot} (step : kernel.step before request observed after)
    (valid : caps.Valid before) (member : root ∈ caps.roots) (peer : root.actor ≠ actor)
    (component : ComponentRequest request)
    (source : request.op = .unlinkAt ∨ request.op = .renameNew → OwnedRemoval caps before actor request) :
    root ∈ (caps.retain after).roots := by
  apply List.mem_filter.mpr
  exact ⟨member, by simpa using owned_syscall_preserves_peer_root laws step valid member peer component source⟩

-- §FS-host-boundary.ownership: Cleanup's own-family role is obtained from its actual source prefix.
theorem run_cleanup_removal_owned (caps : Capabilities) (world : World) (root : PrivateRoot)
    (owned : RunDirectory.Owned) (member : root ∈ caps.roots) (valid : caps.Valid world)
    (name : owned.name = root.name)
    (directory : ∃ handle, world.handles owned.directory.fd = some handle ∧ handle.object = root.object)
    (container : ∃ handle, world.handles owned.container.fd = some handle ∧ handle.object = root.parent)
    {events : List (Request × Option Reply)} (source : Prefix (RunDirectory.cleanup owned) events)
    (event : Request × Option Reply) (occurs : event ∈ events) (unlink : event.1.op = .unlinkAt) :
    OwnedRemoval caps world root.actor event.1 := by
  have role := RunDirectory.cleanup_request_prefix owned source event occurs
  unfold RunDirectory.CleanupRequest at role
  rw [unlink] at role
  change ((event.1.first = owned.directory.fd ∧ event.1.second = 0 ∧
    event.1.left ∈ ["request.cpio".toUTF8, "control.sock".toUTF8, "policy.json".toUTF8]) ∨
    (event.1.first = owned.container.fd ∧ event.1.second = 512 ∧ event.1.left = owned.name)) at role
  rcases role with ⟨sameFd, _, _⟩ | ⟨sameFd, _, sameName⟩
  · right
    refine ⟨unlink, root, member, rfl, ?_⟩
    obtain ⟨handle, live, object⟩ := directory
    refine ⟨handle, ?_, ?_⟩
    · rw [sameFd]; exact live
    · rw [object]; exact (valid.1 root member).2.2.2.1
  · left
    refine ⟨root, member, rfl, ?_⟩
    obtain ⟨handle, live, parent⟩ := container
    exact ⟨handle, by rw [sameFd]; exact live, parent, sameName.trans name⟩

end LeanCage.Host.Kernel
