import FilesystemForeign
import FilesystemDirectorySources
import FilesystemMarkers
import FilesystemCreationSources

namespace LeanCage.Host.Kernel
open Filesystem

-- §AR-host-boundary.primitives: Size, link count and ordinary contents are not frozen here.
def SameAuthority (before after : Stat) : Prop :=
  after.uid = before.uid ∧ after.mode &&& 1023 = before.mode &&& 1023 ∧
    after.mode &&& 61440 = before.mode &&& 61440

def AuthorityRetained (world : World) (object : ObjectId) : Prop :=
  RetainedObject world object ∨ ∃ name child, world.entries object name = some child

def CanChangeAuthority (caller : Credentials) (information : Stat) : Prop :=
  caller.uid = information.uid ∨ caller.bypassOwner = true

-- §AR-host-boundary.primitives: User markers do not carry POSIX ACL or security-attribute effects.
def AuthoritySafeRequest (request : Request) : Prop :=
  request.op = .setAttribute → TrackedAttribute request.left

def AuthoritySafeEffect {β : Type} : Effect β → Prop
  | .filesystem request => AuthoritySafeRequest request
  | _ => True

-- §AR-host-boundary.primitives: Each rule describes one actual syscall and filesystem identity.
structure AccountContract (kernel : Contract) (hostUid : Nat) : Prop where
  effective : ∀ before after request reply,
    kernel.step before request (some reply) after → request.op = .euid →
    nativeError reply = false → reply.2 = .empty → reply.1.toNat = hostUid
  mkdir_owner : ∀ before after request observed parent object,
    kernel.step before request observed after → request.op = .mkdirAt → request.second = 448 →
    before.handles request.first = some parent → before.allocated object = false →
    after.entries parent.object request.left = some object →
    ∃ information, after.information object = some information ∧ information.uid = hostUid ∧
      information.directory = true ∧ information.mode &&& 63 = 0
  authority_existing : ∀ before after request observed object information,
    kernel.step before request observed after → AuthoritySafeRequest request →
    before.information object = some information → AuthorityRetained after object →
    ∃ later, after.information object = some later ∧ SameAuthority information later

structure ForeignAuthorityContract {kernel : Contract} (runtime : ActorRuntime kernel) : Prop where
  change : ∀ caller before after object information,
    runtime.foreign caller before after → before.information object = some information →
    AuthorityRetained after object →
    (∃ later, after.information object = some later ∧ SameAuthority information later) ∨
      CanChangeAuthority caller information

-- §AR-host-boundary.primitives: Child filesystem actions stay separate from this parent call.
structure RuntimeAuthorityContract {kernel : Contract} (runtime : ActorRuntime kernel) : Prop where
  other : ∀ {β : Type} actor (effect : Effect β) reply before after object information,
    runtime.other actor effect reply before after → before.information object = some information →
    AuthorityRetained after object →
    ∃ later, after.information object = some later ∧ SameAuthority information later

theorem same_authority_trans {first middle last : Stat}
    (initial : SameAuthority first middle) (final : SameAuthority middle last) : SameAuthority first last :=
  ⟨final.1.trans initial.1, final.2.1.trans initial.2.1, final.2.2.trans initial.2.2⟩

theorem same_authority_regular {before after : Stat} (same : SameAuthority before after) :
    after.regular = before.regular := by
  simp only [Stat.regular, same.2.2]

theorem same_authority_directory {before after : Stat} (same : SameAuthority before after) :
    after.directory = before.directory := by
  simp only [Stat.directory, same.2.2]

theorem same_authority_mask {before after : Stat} (same : SameAuthority before after)
    (mask : Nat) (inside : 1023 &&& mask = mask) : after.mode &&& mask = before.mode &&& mask := by
  calc
    after.mode &&& mask = (after.mode &&& 1023) &&& mask := by rw [Nat.and_assoc, inside]
    _ = (before.mode &&& 1023) &&& mask := by rw [same.2.1]
    _ = before.mode &&& mask := by rw [Nat.and_assoc, inside]

theorem same_authority_trusted (uid : Nat) {before after : Stat} (same : SameAuthority before after) :
    Directories.trusted uid after = Directories.trusted uid before := by
  simp only [Directories.trusted, same_authority_directory same, same.1,
    same_authority_mask same 18 (by decide), same_authority_mask same 512 (by decide)]

theorem operation_keeps_authority {kernel : Contract} {runtime : ActorRuntime kernel} {hostUid : Nat}
    (accounts : AccountContract kernel hostUid) (runtimeLaws : RuntimeAuthorityContract runtime)
    {β : Type} {actor : ActorId} {effect : Effect β} {reply : Option β}
    {before after : World} {object : ObjectId} {information : Stat}
    (actual : ActorOperation runtime actor effect reply before after) (source : AuthoritySafeEffect effect)
    (known : before.information object = some information) (retained : AuthorityRetained after object) :
    ∃ later, after.information object = some later ∧ SameAuthority information later := by
  cases effect with
  | filesystem request => exact accounts.authority_existing _ _ _ _ _ _ actual source known retained
  | spawn arguments => exact runtimeLaws.other _ _ _ _ _ _ _ actual known retained
  | read handle amount => exact runtimeLaws.other _ _ _ _ _ _ _ actual known retained
  | wait child => exact runtimeLaws.other _ _ _ _ _ _ _ actual known retained
  | terminate child => exact runtimeLaws.other _ _ _ _ _ _ _ actual known retained
  | tryWait child => exact runtimeLaws.other _ _ _ _ _ _ _ actual known retained
  | descriptor handle => exact runtimeLaws.other _ _ _ _ _ _ _ actual known retained

-- §FS-host-boundary.ownership: Ordinary foreign credentials cannot rewrite host ownership/modes.
theorem foreign_host_authority_retained {kernel : Contract} {runtime : ActorRuntime kernel}
    (laws : ForeignAuthorityContract runtime) {hostUid : Nat} {caller : Credentials}
    {before after : World} {object : ObjectId} {information : Stat}
    (actual : runtime.foreign caller before after) (ordinary : OrdinaryForeign caller hostUid)
    (known : before.information object = some information) (owned : information.uid = hostUid)
    (retained : AuthorityRetained after object) :
    ∃ later, after.information object = some later ∧ SameAuthority information later := by
  rcases laws.change caller before after object information actual known retained with unchanged | permission
  · exact unchanged
  · rcases permission with owner | bypass
    · exact False.elim (ordinary.1 (owner.trans owned))
    · rw [ordinary.2.2.2] at bypass
      cases bypass

theorem foreign_unowned_authority_retained {kernel : Contract} {runtime : ActorRuntime kernel}
    (laws : ForeignAuthorityContract runtime) {caller : Credentials} {before after : World}
    {object : ObjectId} {information : Stat} (actual : runtime.foreign caller before after)
    (foreign : caller.uid ≠ information.uid) (ordinary : caller.bypassOwner = false)
    (known : before.information object = some information) (retained : AuthorityRetained after object) :
    ∃ later, after.information object = some later ∧ SameAuthority information later := by
  rcases laws.change caller before after object information actual known retained with unchanged | permission
  · exact unchanged
  · rcases permission with owner | bypass
    · exact False.elim (foreign owner)
    · rw [ordinary] at bypass
      cases bypass

theorem masked_no_search (caller : Credentials) (information : Stat)
    (foreign : caller.uid ≠ information.uid) (ordinary : caller.bypassDac = false)
    (mode : information.mode &&& 63 = 0) : ¬ CanSearch caller information := by
  have group := masked_bits information.mode 63 8 0 (by decide) mode
  have other := masked_bits information.mode 63 1 0 (by decide) mode
  have groupZero : information.mode &&& 8 = 0 := by simpa using group
  have otherZero : information.mode &&& 1 = 0 := by simpa using other
  simp [CanSearch, ordinary, foreign, groupZero, otherZero]

theorem masked_no_write (caller : Credentials) (information : Stat)
    (foreign : caller.uid ≠ information.uid) (ordinary : caller.bypassDac = false)
    (mode : information.mode &&& 63 = 0) : ¬ CanWrite caller information := by
  have group := masked_bits information.mode 63 16 0 (by decide) mode
  have other := masked_bits information.mode 63 2 0 (by decide) mode
  have groupZero : information.mode &&& 16 = 0 := by simpa using group
  have otherZero : information.mode &&& 2 = 0 := by simpa using other
  simp [CanWrite, ordinary, foreign, groupZero, otherZero]

-- §FS-host-boundary.ownership: The before-open interval uses mkdir's actual new object metadata.
theorem fresh_mkdir_foreign_denied {kernel : Contract} {hostUid : Nat}
    (accounts : AccountContract kernel hostUid) {before after : World}
    {request : Request} {observed : Option Reply} {parent : Handle} {object : ObjectId}
    (actual : kernel.step before request observed after) (mkdir : request.op = .mkdirAt)
    (mode : request.second = 448) (live : before.handles request.first = some parent)
    (fresh : before.allocated object = false) (created : after.entries parent.object request.left = some object)
    (caller : Credentials) (ordinary : OrdinaryForeign caller hostUid) :
    ∃ information, after.information object = some information ∧ information.uid = hostUid ∧
      information.directory = true ∧ ¬ CanSearch caller information ∧ ¬ CanWrite caller information := by
  obtain ⟨information, known, owner, directory, mask⟩ := accounts.mkdir_owner
    _ _ _ _ _ _ actual mkdir mode live fresh created
  have foreign : caller.uid ≠ information.uid := by rw [owner]; exact ordinary.1
  exact ⟨information, known, owner, directory, masked_no_search caller information foreign ordinary.2.2.1 mask,
    masked_no_write caller information foreign ordinary.2.2.1 mask⟩

-- §FS-host-boundary.ownership: Source arguments, actual physical birth and ownership agree.
theorem actual_private_mkdir_birth {kernel : Contract} {runtime : ActorRuntime kernel} {hostUid : Nat}
    (accounts : AccountContract kernel hostUid) (tick : ActorTick runtime)
    (actor : ActorId) (uid : Nat) (parentFd : UInt64) (request : Request) (reply : Reply)
    (before : List (Request × Option Reply)) (source : NewChildCall uid parentFd PrivateNames.prefixText before request)
    (action : tick.action = .returned actor (.filesystem request) reply)
    (acknowledged : reply.1 = 0) (empty : reply.2.isEmpty = true)
    (parentLive : ∃ engine parent, tick.before.actors actor = some engine ∧ engine.references parentFd = some parent) :
    ∃ (object : ObjectId) (parent : Handle) (information : Stat), FreshBirth tick object ∧
      tick.before.shared.entries parent.object request.left = none ∧
      tick.after.shared.entries parent.object request.left = some object ∧
      tick.after.shared.information object = some information ∧ information.uid = hostUid ∧
      information.directory = true ∧ information.mode &&& 63 = 0 ∧
      PrivateNames.reservedBytes request.left = true := by
  have component : Directories.component request.left = true := by
    rw [source.operation]
    exact source.component
  have mkdir : request.op = .mkdirAt := by rw [source.operation]
  have mode : request.second = 448 := by rw [source.operation]
  have fd : request.first = parentFd := by rw [source.operation]
  have reserved : PrivateNames.reservedBytes request.left = true := by
    rw [source.operation]
    exact private_prefix_reserved _
  rcases tick with ⟨kind, population, afterPopulation, operation⟩
  dsimp only at action parentLive ⊢
  subst kind
  cases operation with
  | @returned β population actualActor current effect next actualReply world present alive head actual =>
    obtain ⟨engine, parent, enginePresent, parentReference⟩ := parentLive
    have sameEngine := Option.some.inj (enginePresent.symm.trans present)
    subst engine
    have reference : current.references request.first = some parent := by rw [fd]; exact parentReference
    obtain ⟨object, fresh, allocated, absent, bound⟩ := kernel.mkdir_fresh
      _ _ _ _ _ actual mkdir reference component acknowledged empty
    obtain ⟨information, known, owner, directory, permissions⟩ := accounts.mkdir_owner
      _ _ _ _ _ _ actual mkdir mode reference fresh bound
    exact ⟨object, parent, information, ⟨fresh, allocated⟩, absent, bound, known,
      owner, directory, permissions, reserved⟩

end LeanCage.Host.Kernel
