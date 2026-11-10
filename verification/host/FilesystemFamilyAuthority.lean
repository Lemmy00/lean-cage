import FilesystemBoundaries
import FilesystemLiveMetadata

namespace LeanCage.Host.Kernel
open Filesystem

def ScopeDirectories (family : Family) (directories : ObjectId → Prop) : Prop :=
  ∀ object scope, family object = some scope → directories scope

theorem empty_scope_directories (directories : ObjectId → Prop) :
    ScopeDirectories (fun _ => none) directories := by
  intro object scope impossible
  cases impossible

theorem set_scope_directories {family : Family} {directories : ObjectId → Prop}
    {object scope : ObjectId} (before : ScopeDirectories family directories) (directory : directories scope) :
    ScopeDirectories (setFamily family object scope) directories := by
  intro query owner label
  by_cases same : query = object
  · subst query
    have actual : scope = owner := Option.some.inj (by simpa only [setFamily, ite_eq_left] using label)
    rw [← actual]
    exact directory
  · exact before query owner (by simpa only [setFamily, ite_eq_right same] using label)

theorem clear_scope_directories {family : Family} {directories : ObjectId → Prop} {scope : ObjectId}
    (before : ScopeDirectories family directories) : ScopeDirectories (clearFamily family scope) directories := by
  intro query owner label
  exact before query owner (clear_family_some label).1

-- §FS-host-boundary.ownership: Old directory authority is derived through the actual physical tick.
theorem retained_private_directory_authority {kernel : Contract} {runtime : ActorRuntime kernel}
    {process : ProcessContract runtime} {primitive : ChildPrimitive kernel} {hostUid : Nat}
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime primitive)
    {prior next : Processes} {tick : ActorTick runtime}
    (source : ExternalStep process primitive hostUid prior tick next) (safe : ExternalAuthoritySafe source)
    {family final : Family} {initialObjects : ObjectId → Bool} {dataObjects directories : ObjectId → Prop}
    (graph : FamilyGraph tick.before.shared family initialObjects dataObjects)
    (authority : PrivateDirectoryAuthority tick.before.shared family hostUid directories)
    (labels : ∀ object scope, final object = some scope → ∃ owner, family object = some owner) :
    PrivateDirectoryAuthority tick.after.shared final hostUid directories := by
  intro object scope information label known directory
  obtain ⟨owner, earlier⟩ := labels object scope label
  have alive : ObjectAlive tick.after.shared object := ⟨information, known⟩
  obtain ⟨oldInformation, oldKnown⟩ := actor_step_live_backward objects tick.operation
    (graph.live object owner earlier) alive
  obtain ⟨oldOwner, oldMode⟩ := authority object owner oldInformation earlier oldKnown directory
  obtain ⟨newInformation, newKnown, same⟩ := external_step_live_authority metadata source safe
    oldKnown (.inl oldOwner) alive
  have sameInformation := Option.some.inj (known.symm.trans newKnown)
  subst newInformation
  exact ⟨same.1.trans oldOwner, (same_authority_mask same 63 (by decide)).trans oldMode⟩

-- §AR-host-boundary.primitives: A successful O_CREAT|O_EXCL creates a nondirectory inode.
-- Fixed lifetime types are independent of finite inode-number reuse and observed permission bits.
structure CreationTypeContract (kernel : Contract) (directories : ObjectId → Prop) : Prop where
  mkdir : ∀ before after request observed parent object,
    kernel.step before request observed after → request.op = .mkdirAt →
    before.handles request.first = some parent → before.allocated object = false →
    after.entries parent.object request.left = some object → directories object
  file : ∀ before after request observed parent object,
    kernel.step before request observed after → request.op = .openAt → request.second = newFileFlags →
    before.handles request.first = some parent → before.allocated object = false →
    after.entries parent.object request.left = some object → ¬ directories object

-- §FS-host-boundary.ownership: Fresh directories use actual mkdir metadata, not a later stat guess.
theorem created_private_directory_authority {kernel : Contract} {hostUid : Nat}
    {directories : ObjectId → Prop} (accounts : AccountContract kernel hostUid)
    (types : CreationTypeContract kernel directories)
    {before after : World} {request : Request} {observed : Option Reply} {parent : Handle} {object : ObjectId}
    (actual : kernel.step before request observed after)
    (operation : request.op = .mkdirAt ∨ (request.op = .openAt ∧ request.second = newFileFlags))
    (mode : request.op = .mkdirAt → request.second = 448)
    (reference : before.handles request.first = some parent) (fresh : before.allocated object = false)
    (bound : after.entries parent.object request.left = some object)
    (directory : directories object) (information : Stat) (known : after.information object = some information) :
    information.uid = hostUid ∧ information.mode &&& 63 = 0 := by
  rcases operation with mkdir | ⟨opening, flags⟩
  · obtain ⟨created, createdKnown, owner, actualDirectory, privateMode⟩ := accounts.mkdir_owner
      _ _ _ _ _ _ actual mkdir (mode mkdir) reference fresh bound
    have same := Option.some.inj (known.symm.trans createdKnown)
    subst created
    exact ⟨owner, privateMode⟩
  · exact False.elim (types.file _ _ _ _ _ _ actual opening flags reference fresh bound directory)

theorem adjoined_private_directory_authority {kernel : Contract} {runtime : ActorRuntime kernel}
    {process : ProcessContract runtime} {primitive : ChildPrimitive kernel} {hostUid : Nat}
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime primitive)
    {prior next : Processes} {tick : ActorTick runtime}
    (source : ExternalStep process primitive hostUid prior tick next) (safe : ExternalAuthoritySafe source)
    {family : Family} {initialObjects : ObjectId → Bool} {dataObjects directories : ObjectId → Prop}
    {object scope : ObjectId} (graph : FamilyGraph tick.before.shared family initialObjects dataObjects)
    (authority : PrivateDirectoryAuthority tick.before.shared family hostUid directories)
    (created : ∀ information, tick.after.shared.information object = some information → directories object →
      information.uid = hostUid ∧ information.mode &&& 63 = 0) :
    PrivateDirectoryAuthority tick.after.shared (setFamily family object scope) hostUid directories := by
  have kept := retained_private_directory_authority objects metadata source safe graph authority
    (fun query owner label => ⟨owner, label⟩)
  intro query owner information label known directory
  by_cases same : query = object
  · subst query
    exact created information known directory
  · exact kept query owner information (by simpa only [setFamily, ite_eq_right same] using label) known directory

end LeanCage.Host.Kernel
