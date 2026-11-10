import FilesystemRootAuthority
import FilesystemChanges
import FilesystemChildEffects

namespace LeanCage.Host.Kernel
open Filesystem

-- §AR-host-boundary.primitives: Include pending lookups and ordinary descriptor transfers.
abbrev ForeignReferences := ObjectId → Bool

-- §AR-host-boundary.primitives: Inode type belongs to the lifetime, not its reused number.
def DirectoryView (world : World) (directories : ObjectId → Prop) : Prop :=
  ∀ object information, world.information object = some information →
    (directories object ↔ information.directory = true)

def PrivateDirectoryAuthority (world : World) (family : Family) (hostUid : Nat)
    (directories : ObjectId → Prop) : Prop :=
  ∀ object scope information, family object = some scope →
    world.information object = some information → directories object →
    information.uid = hostUid ∧ information.mode &&& 63 = 0

def PrivateBoundaryAuthority (world : World) (family : Family) (hostUid : Nat) : Prop :=
  ∀ parent name object scope, world.entries parent name = some object →
    family object = some scope → family parent = none →
    ∃ parentInfo childInfo, world.information parent = some parentInfo ∧
      world.information object = some childInfo ∧ Directories.trusted hostUid parentInfo = true ∧
      childInfo.uid = hostUid

def ForeignReferenceSafe (world : World) (family : Family) (directories : ObjectId → Prop)
    (references : ForeignReferences) : Prop :=
  (∀ object, references object = true → world.allocated object = true) ∧
    ∀ object scope, references object = true → family object = some scope → directories object

-- §AR-host-boundary.primitives: Each acquisition uses a real searched binding or old capability.
inductive ForeignAcquisition (world : World) (references : ForeignReferences)
    (initialObjects : ObjectId → Bool) (caller : Credentials) : ObjectId → Prop where
  | retained {object : ObjectId} (held : references object = true) :
      ForeignAcquisition world references initialObjects caller object
  | fresh {object : ObjectId} (newObject : world.allocated object = false) :
      ForeignAcquisition world references initialObjects caller object
  | lookup {parent object : ObjectId} {name : ByteArray} {information : Stat}
      (binding : world.entries parent name = some object)
      (known : world.information parent = some information) (parentDirectory : information.directory = true)
      (searched : CanSearch caller information) :
      ForeignAcquisition world references initialObjects caller object
  | mounted {object : ObjectId} (initialized : initialObjects object = true) :
      ForeignAcquisition world references initialObjects caller object

-- §AR-host-boundary.primitives: Directory aliases require rename permission, not a file hardlink.
inductive ForeignEntryOrigin (world : World) (references : ForeignReferences)
    (directories : ObjectId → Prop) (caller : Credentials) : ObjectId → Prop where
  | fresh {object : ObjectId} (newObject : world.allocated object = false) :
      ForeignEntryOrigin world references directories caller object
  | file {object : ObjectId} (held : references object = true) (notDirectory : ¬ directories object) :
      ForeignEntryOrigin world references directories caller object
  | movedDirectory {parent object : ObjectId} {name : ByteArray} {parentInfo childInfo : Stat}
      (directory : directories object) (binding : world.entries parent name = some object)
      (parentKnown : world.information parent = some parentInfo)
      (childKnown : world.information object = some childInfo)
      (parentDirectory : parentInfo.directory = true)
      (permission : CanRemove caller parentInfo childInfo) :
      ForeignEntryOrigin world references directories caller object

-- §AR-host-boundary.primitives: These are per-operation VFS observations, without family labels.
structure ForeignNamespaceObservation (before after : World) (references result : ForeignReferences)
    (initialObjects : ObjectId → Bool) (directories : ObjectId → Prop) (caller : Credentials) : Prop where
  acquisition : ∀ object, result object = true →
    ForeignAcquisition before references initialObjects caller object
  live : ∀ object, result object = true → after.allocated object = true
  inserted : ∀ parent name object, after.entries parent name = some object →
    before.entries parent name ≠ some object →
    ∃ information, before.information parent = some information ∧ information.directory = true ∧
      CanWrite caller information ∧ CanSearch caller information ∧
      ForeignEntryOrigin before references directories caller object
  inserted_lifetimes : ∀ parent name object, after.entries parent name = some object →
    before.entries parent name ≠ some object →
    before.allocated parent = true ∧ after.allocated object = true

-- §FS-host-boundary.ownership: An O_PATH reference to a root does not grant child lookup rights.
theorem foreign_acquisition_safe {before : World} {family : Family}
    {initialObjects : ObjectId → Bool} {dataObjects directories : ObjectId → Prop}
    {references : ForeignReferences} {caller : Credentials} {hostUid object scope : Nat}
    (graph : FamilyGraph before family initialObjects dataObjects)
    (view : DirectoryView before directories)
    (privateDirectories : PrivateDirectoryAuthority before family hostUid directories)
    (roots : ∀ object owner, family object = some owner → directories owner)
    (safe : ForeignReferenceSafe before family directories references)
    (ordinary : OrdinaryForeign caller hostUid)
    (acquired : ForeignAcquisition before references initialObjects caller object)
    (label : family object = some scope) : directories object := by
  cases acquired with
  | retained held => exact safe.2 object scope held label
  | fresh newObject =>
    have allocated := graph.live object scope label
    rw [newObject] at allocated
    cases allocated
  | lookup binding known parentDirectory searched =>
    rcases graph.border _ _ _ _ binding label with privateParent | root
    · obtain ⟨owner, mode⟩ := privateDirectories _ _ _ privateParent known
        ((view _ _ known).mpr parentDirectory)
      exact False.elim (masked_no_search caller _ (by rw [owner]; exact ordinary.1)
        ordinary.2.2.1 mode searched)
    · rw [root.2]
      exact roots object scope label
  | mounted initialized =>
    have young := graph.young object scope label
    rw [initialized] at young
    cases young

-- §FS-host-boundary.ownership: Existing private directories cannot become foreign rename sources.
theorem foreign_entry_origin_not_private {before : World} {family : Family}
    {initialObjects : ObjectId → Bool} {dataObjects directories : ObjectId → Prop}
    {references : ForeignReferences} {caller : Credentials} {hostUid object scope : Nat}
    (graph : FamilyGraph before family initialObjects dataObjects)
    (view : DirectoryView before directories)
    (privateDirectories : PrivateDirectoryAuthority before family hostUid directories)
    (boundary : PrivateBoundaryAuthority before family hostUid)
    (safe : ForeignReferenceSafe before family directories references)
    (ordinary : OrdinaryForeign caller hostUid)
    (origin : ForeignEntryOrigin before references directories caller object)
    (label : family object = some scope) : False := by
  cases origin with
  | fresh newObject =>
    have allocated := graph.live object scope label
    rw [newObject] at allocated
    cases allocated
  | file held notDirectory => exact notDirectory (safe.2 object scope held label)
  | @movedDirectory parent object name parentInfo childInfo directory binding parentKnown childKnown
      parentDirectory permission =>
    cases parentLabel : family parent with
    | none =>
      obtain ⟨parentObserved, childObserved, observedParent, observedChild, trusted, owner⟩ :=
        boundary _ _ _ _ binding label parentLabel
      have sameParent := Option.some.inj (parentKnown.symm.trans observedParent)
      have sameChild := Option.some.inj (childKnown.symm.trans observedChild)
      subst parentObserved
      subst childObserved
      exact trusted_parent_no_remove caller hostUid _ _ ordinary.1 ordinary.2.1 ordinary.2.2.1
        ordinary.2.2.2 trusted owner permission
    | some parentScope =>
      obtain ⟨owner, mode⟩ := privateDirectories _ _ _ parentLabel parentKnown
        ((view _ _ parentKnown).mpr parentDirectory)
      exact masked_no_search caller _ (by rw [owner]; exact ordinary.1) ordinary.2.2.1 mode permission.2.1

-- §FS-host-boundary.ownership: A private-file alias requires a prior capability.
theorem foreign_private_binding_earlier {before after : World} {family : Family}
    {initialObjects : ObjectId → Bool} {dataObjects directories : ObjectId → Prop}
    {references result : ForeignReferences} {caller : Credentials} {hostUid parent object scope : Nat}
    {name : ByteArray} (graph : FamilyGraph before family initialObjects dataObjects)
    (view : DirectoryView before directories)
    (privateDirectories : PrivateDirectoryAuthority before family hostUid directories)
    (boundary : PrivateBoundaryAuthority before family hostUid)
    (safe : ForeignReferenceSafe before family directories references)
    (ordinary : OrdinaryForeign caller hostUid)
    (actual : ForeignNamespaceObservation before after references result initialObjects directories caller)
    (binding : after.entries parent name = some object) (label : family object = some scope) :
    before.entries parent name = some object := by
  apply Classical.byContradiction
  intro added
  obtain ⟨_, _, _, _, _, origin⟩ := actual.inserted parent name object binding added
  exact foreign_entry_origin_not_private graph view privateDirectories boundary safe ordinary origin label

-- §FS-host-boundary.ownership: Foreign public changes preserve the derived family graph.
theorem foreign_namespace_family {before after : World} {family : Family}
    {initialObjects : ObjectId → Bool} {dataObjects directories : ObjectId → Prop}
    {references result : ForeignReferences} {caller : Credentials} {hostUid : Nat}
    (graph : FamilyGraph before family initialObjects dataObjects)
    (view : DirectoryView before directories)
    (privateDirectories : PrivateDirectoryAuthority before family hostUid directories)
    (boundary : PrivateBoundaryAuthority before family hostUid)
    (safe : ForeignReferenceSafe before family directories references)
    (ordinary : OrdinaryForeign caller hostUid)
    (actual : ForeignNamespaceObservation before after references result initialObjects directories caller)
    (allocation : ∀ object, before.allocated object = true → after.allocated object = true) :
    FamilyGraph after family initialObjects dataObjects := by
  constructor
  · intro object scope label
    exact allocation object (graph.live object scope label)
  · exact graph.young
  · exact graph.data
  · intro parent name object scope binding label
    exact graph.border _ _ _ _
      (foreign_private_binding_earlier graph view privateDirectories boundary safe ordinary actual binding label) label
  · intro parent name object scope binding label
    by_cases previous : before.entries parent name = some object
    · exact graph.descendants _ _ _ _ previous label
    · obtain ⟨information, known, directory, _, searched, _⟩ := actual.inserted _ _ _ binding previous
      obtain ⟨owner, mode⟩ := privateDirectories _ _ _ label known ((view _ _ known).mpr directory)
      exact False.elim (masked_no_search caller _ (by rw [owner]; exact ordinary.1)
        ordinary.2.2.1 mode searched)

theorem foreign_namespace_references {before after : World} {family : Family}
    {initialObjects : ObjectId → Bool} {dataObjects directories : ObjectId → Prop}
    {references result : ForeignReferences} {caller : Credentials} {hostUid : Nat}
    (graph : FamilyGraph before family initialObjects dataObjects)
    (view : DirectoryView before directories)
    (privateDirectories : PrivateDirectoryAuthority before family hostUid directories)
    (roots : ∀ object scope, family object = some scope → directories scope)
    (safe : ForeignReferenceSafe before family directories references)
    (ordinary : OrdinaryForeign caller hostUid)
    (actual : ForeignNamespaceObservation before after references result initialObjects directories caller) :
    ForeignReferenceSafe after family directories result := by
  refine ⟨actual.live, ?_⟩
  intro object scope held label
  exact foreign_acquisition_safe graph view privateDirectories roots safe ordinary
    (actual.acquisition object held) label

theorem foreign_namespace_well_formed {before after : World} {initialObjects : ObjectId → Bool}
    {directories : ObjectId → Prop} {references result : ForeignReferences} {caller : Credentials}
    (actual : ForeignNamespaceObservation before after references result initialObjects directories caller)
    (beforeValid : NamespaceWellFormed before)
    (allocation : ∀ object, before.allocated object = true → after.allocated object = true) :
    NamespaceWellFormed after := by
  intro parent name object binding
  by_cases previous : before.entries parent name = some object
  · have old := beforeValid _ _ _ previous
    exact ⟨allocation _ old.1, allocation _ old.2⟩
  · have live := actual.inserted_lifetimes _ _ _ binding previous
    exact ⟨allocation _ live.1, live.2⟩

-- §FS-host-boundary.ownership: New private births cannot capture an existing foreign reference.
theorem foreign_references_public_retained {before after : World} {family final : Family}
    {directories : ObjectId → Prop} {references : ForeignReferences}
    (safe : ForeignReferenceSafe before family directories references)
    (allocation : ∀ object, before.allocated object = true → after.allocated object = true)
    (publicObjects : PublicRetained before after family final) :
    ForeignReferenceSafe after final directories references := by
  refine ⟨fun object held => allocation object (safe.1 object held), ?_⟩
  intro object scope held label
  cases old : family object with
  | none =>
    have retained := publicObjects object (safe.1 object held) old
    rw [retained] at label
    cases label
  | some owner => exact safe.2 object owner held old

-- §AR-host-boundary.primitives: The pool is sampled at the same global kernel linearization tick.
-- Pending acquisition/commit observations are retained even when one syscall is still in flight.
structure ForeignNamespaceContract {kernel : Contract} (runtime : ActorRuntime kernel)
    (primitive : ChildPrimitive kernel) (hostUid : Nat) (initialObjects : ObjectId → Bool)
    (directories : ObjectId → Prop) where
  step : ActorTick runtime → ForeignReferences → ForeignReferences → Prop
  application : ∀ tick before after, step tick before after →
    (∀ caller, tick.action ≠ .foreign caller) → after = before
  ordinary : ∀ tick before after caller, step tick before after →
    tick.action = .foreign caller → OrdinaryForeign caller hostUid →
    ForeignNamespaceObservation tick.before.shared tick.after.shared before after initialObjects directories caller
  child : ∀ tick before after prior next (_call : ChildCallAt primitive tick prior next),
    step tick before after → after = before

inductive ForeignReferenceJournal {kernel : Contract} {runtime : ActorRuntime kernel}
    {primitive : ChildPrimitive kernel} {hostUid : Nat} {initialObjects : ObjectId → Bool}
    {directories : ObjectId → Prop}
    (contract : ForeignNamespaceContract runtime primitive hostUid initialObjects directories) :
    ForeignReferences → List (ActorTick runtime) → ForeignReferences → Prop where
  | nil (references : ForeignReferences) : ForeignReferenceJournal contract references [] references
  | cons {before middle after : ForeignReferences} {tick : ActorTick runtime} {ticks : List (ActorTick runtime)}
      (actual : contract.step tick before middle)
      (tail : ForeignReferenceJournal contract middle ticks after) :
      ForeignReferenceJournal contract before (tick :: ticks) after

-- §FS-host-boundary.ownership: Source-classified applications/children do not grant SCM_RIGHTS.
theorem foreign_reference_external_step {kernel : Contract} {runtime : ActorRuntime kernel}
    {process : ProcessContract runtime} {primitive : ChildPrimitive kernel} {hostUid : Nat}
    {initialObjects : ObjectId → Bool} {directories : ObjectId → Prop}
    (contract : ForeignNamespaceContract runtime primitive hostUid initialObjects directories)
    {prior next : Processes} {tick : ActorTick runtime} {before after : ForeignReferences}
    (external : ExternalStep process primitive hostUid prior tick next)
    (recorded : contract.step tick before after) :
    after = before ∨ ∃ caller, tick.action = .foreign caller ∧ OrdinaryForeign caller hostUid ∧
      ForeignNamespaceObservation tick.before.shared tick.after.shared before after initialObjects directories caller := by
  cases external with
  | application source notForeign => exact .inl (contract.application _ _ _ recorded notForeign)
  | ordinary caller source action allowed =>
    exact .inr ⟨caller, action, allowed, contract.ordinary _ _ _ _ recorded action allowed⟩
  | child source call => exact .inl (contract.child _ _ _ _ _ call recorded)
  | native source native impossible call => cases impossible

theorem foreign_reference_journal_split {kernel : Contract} {runtime : ActorRuntime kernel}
    {primitive : ChildPrimitive kernel} {hostUid : Nat} {initialObjects : ObjectId → Bool}
    {directories : ObjectId → Prop}
    {contract : ForeignNamespaceContract runtime primitive hostUid initialObjects directories}
    {before after : ForeignReferences} (first last : List (ActorTick runtime))
    (journal : ForeignReferenceJournal contract before (first ++ last) after) :
    ∃ middle, ForeignReferenceJournal contract before first middle ∧
      ForeignReferenceJournal contract middle last after := by
  induction first generalizing before with
  | nil => exact ⟨before, .nil _, journal⟩
  | cons tick ticks ih =>
    cases journal with
    | cons actual rest =>
      obtain ⟨middle, leading, trailing⟩ := ih rest
      exact ⟨middle, .cons actual leading, trailing⟩

end LeanCage.Host.Kernel
