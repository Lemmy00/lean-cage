import ProgramProofs
import SnapshotProofs
import LeanCageHost.Startup
import LeanCageHost.Directories

namespace LeanCage.Host.Kernel
open Filesystem

abbrev ObjectId := Nat

abbrev DescriptionId := Nat

-- §AR-host-boundary.primitives: Descriptor references are distinct from shared OFD state.
structure Handle where
  object : ObjectId
  description : DescriptionId
  -- §AR-host-boundary.primitives: Original adapter/open request bits, not current F_GETFL.
  flags : UInt64
  rawOwned : Bool

structure Description where
  object : ObjectId
  position : Option Int
  appendMode : Bool

-- §AR-host-boundary.primitives: Track actual raw C-owned/IPC references, not retired SDK leases.
structure World where
  allocated : ObjectId → Bool
  handles : UInt64 → Option Handle
  -- §AR-host-boundary.primitives: Tracked application user attributes, excluding ACL/security data.
  attributes : ObjectId → ByteArray → Option ByteArray
  information : ObjectId → Option Stat
  -- §AR-host-boundary.primitives: Stored data bindings; generated procfs names and mount lookup
  -- have separate relations.
  entries : ObjectId → ByteArray → Option ObjectId
  contents : ObjectId → ByteArray
  closeOnExec : UInt64 → Bool
  descriptionAllocated : DescriptionId → Bool
  -- §AR-host-boundary.primitives: Retired OFDs retain ghost identity records; live positions are
  -- actual.
  descriptions : DescriptionId → Option Description
  workingDirectory : ObjectId
  -- §FS-host-boundary.lookup: Live inode flags may change on foreign-owned public inputs.
  inodeFlags : ObjectId → Nat := fun _ => 0

def ObjectPrivate (world : World) (object : ObjectId) : Prop :=
  (world.attributes object PrivateNames.attributeName).isSome

def HandlePublic (world : World) (fd : UInt64) : Prop :=
  ∀ handle, world.handles fd = some handle → ¬ ObjectPrivate world handle.object

-- §AR-host-boundary.primitives: Laws describe individual operations, never a host procedure.
structure Contract where
  step : World → Request → Option Reply → World → Prop
  interference : World → World → Prop
  interference_handles : ∀ before after,
    interference before after → after.handles = before.handles
  interference_close_exec : ∀ before after,
    interference before after → after.closeOnExec = before.closeOnExec
  interference_directory : ∀ before after,
    interference before after → after.workingDirectory = before.workingDirectory
  step_directory : ∀ before after request observed,
    step before request observed after → after.workingDirectory = before.workingDirectory
  attribute_absent : ∀ before after request reply handle,
    step before request (some reply) after → request.op = .getAttribute →
    request.left = PrivateNames.attributeName →
    before.handles request.first = some handle → nativeError reply = true →
    errorNumber reply = 61 →
    before.attributes handle.object request.left = none
  attribute_frame : ∀ before after request observed,
    step before request observed after → request.op = .getAttribute →
    after.handles = before.handles ∧ after.attributes = before.attributes
  close_exec : ∀ before after request reply,
    step before request (some reply) after → request.op = .closeOnExec →
    reply.1 = 0 → reply.2.isEmpty = true → after.closeOnExec request.first = true
  close_exec_frame : ∀ before after request observed fd,
    step before request observed after → request.op = .closeOnExec →
    fd ≠ request.first → after.closeOnExec fd = before.closeOnExec fd
  rename_no_replace : ∀ before after request observed sourceParent targetParent target,
    step before request observed after → request.op = .renameNew →
    before.handles request.first = some sourceParent →
    before.handles request.second = some targetParent →
    before.entries targetParent.object request.right = some target →
    after.entries targetParent.object request.right = some target
  mkdir_fresh : ∀ before after request reply parent,
    step before request (some reply) after → request.op = .mkdirAt →
    before.handles request.first = some parent → Directories.component request.left = true →
    reply.1 = 0 → reply.2.isEmpty = true →
    ∃ object, before.allocated object = false ∧ after.allocated object = true ∧
      before.entries parent.object request.left = none ∧
      after.entries parent.object request.left = some object
  rename_existing_error : ∀ before after request reply sourceParent targetParent target,
    step before request (some reply) after → request.op = .renameNew →
    before.handles request.first = some sourceParent →
    before.handles request.second = some targetParent →
    before.entries targetParent.object request.right = some target → reply.1 ≠ 0
  random_handles : ∀ before after request observed,
    step before request observed after → request.op = .random → after.handles = before.handles
  write_handles : ∀ before after request observed,
    step before request observed after → request.op = .write → after.handles = before.handles
  allocation_monotone : ∀ before after request observed object,
    step before request observed after → before.allocated object = true → after.allocated object = true
  interference_allocation : ∀ before after object,
    interference before after → before.allocated object = true → after.allocated object = true
  description_allocation_monotone : ∀ before after request observed description,
    step before request observed after → before.descriptionAllocated description = true →
    after.descriptionAllocated description = true
  interference_description_allocation : ∀ before after description,
    interference before after → before.descriptionAllocated description = true →
    after.descriptionAllocated description = true
  exclusive_file : ∀ before after request reply fd,
    step before request (some reply) after → request.op = .openAt →
    request.second = newFileFlags → descriptor reply = some fd →
    ∃ object description, before.allocated object = false ∧ after.allocated object = true ∧
      before.descriptionAllocated description = false ∧ after.descriptionAllocated description = true ∧
      after.descriptions description = some ⟨object, some 0, false⟩ ∧
      after.handles fd = some ⟨object, description, newFileFlags, true⟩

-- §FS-host-boundary.acceptance: Returning executions keep every actual world and kernel reply.
inductive Executes (kernel : Contract) {α : Type} :
    Filesystem.Program α → World → List (Request × Reply) → World → α → Prop where
  | pure (world : World) (value : α) : Executes kernel (.pure value) world [] world value
  | call (request : Request) (next : Reply → Filesystem.Program α) (reply : Reply)
      (before between after : World) (tail : List (Request × Reply)) (value : α)
      (operation : kernel.step before request (some reply) between)
      (rest : Executes kernel (next reply) between tail after value) :
      Executes kernel (.call request next) before ((request, reply) :: tail) after value

theorem executes_returns {kernel : Contract} {α : Type} {program : Filesystem.Program α}
    {before after : World} {events : List (Request × Reply)} {value : α}
    (run : Executes kernel program before events after value) :
    Filesystem.Returns program events value := by
  induction run with
  | pure _ value => exact .pure value
  | call request next reply _ _ _ tail value _ _ ih =>
    exact .call request next reply tail value ih

-- §FS-host-boundary.acceptance: A lost operation may have committed before its reply disappeared.
inductive PrefixExecutes (kernel : Contract) {α : Type} :
    Filesystem.Program α → World → List (Request × Option Reply) → World → Prop where
  | stop (program : Filesystem.Program α) (world : World) :
      PrefixExecutes kernel program world [] world
  | call (request : Request) (next : Reply → Filesystem.Program α) (reply : Reply)
      (before between after : World) (tail : List (Request × Option Reply))
      (operation : kernel.step before request (some reply) between)
      (rest : PrefixExecutes kernel (next reply) between tail after) :
      PrefixExecutes kernel (.call request next) before ((request, some reply) :: tail) after
  | lost (request : Request) (next : Reply → Filesystem.Program α) (before after : World)
      (operation : kernel.step before request none after) :
      PrefixExecutes kernel (.call request next) before [(request, none)] after

theorem prefix_executes_source {kernel : Contract} {α : Type} {program : Filesystem.Program α}
    {before after : World} {events : List (Request × Option Reply)}
    (run : PrefixExecutes kernel program before events after) : Filesystem.Prefix program events := by
  induction run with
  | stop => exact .empty _
  | call request next reply _ _ _ tail _ _ ih => exact .returned request next reply tail ih
  | lost request next _ _ _ => exact .lost request next

-- §FS-host-boundary.caller: Successful startup seals the listed descriptors.
theorem seal_post (kernel : Contract) (fds : List UInt64)
    {before after : World} {events : List (Request × Reply)}
    (run : Executes kernel (Startup.sealDescriptors fds) before events after (.ok ())) :
    ∀ fd, before.closeOnExec fd = true ∨ fd ∈ fds → after.closeOnExec fd = true := by
  induction fds generalizing before events with
  | nil => cases run; intro fd allowed; simpa using allowed
  | cons head tail ih =>
    unfold Startup.sealDescriptors at run
    cases run with
    | call _ _ reply _ between _ rest _ operation next =>
      dsimp only at next
      split at next
      · cases next
      · rename_i passed
        have success : reply.1 = 0 ∧ reply.2.isEmpty = true := by
          simpa using passed
        have sealed := kernel.close_exec _ _ _ _ operation rfl success.1 success.2
        have tailPost := ih next
        intro fd allowed
        apply tailPost fd
        rcases allowed with known | member
        · left
          by_cases equal : fd = head
          · simpa [equal] using sealed
          · have frame := kernel.close_exec_frame _ _ _ _ fd operation rfl equal
            exact frame.trans known
        · rcases List.mem_cons.mp member with equal | member
          · left; simpa [equal] using sealed
          · exact Or.inr member

theorem startup_descriptors (kernel : Contract)
    {before after : World} {events : List (Request × Reply)}
    (run : Executes kernel Startup.descriptors before events after (.ok ())) :
    after.closeOnExec 0 = true ∧ after.closeOnExec 1 = true ∧ after.closeOnExec 3 = true := by
  have sealed := seal_post kernel [0, 1, 3] run
  exact ⟨sealed 0 (by simp), sealed 1 (by simp), sealed 3 (by simp)⟩

-- §FS-host-boundary.ownership: The accepted guard means absence on the actual opened object.
theorem public_handle_source (fd : UInt64) {events : List (Request × Reply)} {value : UInt64}
    (run : Filesystem.Returns (SourcePaths.publicHandle fd) events (.ok value)) :
    value = fd ∧ ∃ reply,
      events = [({
        op := .getAttribute
        first := fd
        second := 1
        left := PrivateNames.attributeName }, reply)] ∧
      nativeError reply = true ∧ errorNumber reply = 61 := by
  unfold SourcePaths.publicHandle at run
  cases run with
  | call _ _ reply tail _ rest =>
    dsimp only at rest
    split at rest
    · rename_i allowed
      have allowed : nativeError reply = true ∧ errorNumber reply = 61 := by simpa using allowed
      obtain ⟨rfl, equal⟩ := Snapshot.returns_pure_eq rest
      cases equal
      exact ⟨rfl, reply, rfl, allowed.1, allowed.2⟩
    · simp only [closeResult] at rest
      cases rest with
      | call _ _ _ _ _ final => cases final

theorem public_handle_is_public {kernel : Contract} (fd : UInt64)
    {before after : World} {events : List (Request × Reply)} {value : UInt64}
    (run : Executes kernel (SourcePaths.publicHandle fd) before events after (.ok value)) :
    value = fd ∧ HandlePublic before fd := by
  obtain ⟨same, reply, shape, failed, absent⟩ := public_handle_source fd (executes_returns run)
  refine ⟨same, ?_⟩
  intro handle reference privateObject
  cases run with
  | call _ _ actual _ _ _ _ _ operation _ =>
    have exactHead := List.cons.inj shape
    have replySame := (Prod.mk.inj exactHead.1).2
    subst actual
    have missing := kernel.attribute_absent _ _ _ _ handle operation rfl rfl reference failed absent
    simp [ObjectPrivate, missing] at privateObject

end LeanCage.Host.Kernel
