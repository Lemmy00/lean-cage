import RunDirectoryProofs.Source

namespace LeanCage.Host.Filesystem

inductive RequestProgram {α : Type} (allowed : Request → Prop) : Filesystem.Program α → Prop where
  | pure (value : α) : RequestProgram allowed (.pure value)
  | call {request : Request} {next : Reply → Filesystem.Program α}
      (permitted : allowed request) (tail : ∀ reply, RequestProgram allowed (next reply)) :
      RequestProgram allowed (.call request next)

theorem request_bind {α β : Type} {allowed : Request → Prop} {program : Filesystem.Program α}
    {next : α → Filesystem.Program β} (first : RequestProgram allowed program)
    (tail : ∀ value, RequestProgram allowed (next value)) : RequestProgram allowed (program.bind next) := by
  induction first with
  | pure => exact tail _
  | call permitted rest ih => exact .call permitted ih

theorem request_weaken {α : Type} {allowed permitted : Request → Prop} {program : Filesystem.Program α}
    (first : RequestProgram allowed program) (includes : ∀ request, allowed request → permitted request) :
    RequestProgram permitted program := by
  induction first with
  | pure => exact .pure _
  | @call request next valid rest ih => exact .call (includes request valid) ih

theorem request_prefix {α : Type} {allowed : Request → Prop} {program : Filesystem.Program α}
    {events : List (Request × Option Reply)} (verified : RequestProgram allowed program) (run : Prefix program events) :
    ∀ event ∈ events, allowed event.1 := by
  induction run with
  | empty => simp
  | lost request next => cases verified with | call permitted => simpa using permitted
  | returned request next reply events run ih =>
    cases verified with
    | call permitted tail =>
      intro event member
      rcases List.mem_cons.mp member with rfl | member
      · exact permitted
      · exact ih (tail reply) event member

end LeanCage.Host.Filesystem

namespace LeanCage.Host.RunDirectory
open Filesystem

-- §FS-host-boundary.ownership: Run setup has no data write, rename or caller-selected content path.
def DirectoryRequest (request : Request) : Prop :=
  match request.op with
  | .openAt => request.second = directoryFlags
  | .mkdirAt => request.second = 448
  | .random => 1 ≤ request.first.toNat ∧ request.first.toNat ≤ 16
  | .setAttribute => request.left = PrivateNames.attributeName ∧ request.right = PrivateNames.attributeValue
  | .unlinkAt => request.second = 512
  | .close | .stat | .euid => True
  | _ => False

def BeforeMarkRequest (request : Request) : Prop :=
  DirectoryRequest request ∧ request.op ≠ .setAttribute ∧ request.op ≠ .unlinkAt

private theorem close_requests {α : Type} (fd : UInt64) (result : Result α) :
    RequestProgram BeforeMarkRequest (closeResult fd result) := by
  apply RequestProgram.call (by exact ⟨True.intro, by simp, by simp⟩)
  intro reply
  cases result with
  | error => exact .pure _
  | ok => dsimp only; split <;> exact .pure _

theorem directoryInspect_requests (uid : Nat) (fd : UInt64) :
    RequestProgram BeforeMarkRequest (Directories.inspect uid fd) := by
  unfold Directories.inspect
  apply RequestProgram.call (by exact ⟨True.intro, by simp, by simp⟩)
  intro reply
  split
  · exact close_requests _ _
  · split
    · exact .pure _
    · exact close_requests _ _

theorem directoryOpen_requests (uid : Nat) (parent : UInt64) (name : ByteArray) :
    RequestProgram BeforeMarkRequest (Directories.openAt uid parent name) := by
  unfold Directories.openAt
  apply RequestProgram.call (by exact ⟨rfl, by simp, by simp⟩)
  intro reply
  split
  · exact .pure _
  · exact directoryInspect_requests _ _

theorem temporaryParent_requests : RequestProgram BeforeMarkRequest Directories.temporaryParent := by
  unfold Directories.temporaryParent
  apply RequestProgram.call (by exact ⟨True.intro, by simp, by simp⟩)
  intro reply
  dsimp only [Filesystem.Program.bind]
  split
  · exact .pure _
  · apply request_bind (directoryOpen_requests _ _ _)
    intro result
    cases result <;> exact .pure _

theorem directoryRandom_requests (fuel count : Nat) (bytes : ByteArray) (bound : count ≤ 16) :
    RequestProgram BeforeMarkRequest (Directories.randomBytes fuel count bytes) := by
  induction fuel generalizing bytes with
  | zero => exact .pure _
  | succ fuel ih =>
    unfold Directories.randomBytes
    split
    · exact .pure _
    · split
      · exact .pure _
      · apply RequestProgram.call
        · refine ⟨?_, by simp, by simp⟩
          change 1 ≤ (count - bytes.size).toUInt64.toNat ∧ (count - bytes.size).toUInt64.toNat ≤ 16
          have different : bytes.size ≠ count := by simpa using ‹¬(bytes.size == count) = true›
          have fits : count - bytes.size < 2 ^ 64 := by omega
          rw [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt fits]
          constructor <;> omega
        · intro reply
          split
          · exact .pure _
          · split
            · exact .pure _
            · exact ih _

theorem directoryChild_requests (uid : Nat) (parent : UInt64) (prefixName : String) :
    RequestProgram BeforeMarkRequest (Directories.newChild uid parent prefixName) := by
  unfold Directories.newChild
  apply request_bind (directoryRandom_requests _ _ _ (by decide))
  intro random
  cases random with
  | error => exact .pure _
  | ok bytes =>
    dsimp only
    split
    · exact .pure _
    · apply RequestProgram.call (by exact ⟨rfl, by simp, by simp⟩)
      intro made
      dsimp only [Filesystem.Program.bind]
      split
      · exact .pure _
      · apply request_bind (directoryOpen_requests _ _ _)
        intro opened
        cases opened with
        | error => exact .pure _
        | ok directory =>
          dsimp only
          split
          · exact close_requests _ _
          · exact .pure _

private theorem run_close {α : Type} (fd : UInt64) (result : Result α) :
    RequestProgram DirectoryRequest (closeResult fd result) :=
  request_weaken (close_requests _ _) (fun _ proof => proof.1)

theorem create_requests : RequestProgram DirectoryRequest create := by
  unfold create
  apply request_bind (request_weaken temporaryParent_requests (fun _ proof => proof.1))
  intro area
  cases area with
  | error => exact .pure _
  | ok area =>
    rcases area with ⟨container, areaPath, uid⟩
    apply request_bind (request_weaken (directoryChild_requests _ _ _) (fun _ proof => proof.1))
    intro child
    cases child with
    | error => exact run_close _ _
    | ok child =>
      apply RequestProgram.call (by exact ⟨rfl, rfl⟩)
      intro marked
      dsimp only [Filesystem.Program.bind]
      split
      · apply RequestProgram.call (by trivial)
        intro reply
        dsimp only [Filesystem.Program.bind]
        apply RequestProgram.call (by rfl)
        intro reply
        dsimp only [Filesystem.Program.bind]
        exact run_close _ _
      · split
        · apply RequestProgram.call (by trivial)
          intro reply
          dsimp only [Filesystem.Program.bind]
          exact run_close _ _
        · split
          · apply RequestProgram.call (by trivial)
            intro reply
            dsimp only [Filesystem.Program.bind]
            exact run_close _ _
          · exact .pure _

-- §FS-host-boundary.ownership: Interrupted setup retains the same finite operation roles.
theorem create_request_prefix {events : List (Request × Option Reply)} (run : Prefix create events) :
    ∀ event ∈ events, DirectoryRequest event.1 := request_prefix create_requests run

end LeanCage.Host.RunDirectory

namespace LeanCage.Host.Filesystem

theorem request_forIn {α β : Type} (items : List α) (initial : β) (allowed : Request → Prop)
    (body : α → β → Filesystem.Program (ForInStep β))
    (permitted : ∀ item ∈ items, ∀ state, RequestProgram allowed (body item state)) :
    RequestProgram allowed (forIn items initial body) := by
  induction items generalizing initial with
  | nil => exact .pure _
  | cons item rest ih =>
    rw [List.forIn_cons]
    apply request_bind (permitted item (by simp) initial)
    intro step
    cases step with
    | done => exact .pure _
    | yield state => exact ih state (fun item member => permitted item (by simp [member]))

end LeanCage.Host.Filesystem
