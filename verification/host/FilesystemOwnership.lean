import FilesystemContracts
import PublicationProofs.Creation
import PublicationProofs.Commit

namespace LeanCage.Host.Kernel
open Filesystem

-- §AR-host-boundary.primitives: Keep each primitive's actual before/after objects in the trace.
inductive History (kernel : Contract) :
    World → List (Request × Reply) → World → Prop where
  | nil (world : World) : History kernel world [] world
  | cons {before between after : World} {request : Request} {reply : Reply}
      {events : List (Request × Reply)}
      (operation : kernel.step before request (some reply) between)
      (tail : History kernel between events after) :
      History kernel before ((request, reply) :: events) after
  | environment {before between after : World} {events : List (Request × Reply)}
      (interference : kernel.interference before between)
      (tail : History kernel between events after) : History kernel before events after

-- §FS-host-boundary.acceptance: Environment steps can intervene between every application call.
def ConcurrentRun (kernel : Contract) {α : Type} (program : Filesystem.Program α)
    (before : World) (events : List (Request × Reply)) (after : World) (value : α) : Prop :=
  Returns program events value ∧ History kernel before events after

theorem executes_history {kernel : Contract} {α : Type} {program : Filesystem.Program α}
    {before after : World} {events : List (Request × Reply)} {value : α}
    (run : Executes kernel program before events after value) : History kernel before events after := by
  induction run with
  | pure world => exact .nil world
  | call _ _ _ _ _ _ _ _ operation _ ih => exact .cons operation ih

theorem history_append {kernel : Contract} {first middle last : World}
    {before after : List (Request × Reply)}
    (initial : History kernel first before middle) (final : History kernel middle after last) :
    History kernel first (before ++ after) last := by
  induction initial with
  | nil => exact final
  | cons operation tail ih => exact .cons operation (ih final)
  | environment interference tail ih => exact .environment interference (ih final)

theorem history_head {kernel : Contract} {before after : World}
    {request : Request} {reply : Reply} {events : List (Request × Reply)}
    (history : History kernel before ((request, reply) :: events) after) :
    ∃ actual between, History kernel before [] actual ∧
      kernel.step actual request (some reply) between ∧ History kernel between events after := by
  generalize shape : (request, reply) :: events = all at history
  induction history with
  | nil => cases shape
  | cons operation tail ih =>
    cases shape
    exact ⟨_, _, .nil _, operation, tail⟩
  | environment interference tail ih =>
    obtain ⟨actual, between, leading, operation, rest⟩ := ih shape
    exact ⟨actual, between, .environment interference leading, operation, rest⟩

theorem history_split {kernel : Contract} {before after : World}
    (first last : List (Request × Reply)) (history : History kernel before (first ++ last) after) :
    ∃ between, History kernel before first between ∧ History kernel between last after := by
  induction first generalizing before with
  | nil => exact ⟨before, .nil _, history⟩
  | cons event rest ih =>
    obtain ⟨actual, between, leading, operation, tail⟩ := history_head history
    obtain ⟨middle, firstHistory, lastHistory⟩ := ih tail
    exact ⟨middle, history_append leading (.cons operation firstHistory), lastHistory⟩

theorem random_history_handles {kernel : Contract} {before after : World}
    {events : List (Request × Reply)} (history : History kernel before events after)
    (random : ∀ event ∈ events, event.1.op = .random) : after.handles = before.handles := by
  induction history with
  | nil => rfl
  | @cons before between after request reply events operation tail ih =>
    have head := kernel.random_handles _ _ _ _ operation (random (request, reply) (by simp))
    have rest := ih (fun event member => random event (by simp [member]))
    exact rest.trans head
  | environment interference tail ih =>
    exact (ih random).trans (kernel.interference_handles _ _ interference)

theorem randomBytes_calls (fuel count : Nat) (bytes : ByteArray)
    {events : List (Request × Reply)} {result : Filesystem.Result ByteArray}
    (run : Returns (Directories.randomBytes fuel count bytes) events result) :
    ∀ event ∈ events, event.1.op = .random := by
  induction fuel generalizing bytes events with
  | zero => cases run; simp
  | succ fuel ih =>
    unfold Directories.randomBytes at run
    split at run
    · cases run; simp
    · split at run
      · cases run; simp
      · obtain ⟨reply, tail, rfl, continued⟩ := Snapshot.returns_call_split run
        intro event member
        rcases List.mem_cons.mp member with rfl | member
        · rfl
        · split at continued
          · cases continued; simp at member
          · split at continued
            · cases continued; simp at member
            · exact ih _ continued event member

-- §FS-host-boundary.ownership: A successful source mkdir created a genuinely new kernel object.
theorem new_child_has_fresh_birth (kernel : Contract) (uid : Nat) (parent : UInt64)
    (prefixName : String) {before after : World} {events : List (Request × Reply)}
    {child : Directories.NewDirectory} {parentHandle : Handle}
    (run : ConcurrentRun kernel (Directories.newChild uid parent prefixName)
      before events after (.ok child))
    (parentLive : before.handles parent = some parentHandle) :
    ∃ creating created object randomEvents opening made,
      events = randomEvents ++ ({
        op := .mkdirAt, first := parent, second := 448,
        left := child.name}, made) :: opening ∧
      History kernel before randomEvents creating ∧
      kernel.step creating {
        op := .mkdirAt, first := parent, second := 448,
        left := child.name} (some made) created ∧
      creating.handles parent = some parentHandle ∧
      creating.allocated object = false ∧ created.allocated object = true ∧
      creating.entries parentHandle.object child.name = none ∧
      created.entries parentHandle.object child.name = some object := by
  obtain ⟨random, randomEvents, made, opening, shape, randomRun, _, _, component,
    acknowledged, empty, _⟩ := Publication.newChild_source uid parent prefixName run.1
  have history := run.2
  have shape : events = randomEvents ++ ({
      op := .mkdirAt, first := parent, second := 448, left := child.name}, made) :: opening := by
    simpa only [List.append_assoc, List.singleton_append] using shape
  rw [shape] at history
  obtain ⟨afterRandom, randomHistory, tail⟩ := history_split randomEvents _ history
  obtain ⟨creating, created, leading, operation, rest⟩ := history_head tail
  have extended : History kernel before randomEvents creating := by
    simpa only [List.append_nil] using history_append randomHistory leading
  have live : creating.handles parent = some parentHandle := by
    rw [random_history_handles extended (randomBytes_calls _ _ _ randomRun)]
    exact parentLive
  obtain ⟨object, fresh, allocated, absent, added⟩ := kernel.mkdir_fresh _ _ _ _ _ operation
    rfl live component acknowledged (by rw [empty]; rfl)
  exact ⟨creating, created, object, randomEvents, opening, made,
    shape, extended, operation, live, fresh, allocated, absent, added⟩

end LeanCage.Host.Kernel
