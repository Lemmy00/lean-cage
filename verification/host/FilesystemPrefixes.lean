import FilesystemWrites

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.acceptance: A lost last operation keeps its actual possible kernel effect.
inductive PhysicalPrefix (kernel : Contract) {α : Type} :
    Filesystem.Program α → World → List (Request × Option Reply) → World → Prop where
  | stop (program : Filesystem.Program α) (world : World) : PhysicalPrefix kernel program world [] world
  | environment {program : Filesystem.Program α} {before between after : World}
      {events : List (Request × Option Reply)} (interference : kernel.interference before between)
      (tail : PhysicalPrefix kernel program between events after) :
      PhysicalPrefix kernel program before events after
  | returned {request : Request} {next : Reply → Filesystem.Program α} {reply : Reply}
      {before between after : World} {events : List (Request × Option Reply)}
      (operation : kernel.step before request (some reply) between)
      (tail : PhysicalPrefix kernel (next reply) between events after) :
      PhysicalPrefix kernel (.call request next) before ((request, some reply) :: events) after
  | lost {request : Request} {next : Reply → Filesystem.Program α} {before after : World}
      (operation : kernel.step before request none after) :
      PhysicalPrefix kernel (.call request next) before [(request, none)] after

theorem physical_prefix_source {kernel : Contract} {α : Type} {program : Filesystem.Program α}
    {before after : World} {events : List (Request × Option Reply)}
    (run : PhysicalPrefix kernel program before events after) : Filesystem.Prefix program events := by
  induction run with
  | stop => exact .empty _
  | environment interference tail ih => exact ih
  | returned operation tail ih => exact .returned _ _ _ _ ih
  | lost operation => exact .lost _ _

def acknowledgedPrefix (events : List (Request × Reply)) : List (Request × Option Reply) :=
  events.map (fun event => (event.1, some event.2))

-- §FS-host-boundary.acceptance: A continuation runs only after the actual first phase returns.
theorem physical_bind_split {kernel : Contract} {α β : Type}
    (first : Filesystem.Program α) (next : α → Filesystem.Program β)
    {before after : World} {events : List (Request × Option Reply)}
    (run : PhysicalPrefix kernel (first.bind next) before events after) :
    PhysicalPrefix kernel first before events after ∨
      ∃ middle initial value final,
        ConcurrentRun kernel first before initial middle value ∧
        PhysicalPrefix kernel (next value) middle final after ∧
        events = acknowledgedPrefix initial ++ final := by
  generalize shape : first.bind next = program at run
  induction run generalizing first with
  | stop program world =>
    exact .inl (.stop first world)
  | environment interference tail ih =>
    rcases ih first shape with early | ⟨middle, initial, value, final, ran, rest, trace⟩
    · exact .inl (.environment interference early)
    · exact .inr ⟨middle, initial, value, final, ⟨ran.1, .environment interference ran.2⟩, rest, trace⟩
  | @returned request actualNext reply before between after events operation tail ih =>
    cases first with
    | pure value =>
      change next value = Filesystem.Program.call request actualNext at shape
      exact .inr ⟨before, [], value, (request, some reply) :: events, ⟨.pure value, .nil _⟩,
        by rw [shape]; exact PhysicalPrefix.returned operation tail, rfl⟩
    | call original continuation =>
      change Filesystem.Program.call original (fun reply => (continuation reply).bind next) =
        Filesystem.Program.call request actualNext at shape
      injection shape with sameRequest sameNext
      subst original
      rcases ih (continuation reply) (congrFun sameNext reply) with early |
          ⟨middle, initial, value, final, ran, rest, trace⟩
      · exact .inl (.returned operation early)
      · refine .inr ⟨middle, (request, reply) :: initial, value, final,
          ⟨.call request continuation reply initial value ran.1, .cons operation ran.2⟩, rest, ?_⟩
        simpa only [acknowledgedPrefix, List.map_cons, List.cons_append] using
          congrArg (fun events => (request, some reply) :: events) trace
  | @lost request actualNext before after operation =>
    cases first with
    | pure value =>
      change next value = Filesystem.Program.call request actualNext at shape
      exact .inr ⟨before, [], value, [(request, none)], ⟨.pure value, .nil _⟩,
        by rw [shape]; exact PhysicalPrefix.lost (next := actualNext) operation, rfl⟩
    | call original continuation =>
      change Filesystem.Program.call original (fun reply => (continuation reply).bind next) =
        Filesystem.Program.call request actualNext at shape
      injection shape with sameRequest sameNext
      subst original
      exact .inl (.lost operation)

inductive PrefixTargets (kernel : Contract) (allowed : ObjectId → Prop) :
    World → List (Request × Option Reply) → World → Prop where
  | nil (world : World) : PrefixTargets kernel allowed world [] world
  | environment {before between after : World} {events : List (Request × Option Reply)}
      (interference : kernel.interference before between)
      (tail : PrefixTargets kernel allowed between events after) :
      PrefixTargets kernel allowed before events after
  | returned {before between after : World} {request : Request} {reply : Reply}
      {events : List (Request × Option Reply)} (operation : kernel.step before request (some reply) between)
      (target : request.op = .write → ∃ handle,
        before.handles request.first = some handle ∧ allowed handle.object)
      (tail : PrefixTargets kernel allowed between events after) :
      PrefixTargets kernel allowed before ((request, some reply) :: events) after
  | lost {before after : World} {request : Request} (operation : kernel.step before request none after)
      (target : request.op = .write → ∃ handle,
        before.handles request.first = some handle ∧ allowed handle.object) :
      PrefixTargets kernel allowed before [(request, none)] after

theorem writes_prefix_targets {kernel : Contract} {allowed : ObjectId → Prop}
    {before after : World} {events : List (Request × Reply)}
    (run : WritesWithin kernel allowed before events after) :
    PrefixTargets kernel allowed before (acknowledgedPrefix events) after := by
  induction run with
  | nil => exact .nil _
  | cons operation target tail ih => exact .returned operation target ih
  | environment interference tail ih => exact .environment interference ih

theorem writes_then_prefix {kernel : Contract} {allowed : ObjectId → Prop}
    {first middle last : World} {before : List (Request × Reply)}
    {after : List (Request × Option Reply)}
    (initial : WritesWithin kernel allowed first before middle)
    (final : PrefixTargets kernel allowed middle after last) :
    PrefixTargets kernel allowed first (acknowledgedPrefix before ++ after) last := by
  induction initial with
  | nil => exact final
  | cons operation target tail ih => exact .returned operation target (ih final)
  | environment interference tail ih => exact .environment interference (ih final)

theorem prefix_targets_mono {kernel : Contract} {firstAllowed lastAllowed : ObjectId → Prop}
    {before after : World} {events : List (Request × Option Reply)}
    (run : PrefixTargets kernel firstAllowed before events after)
    (inclusion : ∀ object, firstAllowed object → lastAllowed object) :
    PrefixTargets kernel lastAllowed before events after := by
  induction run with
  | nil => exact .nil _
  | returned operation target tail ih =>
    apply PrefixTargets.returned operation
    · intro write
      obtain ⟨handle, actual, allowed⟩ := target write
      exact ⟨handle, actual, inclusion _ allowed⟩
    · exact ih
  | environment interference tail ih => exact .environment interference ih
  | lost operation target =>
    apply PrefixTargets.lost operation
    intro write
    obtain ⟨handle, actual, allowed⟩ := target write
    exact ⟨handle, actual, inclusion _ allowed⟩

theorem physical_nonwrite {kernel : Contract} {α : Type} {program : Filesystem.Program α}
    {before after : World} {events : List (Request × Option Reply)} {allowed : ObjectId → Prop}
    (run : PhysicalPrefix kernel program before events after)
    (none : ∀ event ∈ events, event.1.op ≠ .write) :
    PrefixTargets kernel allowed before events after := by
  induction run with
  | stop => exact .nil _
  | environment interference tail ih => exact .environment interference (ih none)
  | @returned request next reply before between after events operation tail ih =>
    exact .returned operation (fun write => False.elim (none (request, some reply) (by simp) write))
      (ih (fun event member => none event (by simp [member])))
  | @lost request next before after operation =>
    exact .lost operation (fun write => False.elim (none (request, Option.none) (by simp) write))

inductive CallCut (kernel : Contract) {α : Type} (request : Request)
    (next : Reply → Filesystem.Program α) (before : World) :
    List (Request × Option Reply) → World → Prop where
  | waiting {after : World} (leading : History kernel before [] after) : CallCut kernel request next before [] after
  | lost {actual after : World} (leading : History kernel before [] actual)
      (operation : kernel.step actual request none after) :
      CallCut kernel request next before [(request, none)] after
  | returned {actual between after : World} {reply : Reply} {events : List (Request × Option Reply)}
      (leading : History kernel before [] actual)
      (operation : kernel.step actual request (some reply) between)
      (tail : PhysicalPrefix kernel (next reply) between events after) :
      CallCut kernel request next before ((request, some reply) :: events) after

-- §FS-host-boundary.acceptance: This source cut retains interference before an actual call.
theorem physical_call_cut {kernel : Contract} {α : Type} {request : Request}
    {next : Reply → Filesystem.Program α} {before after : World}
    {events : List (Request × Option Reply)}
    (run : PhysicalPrefix kernel (.call request next) before events after) :
    CallCut kernel request next before events after := by
  generalize shape : Filesystem.Program.call request next = program at run
  induction run with
  | stop program world => exact .waiting (.nil _)
  | environment interference tail ih =>
    cases ih shape with
    | waiting leading => exact .waiting (.environment interference leading)
    | lost leading operation => exact .lost (.environment interference leading) operation
    | returned leading operation tail => exact .returned (.environment interference leading) operation tail
  | returned operation tail ih =>
    cases shape
    exact .returned (.nil _) operation tail
  | lost operation =>
    cases shape
    exact .lost (.nil _) operation

inductive OnlyWrites (fd : UInt64) {α : Type} : Filesystem.Program α → Prop where
  | pure (value : α) : OnlyWrites fd (.pure value)
  | call {request : Request} {next : Reply → Filesystem.Program α}
      (op : request.op = .write) (descriptor : request.first = fd)
      (tail : ∀ reply, OnlyWrites fd (next reply)) : OnlyWrites fd (.call request next)

theorem writeLoop_only (fuel : Nat) (fd : UInt64) (bytes : ByteArray) (offset : Nat) :
    OnlyWrites fd (writeLoop fuel fd bytes offset) := by
  induction fuel generalizing offset with
  | zero => exact .pure _
  | succ fuel ih =>
    unfold writeLoop
    split
    · exact .pure _
    · dsimp only
      apply OnlyWrites.call (request := {
        op := .write, first := fd,
        left := bytes.extract offset (min bytes.size (offset + chunkMax)) }) rfl rfl
      intro reply
      split
      · exact .pure _
      · split
        · exact .pure _
        · exact ih _

theorem onlyWrites_prefix {kernel : Contract} {α : Type} {program : Filesystem.Program α}
    {before after : World} {events : List (Request × Option Reply)}
    (run : PhysicalPrefix kernel program before events after) (fd : UInt64) (handle : Handle)
    (live : before.handles fd = some handle) (only : OnlyWrites fd program) :
    PrefixTargets kernel (· = handle.object) before events after := by
  induction run with
  | stop => exact .nil _
  | environment interference tail ih =>
    apply PrefixTargets.environment interference
    apply ih
    · rw [kernel.interference_handles _ _ interference]
      exact live
    · exact only
  | @returned request next reply before between after events operation tail ih =>
    cases only with
    | call op descriptor rest =>
      apply PrefixTargets.returned operation
      · intro _
        exact ⟨handle, by rw [descriptor]; exact live, rfl⟩
      · apply ih
        · rw [kernel.write_handles _ _ _ _ operation op]
          exact live
        · exact rest reply
  | lost operation =>
    cases only with
    | call op descriptor rest =>
      apply PrefixTargets.lost operation
      intro _
      exact ⟨handle, by rw [descriptor]; exact live, rfl⟩

-- §FS-host-boundary.ownership: Failure, loss and peer interference cannot redirect this writer.
theorem writeLoop_prefix_targets (kernel : Contract) (fuel : Nat) (fd : UInt64)
    (bytes : ByteArray) (offset : Nat) {before after : World}
    {events : List (Request × Option Reply)} {handle : Handle}
    (run : PhysicalPrefix kernel (writeLoop fuel fd bytes offset) before events after)
    (live : before.handles fd = some handle) :
    PrefixTargets kernel (· = handle.object) before events after :=
  onlyWrites_prefix run fd handle live (writeLoop_only fuel fd bytes offset)

theorem closeResult_prefix_targets (kernel : Contract) {α : Type} (fd : UInt64)
    (result : Filesystem.Result α) {before after : World}
    {events : List (Request × Option Reply)} {allowed : ObjectId → Prop}
    (run : PhysicalPrefix kernel (closeResult fd result) before events after) :
    PrefixTargets kernel allowed before events after := by
  apply physical_nonwrite run
  intro event member write
  have input := Snapshot.input_prefix (Snapshot.closeResult_input fd result)
    (physical_prefix_source run) event member
  simp [Snapshot.InputRequest, write] at input

theorem writeAndClose_prefix_targets (kernel : Contract) (fuel : Nat) (fd : UInt64)
    (bytes : ByteArray) (offset : Nat) {before after : World}
    {events : List (Request × Option Reply)} {handle : Handle}
    (run : PhysicalPrefix kernel ((writeLoop fuel fd bytes offset).bind (closeResult fd))
      before events after) (live : before.handles fd = some handle) :
    PrefixTargets kernel (· = handle.object) before events after := by
  rcases physical_bind_split _ _ run with early | ⟨middle, initial, result, final, written, closed, trace⟩
  · exact writeLoop_prefix_targets kernel fuel fd bytes offset early live
  · rw [trace]
    exact writes_then_prefix (writeLoop_targets kernel fuel fd bytes offset written live)
      (closeResult_prefix_targets kernel fd result closed)

-- §FS-host-boundary.ownership: The exclusive writer stays fresh through every failure/loss cut.
theorem writeNew_prefix_only_fresh (kernel : Contract) (parent : UInt64) (name bytes : ByteArray)
    (mode : UInt64) {before after : World} {events : List (Request × Option Reply)}
    (run : PhysicalPrefix kernel (writeNew parent name bytes mode) before events after) :
    PrefixTargets kernel (fun object => before.allocated object = false) before events after := by
  unfold writeNew at run
  split at run
  · apply physical_nonwrite run
    have empty := Snapshot.prefix_pure_empty (physical_prefix_source run)
    rw [empty]
    simp
  · cases physical_call_cut run with
    | waiting leading =>
      exact writes_prefix_targets (nonwrite_history leading (by simp))
    | lost leading operation =>
      exact writes_then_prefix (nonwrite_history leading (by simp))
        (.lost operation (by intro impossible; cases impossible))
    | @returned actual between final reply events leading operation tail =>
      cases recognized : descriptor reply with
      | none =>
        simp only [recognized] at tail
        have rest : PrefixTargets kernel (fun object => before.allocated object = false)
            between events after := by
          apply physical_nonwrite tail
          have empty := Snapshot.prefix_pure_empty (physical_prefix_source tail)
          rw [empty]
          simp
        exact writes_then_prefix (nonwrite_history leading (by simp))
          (.returned operation (by intro impossible; cases impossible) rest)
      | some fd =>
        simp only [recognized] at tail
        obtain ⟨object, description, fresh, _, _, _, _, live⟩ := kernel.exclusive_file _ _ _ _ _ operation rfl rfl recognized
        have original : before.allocated object = false := by
          cases allocation : before.allocated object with
          | false => rfl
          | true =>
            have allocated := history_allocated leading object allocation
            rw [fresh] at allocated
            contradiction
        have targets := writeAndClose_prefix_targets kernel (bytes.size + 1) fd bytes 0 tail live
        have rest : PrefixTargets kernel (fun object => before.allocated object = false)
            between events after := prefix_targets_mono targets (by
          intro selected same
          have same : selected = object := same
          rw [same]
          exact original)
        exact writes_then_prefix (nonwrite_history leading (by simp))
          (.returned operation (by intro impossible; cases impossible) rest)

end LeanCage.Host.Kernel
