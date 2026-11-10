import FilesystemActors
import FilesystemSourceFrames

namespace LeanCage.Host.Kernel
open Filesystem

def RetainedObject (world : World) (object : ObjectId) : Prop :=
  (∃ fd handle, world.handles fd = some handle ∧ handle.object = object) ∨
    ∃ parent component, world.entries parent component = some object

-- §FS-host-boundary.publication: The exposed API cannot replace an existing tracked user attribute.
theorem syscall_keeps_marker {kernel : Contract} (laws : NamespaceContract kernel)
    {before after : World} {request : Request} {observed : Option Reply}
    {object : ObjectId} {name value : ByteArray} (step : kernel.step before request observed after)
    (source : request.op = .setAttribute → TrackedAttribute request.left)
    (binding : request.op = .setAttribute → ∃ handle, before.handles request.first = some handle)
    (tracked : TrackedAttribute name) (allocated : before.allocated object = true)
    (retained : RetainedObject after object) (marked : before.attributes object name = some value) :
    after.attributes object name = some value := by
  by_cases attributeCall : request.op = .setAttribute
  · obtain ⟨handle, reference⟩ := binding attributeCall
    by_cases same : object = handle.object ∧ name = request.left
    · rcases same with ⟨rfl, rfl⟩
      exact laws.existing_attribute _ _ _ _ _ _ step attributeCall (source attributeCall) reference marked
    · have different : object ≠ handle.object ∨ name ≠ request.left := by
        by_cases objectSame : object = handle.object
        · right; intro nameSame; exact same ⟨objectSame, nameSame⟩
        · exact .inl objectSame
      rw [laws.attribute_other _ _ _ _ _ _ _ step attributeCall (source attributeCall) tracked reference different]
      exact marked
  · rw [laws.attribute_passive _ _ _ _ _ _ step attributeCall tracked allocated retained]
    exact marked

-- §FS-host-boundary.ownership: Test the actual tick's retained object, not its finite inode
-- numbers.
theorem accepted_public_tick_excludes_marker {kernel : Contract} {runtime : ActorRuntime kernel}
    (tick : ActorTick runtime) (actor : ActorId) (fd : UInt64) (reply : Reply)
    (action : tick.action = .returned actor (.filesystem {
      op := .getAttribute, first := fd, second := 1, left := PrivateNames.attributeName }) reply)
    (accepted : nativeError reply = true ∧ errorNumber reply = 61)
    {object : ObjectId} {value : ByteArray} (marked : tick.before.shared.attributes object PrivateNames.attributeName = some value)
    (engine : EngineState) (present : tick.before.actors actor = some engine)
    (handle : Handle) (live : engine.references fd = some handle) : handle.object ≠ object := by
  intro same
  rcases tick with ⟨kind, before, after, operation⟩
  dsimp only at action marked present ⊢
  subst kind
  cases operation with
  | @returned β population actualActor current effect next actualReply world currentPresent alive head actual =>
    have sameEngine := Option.some.inj (present.symm.trans currentPresent)
    subst engine
    have absent := kernel.attribute_absent _ _ _ _ handle actual rfl rfl live accepted.1 accepted.2
    change before.shared.attributes handle.object PrivateNames.attributeName = none at absent
    rw [same, marked] at absent
    cases absent

-- §FS-host-boundary.snapshot: Copying never changes the reference that passed the actual guard.
theorem guarded_copy_excludes_object {kernel : Contract} (laws : DescriptorContract kernel)
    (fd : UInt64) (handle : Handle) (limit : Nat) (excluded : ObjectId)
    {before after : World} {events : List (Request × Option Reply)}
    (run : PhysicalPrefix kernel (copyOpened fd limit) before events after)
    (live : before.handles fd = some handle) (different : handle.object ≠ excluded) :
    after.handles fd = some handle ∧ handle.object ≠ excluded :=
  ⟨borrow_prefix (copyOpened_borrow laws fd handle fd limit) run live, different⟩

end LeanCage.Host.Kernel
