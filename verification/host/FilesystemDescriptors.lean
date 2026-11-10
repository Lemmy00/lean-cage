import FilesystemOwnership

namespace LeanCage.Host.Kernel
open Filesystem

def AllocatesDescriptor (operation : Op) : Prop :=
  operation = .openAt ∨ operation = .socket ∨ operation = .selfExecutable

def RetainsDescriptors (operation : Op) : Prop :=
  operation ≠ .openAt ∧ operation ≠ .socket ∧ operation ≠ .selfExecutable ∧
    operation ≠ .close ∧ operation ≠ .dirClose

def ValidReferences (world : World) (references : UInt64 → Option Handle) : Prop :=
  ∀ fd handle, references fd = some handle →
    world.allocated handle.object = true ∧ world.descriptionAllocated handle.description = true ∧
    ∃ description, world.descriptions handle.description = some description ∧ description.object = handle.object

def RawReferences (references : UInt64 → Option Handle) : Prop :=
  ∀ fd handle, references fd = some handle → handle.rawOwned = true

-- §AR-host-boundary.primitives: Linux descriptor references and shared OFDs have separate laws.
structure DescriptorContract (kernel : Contract) : Prop where
  allocated_fresh : ∀ before after request reply fd,
    kernel.step before request (some reply) after → AllocatesDescriptor request.op →
    descriptor reply = some fd → before.handles fd = none ∧ ∃ handle, after.handles fd = some handle
  allocated_raw : ∀ before after request reply fd handle,
    kernel.step before request (some reply) after → AllocatesDescriptor request.op →
    descriptor reply = some fd → after.handles fd = some handle → handle.rawOwned = true
  allocate_existing : ∀ before after request observed fd handle,
    kernel.step before request observed after → AllocatesDescriptor request.op →
    before.handles fd = some handle → after.handles fd = some handle
  retained : ∀ before after request observed,
    kernel.step before request observed after → RetainsDescriptors request.op → after.handles = before.handles
  close_other : ∀ before after request observed fd,
    kernel.step before request observed after → request.op = .close → fd ≠ request.first →
    after.handles fd = before.handles fd
  stat_actual : ∀ before after request reply information handle,
    kernel.step before request (some reply) after → request.op = .stat →
    before.handles request.first = some handle → parseStat reply = some information →
    before.information handle.object = some information
  reference_allocated : ∀ before after request observed fd handle,
    kernel.step before request observed after → before.handles fd = some handle → before.allocated handle.object = true
  after_references : ∀ before after request observed,
    kernel.step before request observed after → ValidReferences after after.handles
  after_raw : ∀ before after request observed,
    kernel.step before request observed after → RawReferences after.handles
  description_identity : ∀ before after request observed id description,
    kernel.step before request observed after → before.descriptions id = some description →
    ∃ later, after.descriptions id = some later ∧ later.object = description.object
  reference_descriptions : ∀ before after request observed fd handle,
    kernel.step before request observed after → before.handles fd = some handle →
    ∃ description, before.descriptions handle.description = some description ∧ description.object = handle.object
  interference_descriptions : ∀ before after fd handle,
    kernel.interference before after → before.handles fd = some handle →
    ∃ description, after.descriptions handle.description = some description ∧ description.object = handle.object

-- §FS-host-boundary.ownership: A directory's observed metadata names its actual retained object.
theorem directory_open_handle (kernel : Contract) (descriptors : DescriptorContract kernel)
    (uid : Nat) (parent : UInt64) (name : ByteArray) {before after : World}
    {events : List (Request × Reply)} {opened : Directories.Opened}
    (run : ConcurrentRun kernel (Directories.openAt uid parent name) before events after (.ok opened)) :
    ∃ handle actual openedWorld observing queried openReply statReply,
      History kernel before [] actual ∧
      kernel.step actual {op := .openAt, first := parent, second := directoryFlags, left := name}
        (some openReply) openedWorld ∧ descriptor openReply = some opened.fd ∧
      History kernel openedWorld [] observing ∧
      kernel.step observing {op := .stat, first := opened.fd} (some statReply) queried ∧
      parseStat statReply = some opened.information ∧ History kernel queried [] after ∧
      after.handles opened.fd = some handle ∧ observing.handles opened.fd = some handle ∧
      observing.information handle.object = some opened.information ∧
      Directories.trusted uid opened.information = true := by
  obtain ⟨openedReply, statReply, shape, recognized, parsed, trusted⟩ :=
    Retrieval.directoryOpening_source _ _ _ run.1
  have history := run.2
  rw [shape] at history
  obtain ⟨actual, openedWorld, leading, operation, rest⟩ := history_head history
  obtain ⟨fresh, handle, live⟩ := descriptors.allocated_fresh _ _ _ _ _ operation (.inl rfl) recognized
  obtain ⟨statWorld, queried, between, observed, final⟩ := history_head rest
  have atStat : statWorld.handles opened.fd = some handle := by
    have frames : statWorld.handles = openedWorld.handles :=
      random_history_handles between (by intro event member; cases member)
    rw [frames]
    exact live
  have information := descriptors.stat_actual _ _ _ _ _ handle observed rfl atStat parsed
  have statRetained := descriptors.retained _ _ _ _ observed (by simp [RetainsDescriptors])
  have finalFrames : after.handles = queried.handles :=
    random_history_handles final (by intro event member; cases member)
  refine ⟨handle, actual, openedWorld, statWorld, queried, openedReply, statReply,
    leading, operation, recognized, between, observed, parsed, final, ?_, atStat, information, trusted⟩
  rw [finalFrames, statRetained]
  exact atStat

end LeanCage.Host.Kernel
