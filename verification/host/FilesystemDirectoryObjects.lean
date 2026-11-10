import FilesystemCapabilities
import FilesystemSourceFrames

namespace LeanCage.Host.Kernel
open Filesystem

private theorem reserved_not_dot (name : ByteArray) (reserved : PrivateNames.reservedBytes name = true) :
    name ≠ ".".toUTF8 ∧ name ≠ "..".toUTF8 := by
  have dot : PrivateNames.reservedBytes ".".toUTF8 = false := by decide
  have up : PrivateNames.reservedBytes "..".toUTF8 = false := by decide
  constructor
  · intro same; rw [same, dot] at reserved; cases reserved
  · intro same; rw [same, up] at reserved; cases reserved

-- §FS-host-boundary.ownership: Join the actual open to the registered physical birth, including
-- aliases.
theorem registered_root_opened {kernel : Contract} {initialObjects : ObjectId → Bool}
    (descriptors : DescriptorContract kernel) (mounts : MountContract kernel initialObjects)
    {caps : Capabilities} {before after : World} {root : PrivateRoot} {parent : Handle}
    (fd : UInt64) (reply : Reply) (opened : UInt64)
    (actual : kernel.step before {
      op := .openAt, first := fd, second := directoryFlags, left := root.name } (some reply) after)
    (valid : caps.Valid before) (member : root ∈ caps.roots)
    (parentLive : before.handles fd = some parent) (parentObject : parent.object = root.parent)
    (recognized : descriptor reply = some opened) (component : Directories.component root.name = true)
    (reserved : PrivateNames.reservedBytes root.name = true) (fresh : initialObjects root.object = false) :
    ∃ handle, after.handles opened = some handle ∧ handle.object = root.object ∧ handle.rawOwned = true := by
  have noDots := reserved_not_dot root.name reserved
  have bound : before.entries parent.object root.name = some root.object := by
    rw [parentObject]
    exact (valid.1 root member).2.2.1
  obtain ⟨handle, live, object⟩ := fresh_directory_lookup mounts actual rfl rfl parentLive recognized
    component noDots.1 noDots.2 bound fresh
  exact ⟨handle, live, object, descriptors.allocated_raw _ _ _ _ _ _ actual (.inl rfl) recognized live⟩

-- §FS-host-boundary.ownership: Its fstat observation is on the same live birth object's descriptor.
theorem registered_root_stat {kernel : Contract} (descriptors : DescriptorContract kernel)
    {before after : World} {fd : UInt64} {reply : Reply} {information : Stat} {handle : Handle}
    (step : kernel.step before {op := .stat, first := fd} (some reply) after)
    (live : before.handles fd = some handle) (parsed : parseStat reply = some information) :
    before.information handle.object = some information ∧ after.handles fd = some handle := by
  have actualInformation := descriptors.stat_actual _ _ _ _ _ handle step rfl live parsed
  exact ⟨actualInformation, by
    rw [descriptors.retained _ _ _ _ step (by simp [RetainsDescriptors])]
    exact live⟩

end LeanCage.Host.Kernel
