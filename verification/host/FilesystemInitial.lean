import FilesystemRuntime

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.caller: These are the same native socketpair objects after actual engine exec.
structure EngineChannels (objects : Nat → Option Nat) (closeExec : Nat → Bool)
    (dataEndpoint cancellationEndpoint : Nat) : Prop where
  dataInput : objects 0 = some dataEndpoint
  dataOutput : objects 1 = some dataEndpoint
  cancellationInput : objects 3 = some cancellationEndpoint
  separate : dataEndpoint ≠ cancellationEndpoint
  otherClosed : ∀ fd, fd ≠ 0 → fd ≠ 1 → fd ≠ 3 → objects fd = none
  dataInputInherited : closeExec 0 = false
  dataOutputInherited : closeExec 1 = false
  cancellationInherited : closeExec 3 = false

def rawObjects (references : UInt64 → Option Handle) (fd : Nat) : Option Nat :=
  if fd < 2 ^ 64 then (references fd.toUInt64).map (·.object) else none

def rawCloseExec (closeExec : UInt64 → Bool) (fd : Nat) : Bool :=
  if fd < 2 ^ 64 then closeExec fd.toUInt64 else false

-- §AR-host-boundary.primitives: IPC kinds are actual lifetime objects, including later launches.
structure InitialEngineBinding (ipc : ObjectId → Prop) (references : UInt64 → Option Handle)
    (closeExec : UInt64 → Bool) where
  dataEndpoint : ObjectId
  cancellationEndpoint : ObjectId
  channels : EngineChannels (rawObjects references) (rawCloseExec closeExec)
    dataEndpoint cancellationEndpoint
  dataIpc : ipc dataEndpoint
  cancellationIpc : ipc cancellationEndpoint

theorem rawObjects_live (references : UInt64 → Option Handle) (fd : UInt64) (handle : Handle)
    (live : references fd = some handle) : rawObjects references fd.toNat = some handle.object := by
  simp only [rawObjects, UInt64.toNat_lt, ↓reduceIte, UInt64.ofNat_toNat, live, Option.map_some]

-- §FS-host-boundary.ownership: No inherited raw capability is an arbitrary stored data object.
theorem initial_reference_ipc {ipc : ObjectId → Prop} {references : UInt64 → Option Handle}
    {closeExec : UInt64 → Bool} (binding : InitialEngineBinding ipc references closeExec)
    {fd : UInt64} {handle : Handle} (live : references fd = some handle) :
    ipc handle.object ∧ (fd.toNat = 0 ∨ fd.toNat = 1 ∨ fd.toNat = 3) := by
  have observed := rawObjects_live references fd handle live
  by_cases input : fd.toNat = 0
  · have same := Option.some.inj (observed.symm.trans (input ▸ binding.channels.dataInput))
    exact ⟨same.symm ▸ binding.dataIpc, .inl input⟩
  · by_cases output : fd.toNat = 1
    · have same := Option.some.inj (observed.symm.trans (output ▸ binding.channels.dataOutput))
      exact ⟨same.symm ▸ binding.dataIpc, .inr (.inl output)⟩
    · by_cases cancellation : fd.toNat = 3
      · have same := Option.some.inj (observed.symm.trans (cancellation ▸ binding.channels.cancellationInput))
        exact ⟨same.symm ▸ binding.cancellationIpc, .inr (.inr cancellation)⟩
      · have absent := binding.channels.otherClosed fd.toNat input output cancellation
        rw [observed] at absent
        cases absent

theorem initial_reference_outside_data {ipc : ObjectId → Prop} {dataObjects : ObjectId → Prop}
    {references : UInt64 → Option Handle} {closeExec : UInt64 → Bool}
    (binding : InitialEngineBinding ipc references closeExec)
    (separate : ∀ object, ipc object → ¬ dataObjects object)
    {fd : UInt64} {handle : Handle} (live : references fd = some handle) : ¬ dataObjects handle.object :=
  separate handle.object (initial_reference_ipc binding live).1

end LeanCage.Host.Kernel
