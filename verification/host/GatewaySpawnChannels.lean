import FilesystemInitial

namespace LeanCage.Host.NativeSpawn
open Kernel

-- §AR-host-boundary.interfaces: The native child view carries actual object/OFD/FD-flag identities.
structure Descriptor where
  object : Nat
  description : Nat
  closeExec : Bool
  deriving DecidableEq

def channelSlot (fd : Nat) : Bool := fd == 0 || fd == 1 || fd == 3

-- §FS-host-boundary.ownership: This is only the application-owned raw projection.
-- SDK stderr and internal handles keep separate actual leases.
def rawReferences (table : Nat → Option Descriptor) (fd : UInt64) : Option Handle :=
  if channelSlot fd.toNat then
    (table fd.toNat).map fun entry => ⟨entry.object, entry.description, 0, true⟩
  else none

-- §AR-host-boundary.primitives: The zero request word records no engine-side open operation.
-- It does not assert a live F_GETFL value; that status is a separate OFD observation.
def rawFlags (table : Nat → Option Descriptor) (fd : UInt64) : Bool :=
  if channelSlot fd.toNat then (table fd.toNat).map (·.closeExec) |>.getD false else false

-- §AR-host-boundary.interfaces: This is the strict bridge's exact conjunction of
-- descriptor observations. IPC kind is supplied separately by the same socket births.
def ChannelEvidence (table : Nat → Option Descriptor) (data control : Descriptor) : Prop :=
  table 0 = some data ∧ table 1 = some data ∧ table 3 = some control ∧
  data.closeExec = false ∧ control.closeExec = false ∧ data.object ≠ control.object

-- §FS-host-boundary.ownership: A raw-projected handle is an actual source-owned reference.
theorem raw_references_owned (table : Nat → Option Descriptor) (fd : UInt64) (handle : Handle)
    (live : rawReferences table fd = some handle) : handle.rawOwned = true := by
  unfold rawReferences at live
  split at live
  · cases found : table fd.toNat with
    | none => simp [found] at live
    | some entry =>
      simp only [found, Option.map_some] at live
      cases live
      rfl
  · cases live

-- §AR-host-boundary.interfaces: Actual source actions must produce these same three descriptor
-- observations; this adapter supplies neither action execution nor IPC kind by assumption.
def initial_binding_of_exec (table : Nat → Option Descriptor) (data control : Descriptor)
    (input : table 0 = some data) (output : table 1 = some data) (cancellation : table 3 = some control)
    (dataInherited : data.closeExec = false) (controlInherited : control.closeExec = false)
    (separate : data.object ≠ control.object) (ipc : Nat → Prop)
    (dataIpc : ipc data.object) (controlIpc : ipc control.object) :
    InitialEngineBinding ipc (rawReferences table) (rawFlags table) := by
  refine ⟨data.object, control.object, ?_, dataIpc, controlIpc⟩
  refine ⟨?_, ?_, ?_, separate, ?_, ?_, ?_, ?_⟩
  · simp [rawObjects, rawReferences, channelSlot, input]
  · simp [rawObjects, rawReferences, channelSlot, output]
  · simp [rawObjects, rawReferences, channelSlot, cancellation]
  · intro fd notInput notOutput notCancellation
    by_cases bounded : fd < 2 ^ 64
    · simp [rawObjects, bounded, rawReferences, channelSlot,
        Nat.mod_eq_of_lt bounded, notInput, notOutput, notCancellation]
    · simp [rawObjects, bounded]
  · simp [rawCloseExec, rawFlags, channelSlot, input, dataInherited]
  · simp [rawCloseExec, rawFlags, channelSlot, output, dataInherited]
  · simp [rawCloseExec, rawFlags, channelSlot, cancellation, controlInherited]

-- §FS-host-boundary.caller: The independently checked native facts feed the same
-- actual raw-table adapter, without supplying an already-safe initial engine table.
def initial_binding_of_evidence (table : Nat → Option Descriptor) (data control : Descriptor)
    (observed : ChannelEvidence table data control) (ipc : Nat → Prop)
    (dataIpc : ipc data.object) (controlIpc : ipc control.object) :
    InitialEngineBinding ipc (rawReferences table) (rawFlags table) :=
  initial_binding_of_exec table data control observed.1 observed.2.1 observed.2.2.1
    observed.2.2.2.1 observed.2.2.2.2.1 observed.2.2.2.2.2 ipc dataIpc controlIpc

end LeanCage.Host.NativeSpawn
