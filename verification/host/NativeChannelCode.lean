import NativeCode

namespace LeanCage.Host.NativeChannels

-- §AR-host-boundary.interfaces.gateway: Observe object identities in the actual full exec table.
def objectAt (references : NativeCode.References) (fd : Nat) : Option Nat :=
  match references.handles fd with
  | none => none
  | some handle => some handle.object

-- §FS-host-boundary.caller: Source actions produce these fields; this shared
-- proposition supplies no already-safe raw engine table or IPC-kind assertion.
def Evidence (references : NativeCode.References) (data control : Nat) : Prop :=
  objectAt references 0 = some data ∧ objectAt references 1 = some data ∧
  objectAt references 3 = some control ∧ references.closeOnExec 0 = false ∧
  references.closeOnExec 1 = false ∧ references.closeOnExec 3 = false ∧ data ≠ control

end LeanCage.Host.NativeChannels
