import NativeChannelCode

namespace LeanCage.Host.ChannelCode

-- §AR-host-boundary.interfaces.gateway: These are raw source/primitive data.
-- Their values supply no private-channel or exclusive-reader conclusion.
inductive PairKind where
  | data | control

structure Invocation where
  key : NativeCode.SourceKey
  dataStorageLifetime : Nat
  controlStorageLifetime : Nat

def Invocation.WellFormed (invocation : Invocation) : Prop :=
  invocation.key.actionsLifetime ≠ invocation.key.attributesLifetime ∧
  invocation.dataStorageLifetime ≠ invocation.controlStorageLifetime ∧
  invocation.dataStorageLifetime ≠ invocation.key.actionsLifetime ∧
  invocation.dataStorageLifetime ≠ invocation.key.attributesLifetime ∧
  invocation.controlStorageLifetime ≠ invocation.key.actionsLifetime ∧
  invocation.controlStorageLifetime ≠ invocation.key.attributesLifetime ∧
  0 < invocation.key.actionsLifetime ∧ 0 < invocation.key.attributesLifetime ∧
  0 < invocation.dataStorageLifetime ∧ 0 < invocation.controlStorageLifetime

def Invocation.storage (invocation : Invocation) : PairKind → Nat
  | .data => invocation.dataStorageLifetime
  | .control => invocation.controlStorageLifetime

def ReferenceAt (references : NativeCode.References) (fd object description : Nat) : Prop :=
  ∃ handle, references.handles fd = some handle ∧ handle.object = object ∧ handle.description = description

structure PairUse where
  invocation : Invocation
  kind : PairKind
  position : Nat
  row : NativeCode.CallRow
  leftFd : Nat
  rightFd : Nat
  leftObject : Nat
  rightObject : Nat
  leftDescription : Nat
  rightDescription : Nat

def PairUse.Consistent (use : PairUse) : Prop :=
  use.invocation.WellFormed ∧ use.row.process = use.invocation.key.process ∧
  use.invocation.key.entryPosition ≤ use.position ∧
  use.row.operation = .socketPair 1 526337 0 ∧ use.row.product = .socketPair use.leftFd use.rightFd ∧
  use.leftFd ≤ 2147483647 ∧ use.rightFd ≤ 2147483647 ∧ use.leftFd ≠ use.rightFd ∧
  use.leftObject ≠ use.rightObject ∧ use.leftDescription ≠ use.rightDescription ∧
  ReferenceAt use.row.afterReferences use.leftFd use.leftObject use.leftDescription ∧
  ReferenceAt use.row.afterReferences use.rightFd use.rightObject use.rightDescription ∧
  use.row.afterReferences.closeOnExec use.leftFd = true ∧ use.row.afterReferences.closeOnExec use.rightFd = true

structure ReceiveUse where
  invocation : Invocation
  position : Nat
  row : NativeCode.CallRow
  descriptor : Nat
  extent : Nat
  dataObject : Nat
  dataDescription : Nat
  bytes : List Nat

def ReceiveUse.Consistent (use : ReceiveUse) : Prop :=
  use.invocation.WellFormed ∧ use.row.process = use.invocation.key.process ∧
  use.invocation.key.entryPosition ≤ use.position ∧ use.descriptor ≤ 2147483647 ∧
  0 < use.extent ∧ use.extent ≤ 65536 ∧
  use.row.operation = .receive use.descriptor use.extent 0 ∧
  ReferenceAt use.row.beforeReferences use.descriptor use.dataObject use.dataDescription ∧
  (use.row.product = .received use.bytes ∨ use.bytes = [] ∧ use.row.product = .none)

end LeanCage.Host.ChannelCode
