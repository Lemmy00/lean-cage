import LeanCageHost.GatewayWire

namespace LeanCage.Host.GatewayChecks

-- §FS-host-boundary.caller: The native signed-size guard agrees with this executable bound.
def bounded (size maximum : Nat) : Bool := size ≤ maximum

theorem bounded_iff (size maximum : Nat) : bounded size maximum = true ↔ size ≤ maximum := by
  simp [bounded]

theorem rejected_iff (size maximum : Nat) : bounded size maximum = false ↔ maximum < size := by
  simp [bounded]

-- §FS-host-boundary.caller: Native slots have the same individual bounds as the engine decoder.
def slotMaximum (index : Nat) : Nat := GatewayWire.fieldMax index

theorem policyMaximum : slotMaximum GatewayWire.policySlot = reportMax := rfl
theorem stdinMaximum : slotMaximum GatewayWire.stdinSlot = stdinMax := rfl
theorem timeoutMaximum : slotMaximum GatewayWire.timeoutSlot = 8 := rfl

end LeanCage.Host.GatewayChecks
