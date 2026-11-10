import Std

namespace LeanCage.Host.BootstrapCode

-- §AR-host-boundary.interfaces: These are the native bootstrap's actual byte paths.
def suffix : List Nat := [47, 112, 121, 116, 104, 111, 110, 47, 108, 101, 97, 110, 99, 97, 103, 101, 47, 95, 104, 111, 115, 116, 46, 97, 98, 105, 51, 46, 115, 111]
def executable : List Nat := [47, 98, 105, 110, 47, 108, 101, 97, 110, 99, 97, 103, 101, 45, 104, 111, 115, 116]
def results : List Nat := [47, 46, 116, 111, 111, 108, 115, 47, 112, 114, 111, 100, 117, 99, 116, 47, 114, 117, 110, 115]

structure Layout where
  root : List Nat
  engine : List Nat
  defaultResults : List Nat
  deriving DecidableEq

def supported (path : List Nat) : Bool :=
  path.length ≤ 4095 && suffix.length < path.length && path.head? == some 47 &&
  path.drop (path.length - suffix.length) == suffix

-- §FS-host-boundary.caller: Filename checks precede slicing and bounded global copies.
def layout (loaded canonical : List Nat) : Option Layout :=
  if supported loaded && supported canonical then
    let api := loaded.take (loaded.length - suffix.length)
    let root := canonical.take (canonical.length - suffix.length)
    if root.length + executable.length + 1 ≤ 4096 && api.length + results.length + 1 ≤ 4096 then
      some ⟨root, root ++ executable, api ++ results⟩
    else none
  else none

theorem layout_supported {loaded canonical : List Nat} {value : Layout}
    (accepted : layout loaded canonical = some value) :
    supported loaded = true ∧ supported canonical = true := by
  unfold layout at accepted
  split at accepted
  · exact Bool.and_eq_true_iff.mp (by assumption)
  · cases accepted

-- §FS-host-boundary.caller: The result describes the exact copied spelling.
-- Namespace identity is supplied separately by the actual loader and lookup.
theorem layout_bytes {loaded canonical : List Nat} {value : Layout}
    (accepted : layout loaded canonical = some value) :
    value.root = canonical.take (canonical.length - suffix.length) ∧
    value.engine = value.root ++ executable ∧
    value.defaultResults = loaded.take (loaded.length - suffix.length) ++ results ∧
    value.engine.length + 1 ≤ 4096 ∧ value.defaultResults.length + 1 ≤ 4096 := by
  unfold layout at accepted
  split at accepted
  · dsimp only at accepted
    split at accepted
    · rename_i fits
      have bounds := Bool.and_eq_true_iff.mp fits
      have engineBound := of_decide_eq_true bounds.1
      have resultsBound := of_decide_eq_true bounds.2
      cases accepted
      refine ⟨rfl, rfl, rfl, ?_, ?_⟩
      · simpa only [List.length_append] using engineBound
      · simpa only [List.length_append] using resultsBound
    · cases accepted
  · cases accepted

end LeanCage.Host.BootstrapCode
