import VirtualMachineProofs.Progress

namespace LeanCage.Host.VirtualMachine

def Selected (descriptors : List (UInt64 × Nat)) (state : State) (boot diagnostic : UInt64) : Prop :=
  ∀ fd flags, (fd, flags) ∈ descriptors → fd ≠ 3 → fd ≠ boot → fd ≠ diagnostic →
    state.connection = some fd

-- §FS-host-boundary.transport: The actual poll list admits only the stored connection as data
-- source.
theorem events_selected (state : State) (boot diagnostic : UInt64) :
    Selected (events state boot diagnostic) state boot diagnostic := by
  intro fd flags member control bootDifferent diagnosticDifferent
  simp only [events, List.mem_append] at member
  rcases member with ((member | member) | member) | member
  · split at member <;> simp_all
  · split at member
    · simp at member
    · cases connection : state.connection with
      | none => simp [connection] at member
      | some value =>
        simp only [connection, Option.toList_some, List.map_cons, List.map_nil,
          List.mem_singleton, Prod.mk.injEq] at member
        exact congrArg some member.1.symm
  · split at member <;> simp_all
  · split at member <;> simp_all

-- §FS-host-boundary.transport: Every selected ready read contributes at its actual original
-- position.
theorem consume_ready_progress (descriptors : List (UInt64 × Nat)) (ready : List Nat)
    (boot diagnostic : UInt64) (now : Nat) (state : State)
    {trace : List Program.Event} {after : State}
    (selected : Selected descriptors state boot diagnostic)
    (run : Program.Returns (consumeReady descriptors ready boot diagnostic now state) trace after) :
    Progress state after trace := by
  induction descriptors generalizing state ready trace with
  | nil =>
    cases ready with
    | nil =>
      obtain ⟨rfl, rfl⟩ := Program.returns_pure _ run
      exact .refl _ _
    | cons head tail =>
      obtain ⟨rfl, rfl⟩ := Program.returns_pure _ run
      exact .fail _ _ _
  | cons head descriptors ih =>
    cases head with
    | mk fd flags =>
      cases ready with
      | nil =>
        obtain ⟨rfl, rfl⟩ := Program.returns_pure _ run
        exact .fail _ _ _
      | cons head ready =>
        unfold consumeReady at run
        try dsimp only at run
        split at run
        · simp only [program_pure_bind] at run
          split at run
          · obtain ⟨rfl, rfl⟩ := Program.returns_pure _ run
            exact .refl _ _
          · apply ih ready state ?_ run
            intro queried mask member
            exact selected queried mask (by simp [member])
        · obtain ⟨first, next, last, initial, ending, shape⟩ := Program.returns_bind_split _ _ run
          have progress := consume_progress fd boot diagnostic now state
            (selected fd flags (by simp)) initial
          try dsimp only at ending
          split at ending
          · obtain ⟨rfl, equal⟩ := Program.returns_pure _ ending
            cases equal
            simpa only [shape, List.append_nil] using progress
          · have selection : Selected descriptors next boot diagnostic := by
              intro queried mask member control bootDifferent diagnosticDifferent
              exact progress.connection queried (selected queried mask (by simp [member])
                control bootDifferent diagnosticDifferent)
            have final := ih ready next selection ending
            rw [shape]
            exact progress.trans final

end LeanCage.Host.VirtualMachine
