import FilesystemRootCatalogue

namespace LeanCage.Host.Kernel

variable {sourceProgram : Program UInt32}

-- §FS-host-boundary.ownership: The application records either no new root or the exact
-- SAME current birth and catalogue insertion. Unrelated historical receipts cannot fill it.
inductive CurrentRootCreation {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {all : List (ActorTick runtime)} (before : Capabilities) (oldCatalogue : Catalogue runtime all)
    (after : Capabilities) (newCatalogue : Catalogue runtime all) (tick : ActorTick runtime) (position : Nat) : Prop where
  | retained (caps : after = before.retain tick.after.shared) (catalogue : newCatalogue = oldCatalogue)
      (entries : tick.after.shared.entries = tick.before.shared.entries) :
      CurrentRootCreation before oldCatalogue after newCatalogue tick position
  | created (root : PrivateRoot) (birth : RootBirth runtime all root)
      (current : birth.tick = tick) (ordinal : birth.position = position)
      (caps : after = before.addRoot root) (catalogue : newCatalogue = Sigma.mk root birth :: oldCatalogue) :
      CurrentRootCreation before oldCatalogue after newCatalogue tick position

theorem CurrentRootCreation.labels {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {all : List (ActorTick runtime)} {before after : Capabilities} {oldCatalogue newCatalogue : Catalogue runtime all}
    {tick : ActorTick runtime} {position : Nat}
    (choice : CurrentRootCreation before oldCatalogue after newCatalogue tick position) :
    ∀ object, tick.before.shared.allocated object = true → after.family object = before.family object := by
  cases choice with
  | retained caps catalogue => rw [caps]; exact fun _ _ => rfl
  | created root birth current ordinal caps catalogue =>
    have fresh : tick.before.shared.allocated root.object = false := by rw [← current]; exact birth.fresh.1
    intro object allocated
    have different : object ≠ root.object := by intro same; rw [same, fresh] at allocated; cases allocated
    simp only [caps, Capabilities.addRoot, ite_eq_right different]

theorem CurrentRootCreation.included {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {all : List (ActorTick runtime)} {before after : Capabilities} {oldCatalogue newCatalogue : Catalogue runtime all}
    {tick : ActorTick runtime} {position : Nat}
    (choice : CurrentRootCreation before oldCatalogue after newCatalogue tick position) :
    ∀ record ∈ oldCatalogue, record ∈ newCatalogue := by
  cases choice with
  | retained caps catalogue => rw [catalogue]; exact fun _ member => member
  | created root birth current ordinal caps catalogue =>
    intro record member
    rw [catalogue]
    exact List.mem_cons_of_mem _ member

-- §AR-host-boundary.interfaces: The earlier receipt interface remains derivable exactly;
-- the stronger source choice also retains the complete catalogue transition.
theorem CurrentRootCreation.receipt {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {all : List (ActorTick runtime)} {before after : Capabilities} {oldCatalogue newCatalogue : Catalogue runtime all}
    {tick : ActorTick runtime} {position : Nat}
    (choice : CurrentRootCreation before oldCatalogue after newCatalogue tick position) :
    after = before.retain tick.after.shared ∨
      ∃ (root : PrivateRoot) (birth : RootBirth runtime all root),
        birth.tick = tick ∧ birth.position = position ∧ Sigma.mk root birth ∈ newCatalogue ∧ after = before.addRoot root := by
  cases choice with
  | retained caps catalogue => exact .inl caps
  | created root birth current ordinal caps catalogue =>
    exact .inr ⟨root, birth, current, ordinal, by rw [catalogue]; simp, caps⟩

end LeanCage.Host.Kernel
