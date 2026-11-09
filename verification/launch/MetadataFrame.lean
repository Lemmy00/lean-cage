import MetadataControl
import LeanCageEntry.State

set_option autoImplicit false

namespace LeanCage.Entry.MetadataFrame

open LeanCageM3.Metadata

-- §AR-metadata.primitives: These updates describe only one open or one close.
def opened (before : State) (fd : UInt32) (handle : Handle) : State :=
  { before with handles := fun slot => if slot = fd then some handle else before.handles slot }

def closed (before : State) (fd : UInt32) : State :=
  { before with handles := fun slot => if slot = fd then none else before.handles slot }

-- §AR-metadata.primitives: The open's decoded word names the fresh descriptor of that operation.
-- No field assumes the metadata helper's sequence, ownership, bound or final state.
structure PrimitiveContract where
  returned : State → LeanCageM3.Metadata.Request → LeanCageM3.Metadata.Reply → State → Prop
  open_return : ∀ before path reply after,
    returned before ⟨.open, 0, 0, path⟩ reply after →
    match openDescriptor reply with
    | none => after = before
    | some fd => ∃ handle, before.handles fd = none ∧ handle.readable = true ∧
        handle.writable = false ∧ handle.cloexec = true ∧ after = opened before fd handle
  read_return : ∀ before fd amount reply after,
    returned before ⟨.read, fd, amount, ""⟩ reply after → after = before
  close_return : ∀ before fd reply after,
    returned before ⟨.close, fd, 0, ""⟩ reply after → fd.toNat ≤ 2147483647 → after = closed before fd

-- §FS-metadata.ownership: Freshness is discharged by open, and the actual selected close
-- restores it.
theorem close_open (before : State) (fd : UInt32) (handle : Handle) (fresh : before.handles fd = none) :
    closed (opened before fd handle) fd = before := by
  have handles : (fun slot => if slot = fd then none else
      (if slot = fd then some handle else before.handles slot)) = before.handles := by
    funext slot
    by_cases same : slot = fd
    · subst slot; simp only [↓reduceIte]; exact fresh.symm
    · simp only [same, ↓reduceIte]
  change { before with handles := fun slot => if slot = fd then none else
    (if slot = fd then some handle else before.handles slot) } = before
  rw [handles]

theorem loop_frame (platform : PrimitiveContract) (fuel : Nat) (path : String) (fd : UInt32)
    (limit : Nat) (bytes : ByteArray) {before after : State} {trace : List (LeanCageM3.Metadata.Request × LeanCageM3.Metadata.Reply)}
    {result : Result} (run : Runs platform.returned (loop fuel path fd limit bytes) before trace result after) :
    after = before := by
  induction fuel generalizing bytes before trace with
  | zero =>
    simp only [loop, pure] at run
    split at run <;> cases run <;> rfl
  | succ fuel ih =>
    simp only [loop, pure] at run
    split at run
    · cases run; rfl
    · cases run with
      | call _ _ reply operation rest =>
        have same := platform.read_return _ _ _ _ _ operation
        dsimp only at rest
        split at rest
        · cases rest; exact same
        · split at rest
          · cases rest; exact same
          · split at rest
            · cases rest; exact same
            · exact (ih (bytes ++ reply.2) rest).trans same

theorem finish_frame (platform : PrimitiveContract) (path : String) (fd : UInt32)
    (input : Result) (fits : fd.toNat ≤ 2147483647) {before after : State}
    {trace : List (LeanCageM3.Metadata.Request × LeanCageM3.Metadata.Reply)} {result : Result}
    (run : Runs platform.returned (finish path fd input) before trace result after) :
    after = closed before fd := by
  simp only [finish, pure] at run
  cases run with
  | call _ _ reply operation rest =>
    have same := platform.close_return _ _ _ _ operation fits
    cases input with
    | error error => dsimp only at rest; cases rest; exact same
    | ok bytes =>
      dsimp only at rest
      split at rest
      · cases rest; exact same
      · split at rest <;> cases rest <;> exact same

-- §AR-metadata.frame: Derive the whole helper frame from its actual per-operation execution.
theorem bounded_frame (platform : PrimitiveContract) (path : String) (limit : Nat)
    {before after : State} {trace : List (LeanCageM3.Metadata.Request × LeanCageM3.Metadata.Reply)} {result : Result}
    (run : Runs platform.returned (bounded path limit) before trace result after) : after = before := by
  unfold bounded at run
  split at run
  · cases run; rfl
  · cases run with
    | call _ _ reply operation rest =>
      have opening := platform.open_return _ _ _ _ operation
      dsimp only at rest
      cases descriptor : openDescriptor reply with
      | none =>
        rw [descriptor] at opening
        simp only [descriptor, pure] at rest
        cases rest; exact opening
      | some fd =>
        rw [descriptor] at opening
        obtain ⟨handle, fresh, readable, writable, cloexec, same⟩ := opening
        simp only [descriptor] at rest
        obtain ⟨first, remaining, value, middle, events, front, last⟩ := runs_bind_split _ _ rest
        have reading := loop_frame platform (limit + 1) path fd limit .empty front
        have closing := finish_frame platform path fd value (openDescriptor_bound reply fd descriptor) last
        rw [reading, same] at closing
        exact closing.trans (close_open _ _ _ fresh)

theorem bounded_preserves_handles (platform : PrimitiveContract) (path : String) (limit : Nat)
    {before after : State} {trace : List (LeanCageM3.Metadata.Request × LeanCageM3.Metadata.Reply)} {result : Result}
    (run : Runs platform.returned (bounded path limit) before trace result after) :
    after.handles = before.handles ∧ after.filters = before.filters := by
  rw [bounded_frame platform path limit run]
  exact ⟨rfl, rfl⟩

theorem loop_prefix_frame (platform : PrimitiveContract) (fuel : Nat) (path : String) (fd : UInt32)
    (limit : Nat) (bytes : ByteArray) {before after : State}
    {trace : List (LeanCageM3.Metadata.Request × LeanCageM3.Metadata.Reply)} {last : Program Result}
    (run : Prefix platform.returned (loop fuel path fd limit bytes) before trace last after) :
    after = before := by
  induction fuel generalizing bytes before trace with
  | zero => simp only [loop, pure] at run; split at run <;> cases run <;> rfl
  | succ fuel ih =>
    simp only [loop, pure] at run
    split at run
    · cases run; rfl
    · cases run with
      | refl => rfl
      | call _ _ reply operation rest =>
        have same := platform.read_return _ _ _ _ _ operation
        dsimp only at rest
        split at rest
        · cases rest; exact same
        · split at rest
          · cases rest; exact same
          · split at rest
            · cases rest; exact same
            · exact (ih (bytes ++ reply.2) rest).trans same

theorem finish_prefix_frame (platform : PrimitiveContract) (path : String) (fd : UInt32)
    (input : Result) (fits : fd.toNat ≤ 2147483647) {before after : State}
    {trace : List (LeanCageM3.Metadata.Request × LeanCageM3.Metadata.Reply)} {last : Program Result}
    (run : Prefix platform.returned (finish path fd input) before trace last after) :
    after = before ∨ after = closed before fd := by
  simp only [finish, pure] at run
  cases run with
  | refl => exact .inl rfl
  | call _ _ reply operation rest =>
    right
    have same := platform.close_return _ _ _ _ operation fits
    cases input with
    | error error => dsimp only at rest; cases rest; exact same
    | ok bytes =>
      dsimp only at rest
      split at rest
      · cases rest; exact same
      · split at rest <;> cases rest <;> exact same

-- §FS-metadata.loss: A prefix may still hold its own fresh slot; prior slots remain owned.
def PrefixState (before after : State) : Prop :=
  after = before ∨ ∃ fd handle, before.handles fd = none ∧ handle.readable = true ∧
    handle.writable = false ∧ handle.cloexec = true ∧ after = opened before fd handle

theorem bounded_prefix_state (platform : PrimitiveContract) (path : String) (limit : Nat)
    {before after : State} {trace : List (LeanCageM3.Metadata.Request × LeanCageM3.Metadata.Reply)}
    {last : Program Result}
    (run : Prefix platform.returned (bounded path limit) before trace last after) :
    PrefixState before after := by
  unfold bounded at run
  split at run
  · cases run; exact .inl rfl
  · cases run with
    | refl => exact .inl rfl
    | call _ _ reply operation rest =>
      have opening := platform.open_return _ _ _ _ operation
      dsimp only at rest
      cases descriptor : openDescriptor reply with
      | none =>
        rw [descriptor] at opening
        simp only [descriptor, pure] at rest
        cases rest
        exact .inl opening
      | some fd =>
        rw [descriptor] at opening
        obtain ⟨handle, fresh, readable, writable, cloexec, same⟩ := opening
        simp only [descriptor] at rest
        rcases prefix_bind_split _ _ rest with ⟨current, frontier, _⟩ |
          ⟨first, remaining, value, middle, _, front, last⟩
        · have reading := loop_prefix_frame platform (limit + 1) path fd limit .empty frontier
          exact .inr ⟨fd, handle, fresh, readable, writable, cloexec, reading.trans same⟩
        · have reading := loop_frame platform (limit + 1) path fd limit .empty front
          rcases finish_prefix_frame platform path fd value (openDescriptor_bound reply fd descriptor) last with
            pending | closed
          · exact .inr ⟨fd, handle, fresh, readable, writable, cloexec, pending.trans (reading.trans same)⟩
          · left
            rw [reading, same] at closed
            exact closed.trans (close_open _ _ _ fresh)

theorem prefix_preserves_existing {before after : State} (frame : PrefixState before after)
    (fd : UInt32) (handle : Handle) (existing : before.handles fd = some handle) :
    after.handles fd = some handle := by
  rcases frame with rfl | ⟨openedFd, openedHandle, fresh, _, _, _, rfl⟩
  · exact existing
  · have different : fd ≠ openedFd := by intro same; subst fd; rw [fresh] at existing; contradiction
    simpa only [opened, different, ↓reduceIte] using existing

theorem prefix_preserves_filters {before after : State} (frame : PrefixState before after) :
    after.filters = before.filters := by
  rcases frame with rfl | ⟨_, _, _, _, _, _, rfl⟩ <;> rfl

end LeanCage.Entry.MetadataFrame
