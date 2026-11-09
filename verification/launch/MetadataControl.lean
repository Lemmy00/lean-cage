import LeanCageM3.Metadata

set_option autoImplicit false

namespace LeanCageM3.Metadata

-- §AR-metadata.control: Each returned primitive belongs to this same executable program.
inductive Runs {σ α : Type} (effect : σ → Request → Reply → σ → Prop) :
    Program α → σ → List (Request × Reply) → α → σ → Prop
  | pure (value : α) (state : σ) : Runs effect (.pure value) state [] value state
  | call (request : Request) (next : Reply → Program α) (reply : Reply)
      {before middle after : σ} {trace : List (Request × Reply)} {value : α}
      (operation : effect before request reply middle)
      (rest : Runs effect (next reply) middle trace value after) :
      Runs effect (.call request next) before ((request, reply) :: trace) value after

inductive Prefix {σ α : Type} (effect : σ → Request → Reply → σ → Prop) :
    Program α → σ → List (Request × Reply) → Program α → σ → Prop
  | refl (program : Program α) (state : σ) : Prefix effect program state [] program state
  | call (request : Request) (next : Reply → Program α) (reply : Reply)
      {before middle after : σ} {trace : List (Request × Reply)} {last : Program α}
      (operation : effect before request reply middle)
      (rest : Prefix effect (next reply) middle trace last after) :
      Prefix effect (.call request next) before ((request, reply) :: trace) last after

-- §FS-metadata.loss: Loss during a primitive or allocation supplies no returned result.
inductive Outcome (σ α : Type) where
  | returned (value : α) (state : σ)
  | waiting (program : Program α) (state : σ)
  | lost (state : σ)

-- §FS-metadata.loss: Waiting and loss carry no bytes or error result for a caller continuation.
def Outcome.value? {σ α : Type} : Outcome σ α → Option α
  | .returned value _ => some value
  | .waiting _ _ | .lost _ => none

theorem waiting_has_no_result {σ α : Type} (program : Program α) (state : σ) :
    (Outcome.waiting program state).value? = none := rfl

theorem lost_has_no_result {σ α : Type} (state : σ) :
    (Outcome.lost (α := α) state).value? = none := rfl

inductive Execution {σ α : Type} (effect : σ → Request → Reply → σ → Prop)
    (loss : Program α → σ → σ → Prop) (program : Program α) (before : σ) : Outcome σ α → Prop
  | returned {trace : List (Request × Reply)} {value : α} {after : σ}
      (run : Runs effect program before trace value after) : Execution effect loss program before (.returned value after)
  | waiting {trace : List (Request × Reply)} {last : Program α} {after : σ}
      (executionPrefix : Prefix effect program before trace last after) : Execution effect loss program before (.waiting last after)
  | lost {trace : List (Request × Reply)} {last : Program α} {current after : σ}
      (executionPrefix : Prefix effect program before trace last current) (stopped : loss last current after) :
      Execution effect loss program before (.lost after)

theorem runs_bind_split {σ α β : Type} {effect : σ → Request → Reply → σ → Prop}
    (program : Program α) (next : α → Program β) {before after : σ}
    {trace : List (Request × Reply)} {result : β}
    (run : Runs effect (program.bind next) before trace result after) :
    ∃ first rest value middle, trace = first ++ rest ∧
      Runs effect program before first value middle ∧ Runs effect (next value) middle rest result after := by
  induction program generalizing before trace with
  | pure value => exact ⟨[], trace, value, before, rfl, .pure _ _, run⟩
  | call request rest ih =>
    change Runs effect (.call request (fun reply => (rest reply).bind next)) before trace result after at run
    cases run with
    | call _ _ reply operation tail =>
      obtain ⟨first, remaining, value, middle, events, front, last⟩ := ih reply tail
      exact ⟨(request, reply) :: first, remaining, value, middle, by simp [events],
        .call request rest reply operation front, last⟩

-- §FS-metadata.loss: A finite prefix may stop inside the body or in its close continuation.
theorem prefix_bind_split {σ α β : Type} {effect : σ → Request → Reply → σ → Prop}
    (program : Program α) (next : α → Program β) {before after : σ}
    {trace : List (Request × Reply)} {last : Program β}
    (run : Prefix effect (program.bind next) before trace last after) :
    (∃ current, Prefix effect program before trace current after ∧ last = current.bind next) ∨
      ∃ first rest value middle, trace = first ++ rest ∧
        Runs effect program before first value middle ∧ Prefix effect (next value) middle rest last after := by
  induction program generalizing before trace with
  | pure value => exact .inr ⟨[], trace, value, before, rfl, .pure _ _, run⟩
  | call request rest ih =>
    change Prefix effect (.call request (fun reply => (rest reply).bind next)) before trace last after at run
    cases run with
    | refl => exact .inl ⟨.call request rest, .refl _ _, rfl⟩
    | call _ _ reply operation tail =>
      rcases ih reply tail with ⟨current, frontier, equal⟩ | ⟨first, remaining, value, middle, events, front, last⟩
      · exact .inl ⟨current, .call request rest reply operation frontier, equal⟩
      · exact .inr ⟨(request, reply) :: first, remaining, value, middle, by simp [events],
          .call request rest reply operation front, last⟩

theorem readAmount_bound (limit size : Nat) : readAmount limit size ≤ 4096 := Nat.min_le_left _ _

theorem readAmount_positive (limit size : Nat) (active : size ≤ limit) : 0 < readAmount limit size := by
  simp only [readAmount]
  omega

theorem readAmount_exact (limit size : Nat) : (readAmount limit size).toUInt64.toNat = readAmount limit size := by
  apply UInt64.toNat_ofNat_of_lt'
  have bounded := readAmount_bound limit size
  change readAmount limit size < 18446744073709551616
  omega

theorem openDescriptor_bound (reply : Reply) (fd : UInt32) (accepted : openDescriptor reply = some fd) :
    fd.toNat ≤ 2147483647 := by
  unfold openDescriptor at accepted
  split at accepted
  · contradiction
  · rename_i guard
    have fits : reply.1.toNat ≤ 2147483647 := by
      by_cases fit : reply.1.toNat ≤ 2147483647
      · exact fit
      · have bad : reply.1.toNat > 2147483647 := by omega
        exact False.elim (guard (by simp [bad]))
    cases accepted
    rw [UInt64.toNat_toUInt32]
    exact Nat.le_trans (Nat.mod_le _ _) fits

-- §FS-metadata.bounds: Reject an embedded NUL before any open request.
theorem bounded_rejects_nul (path : String) (limit : Nat)
    (nul : path.toUTF8.data.toList.contains 0 = true) :
    bounded path limit = .pure (.error ⟨.open, 22, path⟩) := by
  unfold bounded
  rw [nul]
  rfl

theorem loop_return_bound {σ : Type} {effect : σ → Request → Reply → σ → Prop}
    (fuel : Nat) (path : String) (fd : UInt32) (limit : Nat) (bytes : ByteArray)
    {before after : σ} {trace : List (Request × Reply)} {result : ByteArray}
    (initial : bytes.size ≤ limit + 1)
    (run : Runs effect (loop fuel path fd limit bytes) before trace (.ok result) after) :
    result.size ≤ limit + 1 := by
  induction fuel generalizing bytes before trace with
  | zero =>
    simp only [loop, pure] at run
    split at run
    · cases run; exact initial
    · cases run
  | succ fuel ih =>
    simp only [loop, pure] at run
    split at run
    · cases run; exact initial
    · cases run with
      | call _ _ reply operation rest =>
        dsimp only at rest
        split at rest
        · cases rest
        · split at rest
          · cases rest
          · rename_i valid
            split at rest
            · cases rest; exact initial
            · have checked : reply.2.size ≤ readAmount limit bytes.size := by
                by_cases fit : reply.2.size ≤ readAmount limit bytes.size
                · exact fit
                · have bad : reply.2.size > readAmount limit bytes.size := by omega
                  exact False.elim (valid (by simp [bad]))
              apply ih (bytes ++ reply.2) (by
                rw [ByteArray.size_append]
                have remaining : readAmount limit bytes.size ≤ limit + 1 - bytes.size := Nat.min_le_right _ _
                omega) rest

theorem finish_preserves_ok {σ : Type} {effect : σ → Request → Reply → σ → Prop}
    (path : String) (fd : UInt32) (input : Result) {before after : σ}
    {trace : List (Request × Reply)} {bytes : ByteArray}
    (run : Runs effect (finish path fd input) before trace (.ok bytes) after) : input = .ok bytes := by
  cases input with
  | error error =>
    simp only [finish, pure] at run
    cases run with | call _ _ _ _ rest => cases rest
  | ok original =>
    simp only [finish, pure] at run
    cases run with
    | call _ _ reply operation rest =>
      dsimp only at rest
      split at rest
      · cases rest; rfl
      · split at rest <;> cases rest

theorem bounded_return_bound {σ : Type} {effect : σ → Request → Reply → σ → Prop}
    (path : String) (limit : Nat) {before after : σ}
    {trace : List (Request × Reply)} {bytes : ByteArray}
    (run : Runs effect (bounded path limit) before trace (.ok bytes) after) : bytes.size ≤ limit + 1 := by
  unfold bounded at run
  split at run
  · cases run
  · cases run with
    | call _ _ reply operation rest =>
      dsimp only at rest
      cases decoded : openDescriptor reply with
      | none => simp only [decoded, pure] at rest; cases rest
      | some fd =>
        simp only [decoded] at rest
        obtain ⟨first, remaining, value, middle, events, front, last⟩ := runs_bind_split _ _ rest
        have equal := finish_preserves_ok path fd value last
        cases equal
        exact loop_return_bound (limit + 1) path fd limit .empty (by simp) front

-- §FS-metadata.bounds: A read carries the owned descriptor and an exact bounded machine count.
def ReadRequest (fd : UInt32) (request : Request) : Prop :=
  request.op = .read ∧ request.fd = fd ∧ request.path = "" ∧
    0 < request.amount.toNat ∧ request.amount.toNat ≤ 4096

theorem loop_request (limit size : Nat) (fd : UInt32) (active : size ≤ limit) :
    ReadRequest fd ⟨.read, fd, (readAmount limit size).toUInt64, ""⟩ := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · rw [readAmount_exact]; exact readAmount_positive limit size active
  · rw [readAmount_exact]; exact readAmount_bound limit size

theorem loop_trace {σ : Type} {effect : σ → Request → Reply → σ → Prop}
    (fuel : Nat) (path : String) (fd : UInt32) (limit : Nat) (bytes : ByteArray)
    {before after : σ} {trace : List (Request × Reply)} {result : Result}
    (run : Runs effect (loop fuel path fd limit bytes) before trace result after) :
    ∀ entry ∈ trace, ReadRequest fd entry.1 := by
  induction fuel generalizing bytes before trace with
  | zero => simp only [loop, pure] at run; split at run <;> cases run <;> simp
  | succ fuel ih =>
    simp only [loop, pure] at run
    split at run
    · cases run; simp
    · rename_i active
      cases run with
      | call _ _ reply operation rest =>
        intro entry member
        rcases List.mem_cons.mp member with same | member
        · cases same
          exact loop_request limit bytes.size fd (by omega)
        · dsimp only at rest
          split at rest
          · cases rest; contradiction
          · split at rest
            · cases rest; contradiction
            · split at rest
              · cases rest; contradiction
              · exact ih (bytes ++ reply.2) rest entry member

theorem finish_trace {σ : Type} {effect : σ → Request → Reply → σ → Prop}
    (path : String) (fd : UInt32) (input : Result) {before after : σ}
    {trace : List (Request × Reply)} {result : Result}
    (run : Runs effect (finish path fd input) before trace result after) :
    ∃ reply, trace = [(⟨.close, fd, 0, ""⟩, reply)] := by
  simp only [finish, pure] at run
  cases run with
  | call _ _ reply operation rest =>
    refine ⟨reply, ?_⟩
    cases input with
    | error error => dsimp only at rest; cases rest; rfl
    | ok bytes =>
      dsimp only at rest
      split at rest
      · cases rest; rfl
      · split at rest <;> cases rest <;> rfl

-- §FS-metadata.ownership: This statement names the same open, all reads, and the final close.
def OwnedTrace (path : String) (trace : List (Request × Reply)) : Prop :=
  trace = [] ∨ ∃ reply rest, trace = (⟨.open, 0, 0, path⟩, reply) :: rest ∧
    ((openDescriptor reply = none ∧ rest = []) ∨
      ∃ fd reads closed, openDescriptor reply = some fd ∧
        rest = reads ++ [(⟨.close, fd, 0, ""⟩, closed)] ∧
        ∀ entry ∈ reads, ReadRequest fd entry.1)

theorem bounded_owned_trace {σ : Type} {effect : σ → Request → Reply → σ → Prop}
    (path : String) (limit : Nat) {before after : σ} {trace : List (Request × Reply)} {result : Result}
    (run : Runs effect (bounded path limit) before trace result after) : OwnedTrace path trace := by
  unfold bounded at run
  split at run
  · cases run; exact .inl rfl
  · cases run with
    | call _ _ reply operation rest =>
      right
      refine ⟨reply, _, rfl, ?_⟩
      dsimp only at rest
      cases descriptor : openDescriptor reply with
      | none =>
        simp only [descriptor, pure] at rest
        cases rest
        exact .inl ⟨rfl, rfl⟩
      | some fd =>
        simp only [descriptor] at rest
        obtain ⟨first, remaining, value, middle, events, front, last⟩ := runs_bind_split _ _ rest
        obtain ⟨closed, closing⟩ := finish_trace path fd value last
        exact .inr ⟨fd, first, closed, rfl, by rw [events, closing], loop_trace _ _ _ _ _ front⟩

end LeanCageM3.Metadata
