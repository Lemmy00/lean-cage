import LeanCageHost.Effects

namespace LeanCage.Host.Filesystem

-- §FS-host-boundary.lookup: The parser accepts one exact ABI result, not a truncated flag word.
theorem lookup_word_exact (width : Nat) (reply : Reply) (value : Nat) :
    Lookup.word? width reply = some value ↔
      reply.1 = 0 ∧ reply.2.size = width ∧ fromLittleEndian reply.2 = value := by
  simp only [Lookup.word?]
  split
  · rename_i accepted
    simp only [Bool.and_eq_true, beq_iff_eq] at accepted
    simp only [Option.some.injEq]
    exact ⟨fun decoded => ⟨accepted.1, accepted.2, decoded⟩, fun exact => exact.2.2⟩
  · rename_i rejected
    simp only [Bool.and_eq_true, beq_iff_eq] at rejected
    constructor
    · intro impossible
      cases impossible
    · intro exact
      exact False.elim (rejected ⟨exact.1, exact.2.1⟩)

theorem lookup_ext_exact (reply : Reply) : Lookup.extAllowed reply = true ↔
    ∃ flags, reply.1 = 0 ∧ reply.2.size = 4 ∧ fromLittleEndian reply.2 = flags ∧
      flags &&& (Lookup.casefoldFlag ||| Lookup.encryptionFlag) = 0 := by
  unfold Lookup.extAllowed
  split
  · rename_i absent
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨flags, zero, width, decoded, mask⟩
    have present := (lookup_word_exact 4 reply flags).mpr ⟨zero, width, decoded⟩
    rw [absent] at present
    cases present
  · rename_i flags decoded
    rw [beq_iff_eq]
    obtain ⟨zero, width, actual⟩ := (lookup_word_exact 4 reply flags).mp decoded
    constructor
    · intro mask
      exact ⟨flags, zero, width, actual, mask⟩
    · rintro ⟨other, _, _, same, mask⟩
      have equal : flags = other := actual.symm.trans same
      simpa only [equal] using mask

-- §AR-host-boundary.primitives: This grammar retains both actual requests and exact observations.
def Lookup.Accepted (fd : UInt64) (events : List (Request × Reply)) : Prop :=
  (∃ observed, events = [({ op := .filesystemType, first := fd }, observed)] ∧
    observed.1 = 0 ∧ observed.2.size = 8 ∧ fromLittleEndian observed.2 = Lookup.tmpMagic) ∨
  (∃ observed flags, events = [({ op := .filesystemType, first := fd }, observed),
      ({ op := .inodeFlags, first := fd }, flags)] ∧
    observed.1 = 0 ∧ observed.2.size = 8 ∧ fromLittleEndian observed.2 = Lookup.extMagic ∧
    Lookup.extAllowed flags = true)

private theorem returns_pure {α : Type} (value : α) {events : List (Request × Reply)} {result : α}
    (run : Returns (.pure value) events result) : events = [] ∧ result = value := by
  cases run
  exact ⟨rfl, rfl⟩

theorem lookup_check_source {fd : UInt64} {events : List (Request × Reply)}
    (run : Returns (Lookup.check fd) events true) : Lookup.Accepted fd events := by
  unfold Lookup.check at run
  cases run with
  | call _ _ observed tail _ rest =>
    dsimp only at rest
    split at rest
    · cases rest
    · rename_i magic parsed
      split at rest
      · rename_i same
        cases rest
        have actual : Lookup.word? 8 observed = some Lookup.tmpMagic := by
          simpa only [beq_iff_eq.mp same] using parsed
        obtain ⟨zero, width, value⟩ := (lookup_word_exact 8 observed _).mp actual
        exact .inl ⟨observed, rfl, zero, width, value⟩
      · rename_i different
        split at rest
        · rename_i same
          cases rest with
          | call _ _ flags tail _ final =>
            obtain ⟨rfl, accepted⟩ := returns_pure _ final
            have actual : Lookup.word? 8 observed = some Lookup.extMagic := by
              have same := beq_iff_eq.mp same
              simpa only [same] using parsed
            obtain ⟨zero, width, value⟩ := (lookup_word_exact 8 observed _).mp actual
            exact .inr ⟨observed, flags, rfl, zero, width, value, accepted.symm⟩
        · cases rest

theorem lookup_check_complete {fd : UInt64} {events : List (Request × Reply)}
    (accepted : Lookup.Accepted fd events) : Returns (Lookup.check fd) events true := by
  rcases accepted with ⟨observed, rfl, zero, width, value⟩ |
    ⟨observed, flags, rfl, zero, width, value, allowed⟩
  · have parsed := (lookup_word_exact 8 observed Lookup.tmpMagic).mpr ⟨zero, width, value⟩
    unfold Lookup.check
    apply Returns.call
    rw [parsed]
    exact .pure _
  · have parsed := (lookup_word_exact 8 observed Lookup.extMagic).mpr ⟨zero, width, value⟩
    unfold Lookup.check
    apply Returns.call
    rw [parsed]
    change Returns (.call { op := .inodeFlags, first := fd }
      (fun reply => .pure (Lookup.extAllowed reply))) [({ op := .inodeFlags, first := fd }, flags)] true
    apply Returns.call
    rw [allowed]
    exact .pure _

theorem adapter_returns_bind_split {α β : Type} (program : Program α) (next : α → Program β)
    {events : List (Request × Reply)} {value : β} (run : Returns (program.bind next) events value) :
    ∃ first intermediate last, Returns program first intermediate ∧ Returns (next intermediate) last value ∧
      events = first ++ last := by
  induction program generalizing events with
  | pure result => exact ⟨[], result, events, .pure result, run, rfl⟩
  | call request continuation ih =>
    cases run with
    | call _ _ reply tail _ rest =>
      obtain ⟨first, intermediate, last, initial, final, shape⟩ := ih reply rest
      exact ⟨(request, reply) :: first, intermediate, last,
        .call request continuation reply first intermediate initial, final, by simp [shape]⟩

theorem adapter_prefix_bind_split {α β : Type} (program : Program α) (next : α → Program β)
    {events : List (Request × Option Reply)} (run : Prefix (program.bind next) events) :
    Prefix program events ∨ ∃ first intermediate last,
      Returns program first intermediate ∧ Prefix (next intermediate) last ∧
        events = first.map (fun item => (item.1, some item.2)) ++ last := by
  induction program generalizing events with
  | pure value => exact .inr ⟨[], value, events, .pure value, run, rfl⟩
  | call request continuation ih =>
    cases run with
    | empty => exact .inl (.empty _)
    | lost => exact .inl (.lost _ _)
    | returned _ _ reply tail rest =>
      rcases ih reply rest with earlier | ⟨first, value, last, initial, final, shape⟩
      · exact .inl (.returned request continuation reply tail earlier)
      · exact .inr ⟨(request, reply) :: first, value, last,
          .call request continuation reply first value initial, final, by simp [shape]⟩

-- §FS-host-boundary.acceptance: Interrupted adapters retain all earlier raw operations.
inductive LoweredPrefix {α : Type} :
    Program α → List (Request × Option Reply) → List (Request × Option Reply) → Prop where
  | stop (program : Program α) : LoweredPrefix program [] []
  | active (request : Request) (next : Reply → Program α) (inside : List (Request × Option Reply))
      (source : Prefix (guardedCall request) inside) :
      LoweredPrefix (.call request next) [(request, none)] inside
  | completed (request : Request) (next : Reply → Program α) (reply : Reply)
      (inside : List (Request × Reply)) (logical tail : List (Request × Option Reply))
      (adapter : Returns (guardedCall request) inside reply) (rest : LoweredPrefix (next reply) logical tail) :
      LoweredPrefix (.call request next) ((request, some reply) :: logical)
        (inside.map (fun item => (item.1, some item.2)) ++ tail)

theorem lowered_prefix_source {α : Type} (program : Program α)
    {events : List (Request × Option Reply)} (run : Prefix program.lower events) :
    ∃ logical, LoweredPrefix program logical events := by
  induction program generalizing events with
  | pure value => cases run; exact ⟨[], .stop _⟩
  | call request next ih =>
    change Prefix ((guardedCall request).bind (fun reply => (next reply).lower)) events at run
    rcases adapter_prefix_bind_split _ _ run with active | ⟨inside, reply, tail, adapter, rest, shape⟩
    · exact ⟨_, .active request next events active⟩
    · obtain ⟨logical, refined⟩ := ih reply rest
      rw [shape]
      exact ⟨_, .completed request next reply inside logical tail adapter refined⟩

theorem lowered_logical_prefix {α : Type} {program : Program α}
    {logical raw : List (Request × Option Reply)} (run : LoweredPrefix program logical raw) :
    Prefix program logical := by
  induction run with
  | stop program => exact .empty _
  | active request next inside source => exact .lost _ _
  | completed request next reply inside logical tail adapter rest ih =>
    exact .returned request next reply logical ih

private theorem base_bind_assoc {α β γ : Type} (first : BaseIO α) (second : α → BaseIO β)
    (third : β → BaseIO γ) : (first >>= second) >>= third = first >>= (fun value => second value >>= third) := by
  funext state
  cases first state
  rfl

private theorem interpret_bind {α β : Type} (call : Request → BaseIO Reply)
    (program : Program α) (next : α → Program β) :
    (program.bind next).interpret call = (do
      let value ← program.interpret call
      (next value).interpret call) := by
  induction program with
  | pure value => rfl
  | call request continuation ih =>
    change (call request >>= fun reply => ((continuation reply).bind next).interpret call) =
      (call request >>= fun reply => (continuation reply).interpret call) >>= fun value => (next value).interpret call
    rw [base_bind_assoc]
    exact congrArg (fun rest => call request >>= rest) (funext ih)

-- §AR-host-boundary.interfaces: The live caller executes the proved lowering, not another guard.
theorem call_guarded_source (request : Request) :
    call request = (guardedCall request).interpret rawCall := rfl

theorem execute_lowered_source {α : Type} (program : Program α) :
    execute program = program.lower.interpret rawCall := by
  induction program with
  | pure value => rfl
  | call request next ih =>
    change ((guardedCall request).interpret rawCall >>= fun reply => execute (next reply)) =
      ((guardedCall request).bind (fun reply => (next reply).lower)).interpret rawCall
    rw [interpret_bind]
    exact congrArg (fun continuation => (guardedCall request).interpret rawCall >>= continuation)
      (funext ih)

end LeanCage.Host.Filesystem
