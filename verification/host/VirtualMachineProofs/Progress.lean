import VirtualMachineProofs.Consume

namespace LeanCage.Host.VirtualMachine

theorem program_pure_bind {α β : Type} (value : α) (next : α → Program β) :
    ((pure value : Program α) >>= next) = next value := rfl


theorem program_bind_assoc {α β γ : Type} (first : Program α)
    (next : α → Program β) (last : β → Program γ) :
    ((first >>= next) >>= last) = (first >>= fun value => next value >>= last) := by
  induction first with
  | pure => rfl
  | call effect rest ih =>
    change Program.call effect (fun reply => (rest reply >>= next) >>= last) =
      Program.call effect (fun reply => rest reply >>= fun value => next value >>= last)
    congr 1
    funext reply
    exact ih reply

theorem program_bind_except {ε α β γ : Type} (observed : Except ε α)
    (failed : ε → Program β) (passed : α → Program β) (next : β → Program γ) :
    ((match observed with | .error error => failed error | .ok value => passed value) >>= next) =
      (match observed with | .error error => failed error >>= next | .ok value => passed value >>= next) := by
  cases observed <;> rfl

-- §FS-host-boundary.transport: Bounds and read provenance compose over the same effect sequence.
structure Progress (before after : State) (events : List Program.Event) : Prop where
  connection : ∀ fd, before.connection = some fd → after.connection = some fd
  source : StreamSource before.transport after.transport after.connection events
  bounded : before.Bounded → after.Bounded

theorem Progress.unchanged (before after : State) (events : List Program.Event)
    (transport : after.transport = before.transport)
    (boot : after.boot = before.boot) (diagnostic : after.diagnostic = before.diagnostic)
    (connection : ∀ fd, before.connection = some fd → after.connection = some fd) :
    Progress before after events := by
  refine ⟨connection, ?_, ?_⟩
  · rw [transport]
    exact stream_source_refl _ _ _
  · intro bound
    exact ⟨transport ▸ bound.1, by simpa only [boot] using bound.2.1,
      by simpa only [diagnostic] using bound.2.2⟩

theorem Progress.refl (state : State) (events : List Program.Event) : Progress state state events :=
  .unchanged state state events rfl rfl rfl (fun _ same => same)

theorem Progress.trans {first middle final : State} {before after : List Program.Event}
    (left : Progress first middle before) (right : Progress middle final after) :
    Progress first final (before ++ after) := by
  refine ⟨fun fd selected => right.connection fd (left.connection fd selected), ?_,
    fun bounded => right.bounded (left.bounded bounded)⟩
  obtain ⟨stream, shape, source⟩ := left.source
  exact stream_source_append ⟨stream, shape, read_subsequence_mono right.connection source⟩ right.source

theorem Progress.fail (state : State) (error : String) (events : List Program.Event) :
    Progress state (state.fail error) events :=
  .unchanged _ _ _ rfl rfl rfl (fun _ same => same)

theorem consume_progress (fd boot diagnostic : UInt64) (now : Nat) (state : State)
    {events : List Program.Event} {after : State}
    (selected : fd ≠ 3 → fd ≠ boot → fd ≠ diagnostic → state.connection = some fd)
    (run : Program.Returns (consume fd boot diagnostic now state) events after) :
    Progress state after events := by
  obtain ⟨connection, source, bound⟩ := consume_source fd boot diagnostic now state selected run
  refine ⟨fun _ known => connection.trans known, ?_, bound⟩
  simpa only [connection] using source

end LeanCage.Host.VirtualMachine
