import ApplicationProofs

namespace LeanCage.Host.Program

theorem returns_prefix {α : Type} {program : Program α} {events : List Event} {value : α}
    (run : Returns program events value) : Prefix program events := by
  induction run with
  | pure => exact .empty _
  | call effect next reply tail value run ih => exact .returned effect next reply tail ih

theorem pure_prefix_empty {α : Type} (value : α) {events : List Event}
    (run : Prefix (.pure value) events) : events = [] := by
  cases run
  rfl

theorem pure_has_no_last {α : Type} (value : α) (before : List Event) (event : Event) :
    ¬ Prefix (.pure value) (before ++ [event]) := by
  intro run
  have empty := pure_prefix_empty value run
  have length := congrArg List.length empty
  simp only [List.length_append, List.length_singleton, List.length_nil] at length
  omega

-- §FS-host-boundary.acceptance: Preserve the exact selected last call when splitting a phase.
theorem last_bind_split {α β : Type} (program : Program α) (next : α → Program β)
    {before : List Event} {event : Event} (run : Prefix (program.bind next) (before ++ [event])) :
    Prefix program (before ++ [event]) ∨ ∃ initial value inside,
      Returns program initial value ∧ Prefix (next value) (inside ++ [event]) ∧ before = initial ++ inside := by
  rcases prefix_bind_split program next run with earlier | ⟨initial, value, last, returned, ending, shape⟩
  · exact .inl earlier
  · rcases List.eq_nil_or_concat last with empty | ⟨inside, final, lastShape⟩
    · subst last
      simp only [List.append_nil] at shape
      exact .inl (shape.symm ▸ returns_prefix returned)
    · rw [List.concat_eq_append] at lastShape
      subst last
      have concatenated : List.concat before event = List.concat (initial ++ inside) final := by
        simpa only [List.concat_eq_append, List.append_assoc] using shape
      have same := List.of_concat_eq_concat concatenated
      have finalSame := same.2
      subst final
      exact .inr ⟨initial, value, inside, returned, ending, same.1⟩

end LeanCage.Host.Program

namespace LeanCage.Host.ApplicationProofs

theorem lifted_prefix_source {α : Type} (program : Program α) {events : List Program.Event}
    (run : Program.Prefix (ExceptT.lift program : Checked α).run events) :
    Program.Prefix program events := by
  change Program.Prefix (Program.bind program
    (fun value => .pure (Except.ok value : Except Filesystem.Failure α))) events at run
  rcases Program.prefix_bind_split _ _ run with earlier | ⟨first, value, last, returned, ending, trace⟩
  · exact earlier
  · have empty := Program.pure_prefix_empty _ ending
    subst last
    rw [trace, List.append_nil]
    exact Program.returns_prefix returned

theorem duration_has_no_last (request : GatewayWire.Request) (policy : Policy.Accepted)
    (override : Option Nat) (before : List Program.Event) (event : Program.Event) :
    ¬ Program.Prefix (requestDuration request policy override).run (before ++ [event]) := by
  cases override with
  | none => exact Program.pure_has_no_last _ _ _
  | some duration =>
    dsimp only [requestDuration]
    split <;> exact Program.pure_has_no_last _ _ _

theorem checked_has_no_last {α : Type} (value : Except String α)
    (before : List Program.Event) (event : Program.Event) :
    ¬ Program.Prefix (checked value).run (before ++ [event]) :=
  Program.pure_has_no_last _ _ _

-- §FS-host-boundary.acceptance: An error cannot run the next phase, even in an interrupted call.
theorem last_checked_bind {α β : Type} (program : Checked α) (next : α → Checked β)
    {before : List Program.Event} {event : Program.Event}
    (run : Program.Prefix (program >>= next).run (before ++ [event])) :
    Program.Prefix program.run (before ++ [event]) ∨ ∃ initial value inside,
      Run program initial value ∧ Program.Prefix (next value).run (inside ++ [event]) ∧
        before = initial ++ inside := by
  change Program.Prefix (Program.bind program.run (ExceptT.bindCont next)) (before ++ [event]) at run
  rcases Program.last_bind_split _ _ run with earlier | ⟨initial, result, inside, returned, ending, shape⟩
  · exact .inl earlier
  · cases result with
    | error error => exact False.elim (Program.pure_has_no_last _ _ _ ending)
    | ok value => exact .inr ⟨initial, value, inside, returned, ending, shape⟩

end LeanCage.Host.ApplicationProofs
