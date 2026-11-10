import PublicationProofs.Effects

namespace LeanCage.Host.Publication

open Filesystem

-- §AR-host-boundary.interfaces: These adapters inspect the actual executable list for-loop.
theorem forIn_safe {α β : Type} (items : List α) (initial : β)
    (body : α → β → Filesystem.Program (ForInStep β))
    (allowed : ∀ item state, SafeProgram (body item state)) :
    SafeProgram (forIn items initial body) := by
  induction items generalizing initial with
  | nil => exact .pure _
  | cons item rest ih =>
    rw [List.forIn_cons]
    apply safe_bind (allowed _ _)
    intro step
    cases step with
    | done => exact .pure _
    | yield state => exact ih state

inductive ForInTrace {α β : Type} (body : α → β → Filesystem.Program (ForInStep β)) :
    List α → β → List (Request × Reply) → β → Prop where
  | empty (state : β) : ForInTrace body [] state [] state
  | done (item : α) (rest : List α) (before after : β) (events : List (Request × Reply))
      (step : Returns (body item before) events (.done after)) :
      ForInTrace body (item :: rest) before events after
  | yield (item : α) (rest : List α) (before middle after : β)
      (first last : List (Request × Reply))
      (step : Returns (body item before) first (.yield middle))
      (tail : ForInTrace body rest middle last after) :
      ForInTrace body (item :: rest) before (first ++ last) after

theorem forIn_source {α β : Type} (items : List α) (initial : β)
    (body : α → β → Filesystem.Program (ForInStep β))
    {events : List (Request × Reply)} {result : β}
    (run : Returns (forIn items initial body) events result) :
    ForInTrace body items initial events result := by
  induction items generalizing initial events with
  | nil =>
    obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq run
    cases same
    exact .empty _
  | cons item rest ih =>
    rw [List.forIn_cons] at run
    obtain ⟨first, step, last, called, final, shape⟩ := Snapshot.returns_bind_split _ _ run
    cases step with
    | done result =>
      obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq final
      cases same
      simpa only [shape, List.append_nil] using ForInTrace.done item rest initial result first called
    | yield middle =>
      simpa only [shape] using ForInTrace.yield item rest initial middle result first last called (ih _ final)

end LeanCage.Host.Publication

namespace LeanCage.Host.Publication
open Filesystem

def actionBody {α : Type} (action : α → Filesystem.Program (Result Unit)) (item : α)
    (_state : Option (Result Unit) × Unit) : Filesystem.Program (ForInStep (Option (Result Unit) × Unit)) := do
  let result ← action item
  match result with
  | .error error => pure (.done (some (.error error), ()))
  | _ => pure (.yield (none, ()))

inductive ActionTrace {α : Type} (action : α → Filesystem.Program (Result Unit)) :
    List α → List (Request × Reply) → Prop where
  | empty : ActionTrace action [] []
  | next (item : α) (rest : List α) (first last : List (Request × Reply))
      (called : Returns (action item) first (.ok ())) (tail : ActionTrace action rest last) :
      ActionTrace action (item :: rest) (first ++ last)

private theorem actionLoop_cases {α : Type} (action : α → Filesystem.Program (Result Unit))
    {items : List α} {before after : Option (Result Unit) × Unit} {events : List (Request × Reply)}
    (run : ForInTrace (actionBody action) items before events after) (initial : before.1 = none) :
    (after.1 = none ∧ ActionTrace action items events) ∨ ∃ error, after.1 = some (.error error) := by
  induction run with
  | empty state => exact .inl ⟨initial, .empty⟩
  | done item rest before after events step =>
    unfold actionBody at step
    obtain ⟨first, result, last, called, final, shape⟩ := Snapshot.returns_bind_split _ _ step
    cases result with
    | error error =>
      obtain ⟨_, same⟩ := Snapshot.returns_pure_eq final
      cases same
      exact .inr ⟨error, rfl⟩
    | ok => cases final
  | yield item rest before middle after first last step tail ih =>
    unfold actionBody at step
    obtain ⟨writing, result, finalEvents, called, final, shape⟩ := Snapshot.returns_bind_split _ _ step
    cases result with
    | error => cases final
    | ok value =>
      cases value
      obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq final
      cases same
      rcases ih rfl with success | error
      · exact .inl ⟨success.1, by simpa only [shape, List.append_nil] using
          (ActionTrace.next item rest writing last called success.2)⟩
      · exact .inr error

def checkedActions {α : Type} (action : α → Filesystem.Program (Result Unit)) (items : List α)
    (next : Filesystem.Program (Result Unit)) : Filesystem.Program (Result Unit) := do
  for item in items do
    let result ← action item
    if let .error error := result then return .error error
  next

-- §AR-host-boundary.interfaces: Successful loop completion retains every actual item call in order.
theorem checkedActions_source {α : Type} (action : α → Filesystem.Program (Result Unit)) (items : List α)
    (next : Filesystem.Program (Result Unit)) {events : List (Request × Reply)}
    (run : Returns (checkedActions action items next) events (.ok ())) :
    ∃ first last, events = first ++ last ∧ ActionTrace action items first ∧ Returns next last (.ok ()) := by
  unfold checkedActions at run
  obtain ⟨first, state, last, loopRun, final, shape⟩ := Snapshot.returns_bind_split _ _ run
  have traced := forIn_source _ _ _ loopRun
  rcases actionLoop_cases action traced rfl with success | error
  · dsimp only at final
    simp only [success.1] at final
    exact ⟨first, last, shape, success.2, final⟩
  · obtain ⟨error, failed⟩ := error
    dsimp only at final
    simp only [failed] at final
    cases final

theorem actionTrace_member {α : Type} {action : α → Filesystem.Program (Result Unit)}
    {items : List α} {events : List (Request × Reply)} (observed : ActionTrace action items events) :
    ∀ item ∈ items, ∃ selected, Returns (action item) selected (.ok ()) ∧
      ∀ event ∈ selected, event ∈ events := by
  induction observed with
  | empty => simp
  | next item rest first last called tail ih =>
    intro selected member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨first, called, by intro event member; simp [member]⟩
    · obtain ⟨following, called, included⟩ := ih selected member
      exact ⟨following, called, by intro event member; simp [included event member]⟩

end LeanCage.Host.Publication
