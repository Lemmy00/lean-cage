import LeanCageHost.Program

namespace LeanCage.Host.Program

-- §AR-host-boundary.interfaces: Trace events retain the actual dependent effect and its reply.
inductive Event : Type 1 where
  | returned {β : Type} (effect : Effect β) (value : β)
  | lost {β : Type} (effect : Effect β)

inductive Returns {α : Type} : Program α → List Event → α → Prop where
  | pure (value : α) : Returns (.pure value) [] value
  | call {β : Type} (effect : Effect β) (next : β → Program α) (reply : β)
      (tail : List Event) (value : α) (rest : Returns (next reply) tail value) :
      Returns (.call effect next) (.returned effect reply :: tail) value

-- §FS-host-boundary.acceptance: A prefix may stop or lose the final effect after any earlier reply.
inductive Prefix {α : Type} : Program α → List Event → Prop where
  | empty (program : Program α) : Prefix program []
  | returned {β : Type} (effect : Effect β) (next : β → Program α) (reply : β)
      (tail : List Event) (rest : Prefix (next reply) tail) :
      Prefix (.call effect next) (.returned effect reply :: tail)
  | lost {β : Type} (effect : Effect β) (next : β → Program α) :
      Prefix (.call effect next) [.lost effect]

def filesystemEvent (event : Filesystem.Request × Filesystem.Reply) : Event :=
  .returned (.filesystem event.1) event.2

def filesystemPrefixEvent (event : Filesystem.Request × Option Filesystem.Reply) : Event :=
  match event.2 with
  | none => .lost (.filesystem event.1)
  | some reply => .returned (.filesystem event.1) reply

theorem returns_pure {α : Type} (value : α) {events : List Event} {result : α}
    (run : Returns (.pure value) events result) : events = [] ∧ result = value := by
  cases run
  exact ⟨rfl, rfl⟩

theorem returns_bind_split {α β : Type} (program : Program α) (next : α → Program β)
    {events : List Event} {result : β} (run : Returns (program.bind next) events result) :
    ∃ first value last, Returns program first value ∧ Returns (next value) last result ∧
      events = first ++ last := by
  induction program generalizing events with
  | pure value => exact ⟨[], value, events, .pure value, run, rfl⟩
  | @call γ effect rest ih =>
    change Returns (.call effect (fun reply => (rest reply).bind next)) events result at run
    cases run with
    | call _ _ reply tail _ after =>
      obtain ⟨first, value, last, before, final, shape⟩ := ih reply after
      exact ⟨.returned effect reply :: first, value, last,
        .call effect rest reply first value before, final, by simp [shape]⟩

theorem returns_bind {α β : Type} {program : Program α} {next : α → Program β}
    {first last : List Event} {value : α} {result : β}
    (before : Returns program first value) (after : Returns (next value) last result) :
    Returns (program.bind next) (first ++ last) result := by
  induction before with
  | pure => exact after
  | call effect rest reply tail value before ih =>
    exact .call effect (fun reply => (rest reply).bind next) reply _ _ (ih after)

-- §FS-host-boundary.acceptance: An interrupted continuation still names its actual active phase.
theorem prefix_bind_split {α β : Type} (program : Program α) (next : α → Program β)
    {events : List Event} (run : Prefix (program.bind next) events) :
    Prefix program events ∨ ∃ first value last,
      Returns program first value ∧ Prefix (next value) last ∧ events = first ++ last := by
  induction program generalizing events with
  | pure value => exact .inr ⟨[], value, events, .pure value, run, rfl⟩
  | @call γ effect continuation ih =>
    cases run with
    | empty => exact .inl (.empty _)
    | lost => exact .inl (.lost _ _)
    | returned _ _ reply tail rest =>
      rcases ih reply rest with earlier | ⟨first, value, last, returned, remaining, shape⟩
      · exact .inl (.returned effect continuation reply tail earlier)
      · exact .inr ⟨.returned effect reply :: first, value, last,
          .call effect continuation reply first value returned, remaining, by simp [shape]⟩

-- §AR-host-boundary.interfaces: The live filesystem interpreter keeps each original request/reply.
theorem lift_filesystem_returns {α : Type} {program : Filesystem.Program α}
    {events : List (Filesystem.Request × Filesystem.Reply)} {value : α}
    (run : Filesystem.Returns program events value) :
    Returns (Program.liftFilesystem program) (events.map filesystemEvent) value := by
  induction run with
  | pure value => exact .pure value
  | call request next reply tail value before ih =>
    exact .call (.filesystem request) (fun reply => Program.liftFilesystem (next reply))
      reply _ value ih

theorem lift_filesystem_source {α : Type} (program : Filesystem.Program α)
    {events : List Event} {value : α}
    (run : Returns (Program.liftFilesystem program) events value) :
    ∃ source, Filesystem.Returns program source value ∧ events = source.map filesystemEvent := by
  induction program generalizing events with
  | pure result =>
    obtain ⟨rfl, rfl⟩ := returns_pure _ run
    exact ⟨[], .pure value, rfl⟩
  | call request next ih =>
    change Returns (.call (.filesystem request) (fun reply => Program.liftFilesystem (next reply)))
      events value at run
    cases run with
    | call _ _ reply tail _ after =>
      obtain ⟨source, origin, shape⟩ := ih reply after
      exact ⟨(request, reply) :: source, .call request next reply source value origin,
        by simp [shape, filesystemEvent]⟩

theorem lift_filesystem_prefix {α : Type} {program : Filesystem.Program α}
    {events : List (Filesystem.Request × Option Filesystem.Reply)}
    (run : Filesystem.Prefix program events) :
    Prefix (Program.liftFilesystem program) (events.map filesystemPrefixEvent) := by
  induction run with
  | empty program => exact .empty _
  | returned request next reply tail before ih =>
    exact .returned (.filesystem request) (fun reply => Program.liftFilesystem (next reply)) reply _ ih
  | lost request next =>
    exact .lost (.filesystem request) (fun reply => Program.liftFilesystem (next reply))

-- §AR-host-boundary.interfaces: Lost filesystem calls keep the same real request projection.
theorem lift_filesystem_prefix_source {α : Type} (program : Filesystem.Program α)
    {events : List Event} (run : Prefix (Program.liftFilesystem program) events) :
    ∃ source, Filesystem.Prefix program source ∧ events = source.map filesystemPrefixEvent := by
  induction program generalizing events with
  | pure value =>
    cases run
    exact ⟨[], .empty _, rfl⟩
  | call request next ih =>
    cases run with
    | empty => exact ⟨[], .empty _, rfl⟩
    | lost => exact ⟨[(request, none)], .lost request next, rfl⟩
    | returned _ _ reply tail rest =>
      obtain ⟨source, before, shape⟩ := ih reply rest
      exact ⟨(request, some reply) :: source, .returned request next reply source before,
        by simp [shape, filesystemPrefixEvent]⟩

-- §AR-host-boundary.interfaces: Connect the ordinary program to its live interpreter.
theorem interpret_pure {α : Type} (value : α) :
    Program.interpret (.pure value) = (Pure.pure value : IO α) := rfl

theorem interpret_call {α β : Type} (effect : Effect β) (next : β → Program α) :
    Program.interpret (.call effect next) = (do
      let reply ← Effect.interpret effect
      Program.interpret (next reply)) := rfl

end LeanCage.Host.Program
