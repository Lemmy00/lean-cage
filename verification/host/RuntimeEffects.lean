import PrefixOrigins

namespace LeanCage.Host

def Effect.NonFilesystem {α : Type} : Effect α → Prop
  | .filesystem _ => False
  | _ => True

def Program.Event.NonFilesystem : Program.Event → Prop
  | .returned effect _ => effect.NonFilesystem
  | .lost effect => effect.NonFilesystem

inductive Program.RuntimeOnly {α : Type} : Program α → Prop where
  | pure (value : α) : RuntimeOnly (.pure value)
  | call {β : Type} (effect : Effect β) (next : β → Program α)
      (allowed : effect.NonFilesystem) (rest : ∀ reply, RuntimeOnly (next reply)) :
      RuntimeOnly (.call effect next)

theorem Program.RuntimeOnly.bind {α β : Type} {program : Program α} {next : α → Program β}
    (initial : RuntimeOnly program) (later : ∀ value, RuntimeOnly (next value)) :
    RuntimeOnly (program.bind next) := by
  induction initial with
  | pure => exact later _
  | call effect rest allowed all ih => exact .call effect _ allowed ih

-- §AR-host-boundary.primitives: Each selected event retains its individual runtime effect.
theorem Program.runtime_only_prefix {α : Type} {program : Program α} {events : List Event}
    (scope : RuntimeOnly program) (active : Prefix program events) :
    ∀ event ∈ events, event.NonFilesystem := by
  induction active with
  | empty => simp
  | returned effect next reply tail rest ih =>
    cases scope with
    | call _ _ allowed after =>
      intro event member
      rcases List.mem_cons.mp member with rfl | later
      · exact allowed
      · exact ih (after reply) event later
  | lost effect next =>
    cases scope with
    | call _ _ allowed after =>
      intro event member
      have same : event = .lost effect := List.mem_singleton.mp member
      cases same
      exact allowed

-- §FS-host-boundary.caller: Bounded validator reads cannot issue a filesystem mutation.
theorem read_stream_runtime_only (fuel : Nat) (handle : IO.FS.Handle) (limit : Nat) (bytes : ByteArray) :
    Program.RuntimeOnly (readStream fuel handle limit bytes) := by
  induction fuel generalizing limit bytes with
  | zero => exact .pure _
  | succ fuel ih =>
    unfold readStream
    split
    · exact .pure _
    · apply Program.RuntimeOnly.call (.read handle (min chunkMax (limit + 1 - bytes.size))) _ (by simp only [Effect.NonFilesystem])
      intro reply
      cases reply with
      | error error => exact .pure _
      | ok part =>
        repeat' first | exact .pure _ | exact ih _ _ | split


-- §FS-host-boundary.caller: The actual validator collection uses only its owned runtime stream.
theorem observe_child_runtime_only (raw : ByteArray)
    (child : Except String Validation.ValidatorChild) :
    Program.RuntimeOnly (Validation.observeChild raw child) := by
  cases child with
  | error error => exact .pure _
  | ok child =>
    unfold Validation.observeChild
    apply Program.RuntimeOnly.bind (read_stream_runtime_only _ _ _ _)
    intro output
    apply Program.RuntimeOnly.bind (.call (.wait child) _ trivial (fun _ => .pure _))
    intro code
    exact .pure _

theorem validation_child_runtime_only (raw : ByteArray)
    (child : Except String Validation.ValidatorChild) :
    Program.RuntimeOnly (Validation.validationChild raw child) := by
  unfold Validation.validationChild
  exact Program.RuntimeOnly.bind (observe_child_runtime_only raw child) (fun _ => .pure _)


end LeanCage.Host
