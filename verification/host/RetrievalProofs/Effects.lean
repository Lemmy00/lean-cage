import LeanCageHost.Retrieval
import SnapshotProofs
import ArtifactsProofs.Effects

namespace LeanCage.Host.Retrieval

open Filesystem

-- §FS-host-boundary.publication: Retrieval has no host content or namespace mutation operation.
def Allowed (request : Request) : Prop :=
  match request.op with
  | .openAt => request.second = readFlags ∨ request.second = directoryFlags
  | .read => 1 ≤ request.second.toNat ∧ request.second.toNat ≤ chunkMax
  | .getAttribute => request.second.toNat ≤ 40
  | .close | .stat | .dirOpen | .dirNext | .dirClose | .sha256 | .euid
    | .workingDirectory | .directoryIdentity | .authenticate | .equalSecret => True
  | _ => False

inductive ReadOnly {α : Type} : Filesystem.Program α → Prop where
  | pure (value : α) : ReadOnly (.pure value)
  | call {request : Request} {next : Reply → Filesystem.Program α}
      (allowed : Allowed request) (tail : ∀ reply, ReadOnly (next reply)) :
      ReadOnly (.call request next)

theorem readOnly_bind {α β : Type} {program : Filesystem.Program α} {next : α → Filesystem.Program β}
    (first : ReadOnly program) (tail : ∀ value, ReadOnly (next value)) :
    ReadOnly (program.bind next) := by
  induction first with
  | pure => exact tail _
  | call allowed rest ih => exact .call allowed ih

theorem readOnly_prefix {α : Type} {program : Filesystem.Program α} {events : List (Request × Option Reply)}
    (verified : ReadOnly program) (run : Prefix program events) :
    ∀ event ∈ events, Allowed event.1 := by
  induction run with
  | empty => simp
  | lost request next =>
    cases verified with
    | call allowed => simpa using allowed
  | returned request next reply events run ih =>
    cases verified with
    | call allowed tail =>
      intro event member
      rcases List.mem_cons.mp member with rfl | member
      · exact allowed
      · exact ih (tail reply) event member

theorem readOnly_snapshot {α : Type} {program : Filesystem.Program α} (verified : Snapshot.InputProgram program) :
    ReadOnly program := by
  induction verified with
  | pure => exact .pure _
  | @call request next allowed rest ih =>
    apply ReadOnly.call _ ih
    cases operation : request.op <;> simp_all [Snapshot.InputRequest, Allowed]

theorem readOnly_hashOnly {α : Type} {program : Filesystem.Program α} (verified : Artifacts.HashOnly program) :
    ReadOnly program := by
  induction verified with
  | pure => exact .pure _
  | call hash rest ih => exact .call (by simp only [Allowed, hash]) ih

theorem checked_bind_split {α β : Type} {program : Checked α} {next : α → Checked β}
    {events : List (Request × Reply)} {answer : β}
    (run : Returns ((program.bind next).run) events (.ok answer)) :
    ∃ first value last, Returns program.run first (.ok value) ∧
      Returns (next value).run last (.ok answer) ∧ events = first ++ last := by
  simp only [ExceptT.bind, ExceptT.run, ExceptT.mk] at run
  obtain ⟨first, result, last, initial, final, shape⟩ := Snapshot.returns_bind_split _ _ run
  cases result with
  | error error => cases final
  | ok value => exact ⟨first, value, last, initial, final, shape⟩

theorem checked_result {α : Type} (result : Result α) {events : List (Request × Reply)} {answer : α}
    (run : Returns (checked result).run events (.ok answer)) : events = [] ∧ result = .ok answer := by
  obtain ⟨empty, value⟩ := Snapshot.returns_pure_eq run
  exact ⟨empty, value.symm⟩

theorem except_guard_next {ε α : Type} {condition : Bool} {error : ε}
    {next : Unit → Except ε α} {answer : α}
    (accepted : (if condition then (Except.error error).bind next else next ()) = .ok answer) :
    condition = false ∧ next () = .ok answer := by
  cases condition with
  | false => exact ⟨rfl, accepted⟩
  | true => cases accepted

theorem readOnly_checked_bind {α β : Type} {program : Checked α} {next : α → Checked β}
    (first : ReadOnly program.run) (tail : ∀ value, ReadOnly (next value).run) :
    ReadOnly ((program.bind next).run) := by
  simp only [ExceptT.bind, ExceptT.run, ExceptT.mk]
  apply readOnly_bind first
  intro result
  cases result with
  | error => exact .pure _
  | ok value => exact tail value

end LeanCage.Host.Retrieval
