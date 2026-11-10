import LeanCageHost.Snapshot
import BytesProofs

namespace LeanCage.Host.Snapshot

open Filesystem

instance byteArrayLawfulBEq : LawfulBEq ByteArray where
  eq_of_beq := by
    intro first second same
    apply ByteArray.ext
    change (first.data == second.data) = true at same
    exact eq_of_beq same
  rfl := by
    intro bytes
    change (bytes.data == bytes.data) = true
    simp

-- §AR-host-boundary.interfaces: Bind decomposition retains the same actual primitive transcript.
theorem returns_bind_split {α β : Type} (program : Program α) (next : α → Program β)
    {events : List (Request × Reply)} {answer : β}
    (run : Returns (program.bind next) events answer) :
    ∃ first value last, Returns program first value ∧ Returns (next value) last answer ∧
      events = first ++ last := by
  induction program generalizing events answer with
  | pure value =>
    exact ⟨[], value, events, .pure value, run, rfl⟩
  | call request rest ih =>
    change Returns (.call request (fun reply => (rest reply).bind next)) events answer at run
    cases run with
    | call _ _ reply tail answer run =>
      obtain ⟨first, value, last, initial, final, shape⟩ := ih reply run
      exact ⟨(request, reply) :: first, value, last,
        .call request rest reply first value initial, final, by simp only [shape, List.cons_append]⟩

theorem returns_bind_join {α β : Type} {program : Program α} {next : α → Program β}
    {first last : List (Request × Reply)} {value : α} {answer : β}
    (initial : Returns program first value) (final : Returns (next value) last answer) :
    Returns (program.bind next) (first ++ last) answer := by
  induction initial with
  | pure value => exact final
  | call request rest reply tail value initial ih =>
    exact .call request (fun reply => (rest reply).bind next) reply _ _ (ih final)

theorem returns_pure_eq {α : Type} {value answer : α} {events : List (Request × Reply)}
    (run : Returns (.pure value) events answer) : events = [] ∧ answer = value := by
  cases run
  exact ⟨rfl, rfl⟩

theorem returns_call_split {α : Type} {request : Request} {next : Reply → Program α}
    {events : List (Request × Reply)} {answer : α}
    (run : Returns (.call request next) events answer) :
    ∃ reply rest, events = (request, reply) :: rest ∧ Returns (next reply) rest answer := by
  cases run with
  | call _ _ reply tail answer run => exact ⟨reply, tail, rfl, run⟩

theorem prefix_pure_empty {α : Type} {value : α} {events : List (Request × Option Reply)}
    (run : Prefix (.pure value) events) : events = [] := by
  cases run
  rfl

inductive PostProgram {α : Type} (post : α → Prop) : Program α → Prop where
  | pure {value : α} (property : post value) : PostProgram post (.pure value)
  | call {request : Request} {next : Reply → Program α}
      (tail : ∀ reply, PostProgram post (next reply)) : PostProgram post (.call request next)

theorem post_bind {α β : Type} {firstPost : α → Prop} {lastPost : β → Prop}
    {program : Program α} {next : α → Program β} (first : PostProgram firstPost program)
    (tail : ∀ value, firstPost value → PostProgram lastPost (next value)) :
    PostProgram lastPost (program.bind next) := by
  induction first with
  | pure property => exact tail _ property
  | call rest ih => exact .call ih

theorem post_returns {α : Type} {post : α → Prop} {program : Program α}
    {events : List (Request × Reply)} {value : α}
    (verified : PostProgram post program) (run : Returns program events value) : post value := by
  induction run with
  | pure value => cases verified with | pure property => exact property
  | call request next reply tail value run ih =>
    cases verified with | call rest => exact ih (rest reply)

theorem post_of_returns {α : Type} (post : α → Prop) (program : Program α)
    (property : ∀ events value, Returns program events value → post value) : PostProgram post program := by
  induction program with
  | pure value => exact .pure (property [] value (.pure value))
  | call request rest ih =>
    apply PostProgram.call
    intro reply
    apply ih reply
    intro events value run
    exact property ((request, reply) :: events) value (.call request rest reply events value run)

theorem post_true {α : Type} (program : Program α) : PostProgram (fun _ => True) program :=
  post_of_returns _ program (fun _ _ _ => True.intro)

def ReadRequest (fd : UInt64) (request : Request) : Prop :=
  request.op = .read ∧ request.first = fd ∧ 1 ≤ request.second.toNat ∧
    request.second.toNat ≤ chunkMax

def ReadAcknowledged (request : Request) (reply : Reply) : Prop :=
  nativeError reply = false ∧ reply.1.toNat = reply.2.size ∧ reply.2.size ≤ request.second.toNat

-- §FS-host-boundary.snapshot: Content provenance is acknowledged reads followed by observed EOF.
inductive AcknowledgedReads (fd : UInt64) :
    ByteArray → List (Request × Reply) → ByteArray → Prop where
  | eof {before : ByteArray} {request : Request} {reply : Reply}
      (read : ReadRequest fd request) (ack : ReadAcknowledged request reply)
      (empty : reply.2 = .empty) : AcknowledgedReads fd before [(request, reply)] before
  | more {before after : ByteArray} {request : Request} {reply : Reply}
      {rest : List (Request × Reply)} (read : ReadRequest fd request)
      (ack : ReadAcknowledged request reply) (nonempty : reply.2 ≠ .empty)
      (tail : AcknowledgedReads fd (before ++ reply.2) rest after) :
      AcknowledgedReads fd before ((request, reply) :: rest) after

def readPayloads (events : List (Request × Reply)) : ByteArray :=
  events.foldr (fun event accumulated => event.2.2 ++ accumulated) .empty

theorem acknowledged_bytes {fd : UInt64} {before after : ByteArray} {events : List (Request × Reply)}
    (observed : AcknowledgedReads fd before events after) : after = before ++ readPayloads events := by
  induction observed with
  | eof read ack empty => simp [readPayloads, empty]
  | more read ack nonempty tail ih =>
    simpa only [readPayloads, List.foldr_cons, ByteArray.append_assoc] using ih

theorem acknowledged_calls {fd : UInt64} {before after : ByteArray} {events : List (Request × Reply)}
    (observed : AcknowledgedReads fd before events after) :
    ∀ event ∈ events, ReadRequest fd event.1 ∧ ReadAcknowledged event.1 event.2 := by
  induction observed with
  | eof read ack empty => simpa using And.intro read ack
  | more read ack nonempty tail ih =>
    intro event present
    simp only [List.mem_cons] at present
    rcases present with rfl | present
    · exact ⟨read, ack⟩
    · exact ih event present

end LeanCage.Host.Snapshot
