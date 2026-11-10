import LeanCageHost.Packet
import SnapshotProofs.Effects

namespace LeanCage.Host.Packet
open Filesystem

-- §FS-host-boundary.caller: Exact packet parts retain every same-FD acknowledged native read.
inductive Parts (fd : UInt64) : ByteArray → List (Request × Reply) → ByteArray → Prop where
  | done (bytes : ByteArray) : Parts fd bytes [] bytes
  | more {before after : ByteArray} {request : Request} {reply : Reply}
      {events : List (Request × Reply)} (read : Snapshot.ReadRequest fd request)
      (acknowledged : Snapshot.ReadAcknowledged request reply)
      (nonempty : reply.2.isEmpty = false) (tail : Parts fd (before ++ reply.2) events after) :
      Parts fd before ((request, reply) :: events) after

private theorem count_exact (amount : Nat) : (min chunkMax amount).toUInt64.toNat = min chunkMax amount := by
  have bound : min chunkMax amount < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.min_le_left _ _) (by decide)
  simp only [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt bound]

theorem readExact_source (fuel : Nat) (fd : UInt64) (amount : Nat) (initial : ByteArray)
    {events : List (Request × Reply)} {bytes : ByteArray}
    (run : Returns (readExact fuel fd amount initial) events (.ok bytes)) :
    bytes.size = amount ∧ Parts fd initial events bytes := by
  induction fuel generalizing initial events with
  | zero => cases run
  | succ fuel ih =>
    unfold readExact at run
    split at run
    · cases run
    · rename_i bounded
      split at run
      · rename_i complete
        obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq run
        cases same
        exact ⟨by simpa using complete, .done _⟩
      · rename_i incomplete
        obtain ⟨reply, tail, rfl, continued⟩ := Snapshot.returns_call_split run
        split at continued
        · cases continued
        · rename_i native
          split at continued
          · cases continued
          · rename_i accepted
            split at continued
            · cases continued
            · rename_i nonempty
              obtain ⟨size, source⟩ := ih _ continued
              have fields : reply.1.toNat = reply.2.size ∧
                  reply.2.size ≤ min chunkMax (amount - initial.size) := by
                simpa [Bool.or_eq_true] using accepted
              have available : initial.size < amount := by
                have : initial.size ≠ amount := by simpa using incomplete
                omega
              refine ⟨size, .more ⟨rfl, rfl, ?_, ?_⟩
                ⟨Bool.eq_false_iff.mpr native, fields.1, ?_⟩
                (Bool.eq_false_iff.mpr nonempty) source⟩
              · rw [count_exact]
                apply Nat.le_min.mpr
                constructor
                · decide
                · omega
              · rw [count_exact]
                exact Nat.min_le_left _ _
              · simpa only [count_exact] using fields.2

theorem parts_bytes (fd : UInt64) {before after : ByteArray} {events : List (Request × Reply)}
    (parts : Parts fd before events after) : after = before ++ Snapshot.readPayloads events := by
  induction parts with
  | done bytes => simp [Snapshot.readPayloads]
  | more read acknowledged nonempty tail ih =>
    simpa only [Snapshot.readPayloads, List.foldr_cons, ByteArray.append_assoc] using ih

private theorem except_bind_ok {α β : Type} (first : Except String α)
    (next : α → Except String β) {answer : β} (run : Except.bind first next = .ok answer) :
    ∃ value, first = .ok value ∧ next value = .ok answer := by
  cases first with
  | error error => cases run
  | ok value => exact ⟨value, rfl, run⟩

-- §FS-host-boundary.caller: Length rejection precedes every payload allocation/read.
theorem payloadLength_bounded (header : ByteArray) (amount : Nat)
    (accepted : payloadLength header = .ok amount) :
    header.size = GatewayWire.requestHeader ∧ header.extract 0 8 = GatewayWire.requestMagic ∧
      amount ≤ GatewayWire.requestMax - GatewayWire.requestHeader := by
  unfold payloadLength at accepted
  split at accepted
  · change Except.error _ = Except.ok amount at accepted
    cases accepted
  · rename_i headerGood
    obtain ⟨total, _, final⟩ := except_bind_ok _ _ accepted
    dsimp only at final
    split at final
    · change Except.error _ = Except.ok amount at final
      cases final
    · rename_i bounded
      change Except.ok _ = Except.ok amount at final
      cases final
      have headerGood : header.size = GatewayWire.requestHeader ∧
          header.extract 0 8 = GatewayWire.requestMagic := by simpa [Bool.or_eq_true] using headerGood
      exact ⟨headerGood.1, headerGood.2, by omega⟩

-- §FS-host-boundary.caller: Accepted requests come from exact header/payload/EOF observations.
structure Observation (fd : UInt64) (events : List (Request × Reply)) (request : GatewayWire.Request) where
  header : ByteArray
  payload : ByteArray
  amount : Nat
  headerReads : List (Request × Reply)
  payloadReads : List (Request × Reply)
  eof : Reply
  headerSource : Parts fd .empty headerReads header
  headerSize : header.size = GatewayWire.requestHeader
  declared : payloadLength header = .ok amount
  payloadSource : Parts fd .empty payloadReads payload
  payloadSize : payload.size = amount
  eofCode : eof.1 = 0
  eofBytes : eof.2 = .empty
  decode : GatewayWire.decodeRequest (header ++ payload) = .ok request
  trace : events = headerReads ++ payloadReads ++ [({op := .read, first := fd, second := 1}, eof)]

theorem read_source (fd : UInt64) {events : List (Request × Reply)} {request : GatewayWire.Request}
    (run : Returns (Packet.read fd) events (.ok request)) : Nonempty (Observation fd events request) := by
  unfold Packet.read at run
  obtain ⟨headerReads, result, later, headerRun, afterHeader, headerShape⟩ := Snapshot.returns_bind_split _ _ run
  cases result with
  | error => cases afterHeader
  | ok header =>
    cases declared : payloadLength header with
    | error error => simp only [declared] at afterHeader; cases afterHeader
    | ok amount =>
      simp only [declared] at afterHeader
      obtain ⟨payloadReads, result, ending, payloadRun, afterPayload, payloadShape⟩ := Snapshot.returns_bind_split _ _ afterHeader
      cases result with
      | error => cases afterPayload
      | ok payload =>
        obtain ⟨eof, last, rfl, afterEof⟩ := Snapshot.returns_call_split afterPayload
        change Returns ((if eof.1 != 0 || !eof.2.isEmpty then
            Filesystem.Program.pure (Except.error ("trailing bytes or read failure after host request packet" : Failure))
          else match GatewayWire.decodeRequest (header ++ payload) with
            | .error error => Filesystem.Program.pure (Except.error (error : Failure))
            | .ok actual => Filesystem.Program.pure (Except.ok actual)) :
              Filesystem.Program (Filesystem.Result GatewayWire.Request)) last (Except.ok request) at afterEof
        split at afterEof
        · cases afterEof
        · rename_i eofGood
          cases decoded : GatewayWire.decodeRequest (header ++ payload) with
          | error error => simp only [decoded] at afterEof; cases afterEof
          | ok actual =>
            simp only [decoded] at afterEof
            obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq afterEof
            cases same
            obtain ⟨headerSize, headerSource⟩ := readExact_source _ _ _ _ headerRun
            obtain ⟨payloadSize, payloadSource⟩ := readExact_source _ _ _ _ payloadRun
            have eofFields : eof.1 = 0 ∧ eof.2.isEmpty = true := by simpa [Bool.or_eq_true] using eofGood
            refine ⟨⟨header, payload, amount, headerReads, payloadReads, eof, headerSource, headerSize,
              declared, payloadSource, payloadSize, eofFields.1, ?_, decoded, ?_⟩⟩
            · exact ByteArray.size_eq_zero_iff.mp
                (by simpa only [ByteArray.isEmpty, beq_iff_eq] using eofFields.2)
            · simp only [headerShape, payloadShape, List.append_assoc]

end LeanCage.Host.Packet
