import EntrypointPrefixCuts
import FilesystemPrimitiveRecording
import FilesystemPrimitiveObservations

namespace LeanCage.Host.EntrypointWriterPrefix
open Filesystem

-- §FS-host-boundary.caller: A prefix retains only genuinely acknowledged earlier progress;
-- the selected next write may fail or lose its reply and need not finish the response.
inductive AcknowledgedPrefix (fd : UInt64) (bytes : ByteArray) :
    Nat → List (Request × Reply) → Nat → Prop where
  | nil (offset : Nat) : AcknowledgedPrefix fd bytes offset [] offset
  | more (offset : Nat) (reply : Reply) (events : List (Request × Reply)) (final : Nat)
      (inside : offset < bytes.size) (native : nativeError reply = false)
      (empty : reply.2 = .empty) (positive : 0 < reply.1.toNat)
      (bounded : reply.1.toNat ≤ (bytes.extract offset (min bytes.size (offset + chunkMax))).size)
      (tail : AcknowledgedPrefix fd bytes (offset + reply.1.toNat) events final) :
      AcknowledgedPrefix fd bytes offset
        (({op := .write, first := fd, left := bytes.extract offset (min bytes.size (offset + chunkMax))}, reply) :: events) final

def acknowledgedBytes : List (Request × Reply) → ByteArray
  | [] => .empty
  | (request, reply) :: rest => request.left.extract 0 reply.1.toNat ++ acknowledgedBytes rest

theorem AcknowledgedPrefix.monotone {fd : UInt64} {bytes : ByteArray} {offset final : Nat}
    {events : List (Request × Reply)} (source : AcknowledgedPrefix fd bytes offset events final) : offset ≤ final := by
  induction source with
  | nil => exact Nat.le_refl _
  | more offset reply events final inside native empty positive bounded tail ih => omega

-- §FS-host-boundary.caller: Concatenating actual acknowledged payload prefixes gives
-- exactly the corresponding response prefix, without a successful final write assumption.
theorem AcknowledgedPrefix.bytes {fd : UInt64} {bytes : ByteArray} {offset final : Nat}
    {events : List (Request × Reply)} (source : AcknowledgedPrefix fd bytes offset events final) :
    acknowledgedBytes events = bytes.extract offset final := by
  induction source with
  | nil => exact ByteArray.extract_same.symm
  | more offset reply events final inside native empty positive bounded tail ih =>
    have extent := bounded
    rw [ByteArray.size_extract] at extent
    have upper : offset + reply.1.toNat ≤ min bytes.size (offset + chunkMax) := by omega
    change (bytes.extract offset (min bytes.size (offset + chunkMax))).extract 0 reply.1.toNat ++
      acknowledgedBytes events = bytes.extract offset final
    rw [ByteArray.extract_extract, Nat.add_zero, Nat.min_eq_left upper, ih, ByteArray.extract_append_extract,
      Nat.min_eq_left (by omega), Nat.max_eq_right tail.monotone]

structure WriteFrontier (fd : UInt64) (bytes : ByteArray) (initial : Nat)
    (before : List (Request × Option Reply)) (request : Request) where
  offset : Nat
  acknowledged : List (Request × Reply)
  trace : before = Publication.completed acknowledged
  progress : AcknowledgedPrefix fd bytes initial acknowledged offset
  inside : offset < bytes.size
  operation : request = {
    op := .write
    first := fd
    left := bytes.extract offset (min bytes.size (offset + chunkMax)) }

private theorem pure_no_last {α : Type} (value : α) {before : List (Request × Option Reply)}
    {event : Request × Option Reply} (source : Prefix (.pure value) (before ++ [event])) : False := by
  have length := congrArg List.length (Snapshot.prefix_pure_empty source)
  simp only [List.length_append, List.length_singleton, List.length_nil] at length
  omega

private theorem call_cases {α : Type} {operation : Request} {next : Reply → Filesystem.Program α}
    {events : List (Request × Option Reply)} (source : Prefix (.call operation next) events) :
    events = [] ∨ events = [(operation, none)] ∨
      ∃ reply tail, events = (operation, some reply) :: tail ∧ Prefix (next reply) tail := by
  cases source with
  | empty => exact .inl rfl
  | lost => exact .inr (.inl rfl)
  | returned _ _ reply tail continued => exact .inr (.inr ⟨reply, tail, rfl, continued⟩)

theorem write_loop_frontier (fuel : Nat) (fd : UInt64) (bytes : ByteArray) (offset : Nat)
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix (writeLoop fuel fd bytes offset) (before ++ [(request, observed)])) :
    Nonempty (WriteFrontier fd bytes offset before request) := by
  induction fuel generalizing offset before with
  | zero => exact False.elim (pure_no_last _ source)
  | succ fuel ih =>
    unfold writeLoop at source
    split at source
    · exact False.elim (pure_no_last _ source)
    · rename_i remaining
      cases before with
      | nil =>
        rcases call_cases source with empty | lost | ⟨reply, tail, shape, _⟩
        · cases empty
        · have exactRequest := congrArg Prod.fst (List.cons.inj lost).1
          exact ⟨⟨offset, [], rfl, .nil offset, by omega, exactRequest⟩⟩
        · have exactRequest := congrArg Prod.fst (List.cons.inj shape).1
          exact ⟨⟨offset, [], rfl, .nil offset, by omega, exactRequest⟩⟩
      | cons head rest =>
        change Prefix (.call _ _) (head :: (rest ++ [(request, observed)])) at source
        rcases call_cases source with empty | lost | ⟨reply, tail, shape, continued⟩
        · cases empty
        · have impossible := congrArg List.length lost
          simp only [List.length_cons, List.length_append] at impossible
          omega
        · obtain ⟨rfl, tailShape⟩ := List.cons.inj shape
          rw [← tailShape] at continued
          split at continued
          · exact False.elim (pure_no_last _ continued)
          · rename_i native
            split at continued
            · exact False.elim (pure_no_last _ continued)
            · rename_i valid
              obtain ⟨frontier⟩ := ih _ continued
              have fields : reply.2.isEmpty = true ∧ reply.1 ≠ 0 ∧
                  reply.1.toNat ≤ (bytes.extract offset (min bytes.size (offset + chunkMax))).size := by
                simpa [Bool.or_eq_true, and_assoc] using valid
              have empty : reply.2 = .empty := ByteArray.size_eq_zero_iff.mp
                (by simpa only [ByteArray.isEmpty, beq_iff_eq] using fields.1)
              have positive : 0 < reply.1.toNat := by
                have nonzero : reply.1.toNat ≠ 0 := by
                  intro zero
                  exact fields.2.1 (UInt64.toNat_inj.mp (by simpa using zero))
                omega
              exact ⟨⟨frontier.offset,
                ({op := .write, first := fd, left := bytes.extract offset (min bytes.size (offset + chunkMax))}, reply) ::
                  frontier.acknowledged,
                by simp only [frontier.trace, Publication.completed, List.map_cons],
                .more offset reply _ _ (by omega) (Bool.eq_false_iff.mpr native) empty positive fields.2.2 frontier.progress,
                frontier.inside, frontier.operation⟩⟩

structure ResponseFrontier (before : List Program.Event) (request : Request) (observed : Option Reply) where
  context : EntrypointPrefixCuts.Responded
  bounded : context.bytes.size ≤ GatewayWire.responseMax
  inside : List (Request × Option Reply)
  active : Prefix (writeLoop (context.bytes.size + 1) 1 context.bytes 0) (inside ++ [(request, observed)])
  trace : before = context.events ++ inside.map Program.filesystemPrefixEvent
  writer : WriteFrontier 1 context.bytes 0 inside request

private theorem seal_no_write (descriptors : List UInt64) :
    RequestProgram (fun request => request.op ≠ .write) (Startup.sealDescriptors descriptors) := by
  induction descriptors with
  | nil => exact .pure _
  | cons fd rest ih =>
    unfold Startup.sealDescriptors
    apply RequestProgram.call (by intro wrong; cases wrong)
    intro reply
    split
    · exact .pure _
    · exact ih

private theorem packet_exact_no_write (fuel : Nat) (fd : UInt64) (amount : Nat) (bytes : ByteArray) :
    RequestProgram (fun request => request.op ≠ .write) (Packet.readExact fuel fd amount bytes) := by
  induction fuel generalizing bytes with
  | zero => exact .pure _
  | succ fuel ih =>
    unfold Packet.readExact
    repeat' first
      | exact .pure _
      | split
      | exact ih _
      | apply RequestProgram.call (by intro wrong; cases wrong); intro reply

private theorem packet_no_write (fd : UInt64) :
    RequestProgram (fun request => request.op ≠ .write) (Packet.read fd) := by
  unfold Packet.read
  apply request_bind (packet_exact_no_write _ _ _ _)
  intro header
  cases header with
  | error => exact .pure _
  | ok header =>
    dsimp only
    split
    · exact .pure _
    · apply request_bind (packet_exact_no_write _ _ _ _)
      intro payload
      cases payload with
      | error => exact .pure _
      | ok payload =>
        dsimp only
        apply RequestProgram.call (by intro wrong; cases wrong)
        intro reply
        dsimp only [Filesystem.Program.bind]
        repeat' first | exact .pure _ | split

-- §FS-host-boundary.caller: The total cut does not infer source authority from integer1.
-- Actual IPC-object custody/freshness must exclude application file writes on that endpoint.
inductive Cut (before : List Program.Event) (request : Request) (observed : Option Reply) : Type 1 where
  | application (context : EntrypointPrefixCuts.Read) (input : GatewayWire.Request)
      (packet : context.packet = .ok input) (inside : List Program.Event)
      (active : Program.Prefix (Commands.run input) (inside ++ [Program.filesystemPrefixEvent (request, observed)]))
      (trace : before = context.events ++ inside)
  | response (frontier : ResponseFrontier before request observed)

-- §FS-host-boundary.caller: Every selected source write is in actual dispatch or the final
-- response writer. No engine return, successful final write or complete packet is required.
theorem write_cut {before : List Program.Event} {request : Request} {observed : Option Reply}
    (source : Program.Prefix Entrypoint.run (before ++ [Program.filesystemPrefixEvent (request, observed)]))
    (writing : request.op = .write) : Nonempty (Cut before request observed) := by
  obtain ⟨cut⟩ := EntrypointPrefixCuts.entrypoint_cut source
  cases cut with
  | starting active =>
    exact False.elim (Kernel.selected_filesystem_profile (seal_no_write [0, 1, 3]) active writing)
  | reading context inside active trace =>
    exact False.elim (Kernel.selected_filesystem_profile (packet_no_write 0) active writing)
  | responding context inside active trace =>
    obtain ⟨input, packet, application⟩ := EntrypointPrefixCuts.packet_response_prefix active
    exact ⟨.application context input packet inside application trace⟩
  | writing context inside bound active trace =>
    obtain ⟨events, writer, projected⟩ := Kernel.selected_filesystem_source active
    obtain ⟨frontier⟩ := write_loop_frontier _ _ _ _ writer
    exact ⟨.response ⟨context, bound, events, writer, trace.trans (congrArg (context.events ++ ·) projected), frontier⟩⟩

theorem ResponseFrontier.payload {before : List Program.Event} {request : Request} {observed : Option Reply}
    (source : ResponseFrontier before request observed) :
    request.first = 1 ∧ request.op = .write ∧
      request.left = source.context.bytes.extract source.writer.offset
        (min source.context.bytes.size (source.writer.offset + chunkMax)) ∧
      1 ≤ request.left.size ∧ request.left.size ≤ chunkMax ∧
      acknowledgedBytes source.writer.acknowledged = source.context.bytes.extract 0 source.writer.offset := by
  have bounds := Publication.write_part_bounds source.context.bytes source.writer.offset source.writer.inside
  have exactBytes := source.writer.progress.bytes
  refine ⟨congrArg Request.first source.writer.operation, congrArg Request.op source.writer.operation,
    congrArg Request.left source.writer.operation, ?_, ?_, exactBytes⟩
  · simpa only [source.writer.operation] using bounds.1
  · simpa only [source.writer.operation] using bounds.2

private theorem write_adapter (request : Request) (writing : request.op = .write) :
    guardedCall request = .call request .pure := by
  rcases request with ⟨operation, first, second, third, left, right⟩
  cases writing
  rfl

-- §AR-host-boundary.primitives: A raw write has the same selected source request; it has
-- no lookup probes, and its actual returned or lost acknowledgement remains on the adapter.
structure PrimitiveCut {kernel : Kernel.Contract} {runtime : Kernel.PrimitiveActorRuntime kernel}
    {initial : Kernel.World} {ticks : List (Kernel.ActorTick runtime)} {tick : Kernel.ActorTick runtime}
    {actor : Kernel.ActorId} {engine : Kernel.EngineState} {request : Request} {observed : Option Reply}
    (adapter : Kernel.PrimitiveAdapterAt runtime initial ticks tick actor engine request observed) where
  primary : request = adapter.occurrence.primary
  origin : Cut adapter.occurrence.logicalBefore request none
  noGuards : adapter.occurrence.inside = []
  rawTrace : engine.events = adapter.occurrence.rawBefore

theorem primitive_write_cut {kernel : Kernel.Contract} {runtime : Kernel.PrimitiveActorRuntime kernel}
    {initial : Kernel.World} {ticks : List (Kernel.ActorTick runtime)} {tick : Kernel.ActorTick runtime}
    {actor : Kernel.ActorId} {engine : Kernel.EngineState} {request : Request} {observed : Option Reply}
    (adapter : Kernel.PrimitiveAdapterAt runtime initial ticks tick actor engine request observed)
    (writing : request.op = .write) : Nonempty (PrimitiveCut adapter) := by
  have primary := PrimitiveFilesystem.filesystem_occurrence_primary adapter.occurrence
    (by simp only [writing]; intro wrong; cases wrong)
    (by simp only [writing]; intro wrong; cases wrong)
    (by simp only [writing]; intro wrong; cases wrong)
  have logical := PrimitiveFilesystem.filesystem_occurrence_logical adapter.occurrence
  rw [← primary] at logical
  obtain ⟨origin⟩ := write_cut (observed := none) logical writing
  have noGuards : adapter.occurrence.inside = [] := by
    have active := adapter.occurrence.adapter
    rw [← primary, write_adapter request writing] at active
    rcases call_cases active with empty | lost | ⟨reply, tail, shape, continued⟩
    · have impossible := congrArg List.length empty
      simp only [List.length_append, List.length_singleton, List.length_nil] at impossible
      omega
    · have length := congrArg List.length lost
      simp only [List.length_append, List.length_singleton] at length
      exact List.eq_nil_of_length_eq_zero (by omega)
    · have tailEmpty := Snapshot.prefix_pure_empty continued
      subst tail
      have length := congrArg List.length shape
      simp only [List.length_append, List.length_cons, List.length_nil] at length
      exact List.eq_nil_of_length_eq_zero (by omega)
  exact ⟨⟨primary, origin, noGuards,
    by simpa only [noGuards, List.map_nil, List.append_nil] using adapter.occurrence.trace⟩⟩

end LeanCage.Host.EntrypointWriterPrefix
