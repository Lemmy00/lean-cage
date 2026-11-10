import GatewayStreamSources
import EntrypointChannelWriter

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

-- §FS-host-boundary.caller: This is a proof-only factor of the actual entrypoint;
-- the maintained executable still runs Entrypoint.run.
def responsePrelude : Program (Option (Nat × GatewayWire.Value)) :=
  (Program.liftFilesystem Startup.descriptors).bind fun ready =>
    match ready with
    | .error _ => .pure none
    | .ok () => (Program.liftFilesystem (Packet.read 0)).bind fun packet =>
      (Entrypoint.packetResponse packet).bind fun response => .pure (some response)

def responseTail : Option (Nat × GatewayWire.Value) → Program UInt32
  | none => .pure 126
  | some response => do
    let encoded := GatewayWire.encodeResponse response.1 response.2
    if encoded.size > GatewayWire.responseMax then return 126
    let written ← Program.liftFilesystem (writeLoop (encoded.size + 1) 1 encoded 0)
    match written with
    | .error _ => return 126
    | .ok () => return 0

private theorem bind_associative {α β γ : Type} (first : Program α)
    (second : α → Program β) (third : β → Program γ) :
    (first.bind second).bind third = first.bind (fun value => (second value).bind third) := by
  induction first with
  | pure => rfl
  | call effect next ih =>
    exact congrArg (Program.call effect) (funext ih)

theorem entrypoint_response_factor : Entrypoint.run = responsePrelude.bind responseTail := by
  unfold responsePrelude
  rw [bind_associative]
  unfold Entrypoint.run
  apply congrArg (Program.bind (Program.liftFilesystem Startup.descriptors))
  funext ready
  cases ready with
  | error => rfl
  | ok ready =>
    cases ready
    rw [bind_associative]
    apply congrArg (Program.bind (Program.liftFilesystem (Packet.read 0)))
    funext packet
    rw [bind_associative]
    rfl

theorem responded_prelude (context : EntrypointPrefixCuts.Responded) :
    Program.Returns responsePrelude context.events (some context.response) := by
  unfold responsePrelude
  rw [EntrypointPrefixCuts.Responded.events, EntrypointPrefixCuts.Read.events,
    EntrypointPrefixCuts.Ready.events, List.append_assoc]
  apply Program.returns_bind (Program.lift_filesystem_returns context.read.ready.startup)
  dsimp only
  apply Program.returns_bind (Program.lift_filesystem_returns context.read.read)
  simpa only [List.append_nil] using
    (Program.returns_bind (next := fun value => .pure (some value)) context.respond (.pure (some context.response)))

-- §AR-host-boundary.primitives: Splitting the real lowering retains each actual
-- primitive adapter chunk rather than reconstructing an equal logical transcript.
theorem reached_return_split {α β : Type} {program : Program α} {next : α → Program β}
    {completed logical raw : List Program.Event} {value : α} {after : Program β}
    (returned : Program.Returns program completed value)
    (reached : PrimitiveFilesystem.Reached (program.bind next) (completed ++ logical) raw after) :
    ∃ first last, raw = first ++ last ∧
      PrimitiveFilesystem.Reached program completed first (.pure value) ∧
      PrimitiveFilesystem.Reached (next value) logical last after := by
  induction returned generalizing logical raw with
  | pure value => exact ⟨[], raw, rfl, .refl _, reached⟩
  | call effect continuation reply tail value returned ih =>
    cases reached with
    | call _ _ actual inside _ rest _ adapter continued =>
      obtain ⟨first, last, shape, before, final⟩ := ih continued
      exact ⟨inside ++ first, last, by simp only [shape, List.append_assoc],
        .call effect continuation reply inside tail first _ adapter before, final⟩

theorem reached_pure_returns {α : Type} {program : Program α} {logical raw : List Program.Event}
    {value : α} (reached : PrimitiveFilesystem.Reached program logical raw (.pure value)) :
    Program.Returns (PrimitiveFilesystem.lower program) raw value := by
  generalize shape : (Program.pure value : Program α) = after at reached
  induction reached with
  | refl => cases shape; exact .pure _
  | call effect next reply inside logical raw after adapter rest ih =>
    exact Program.returns_bind adapter (ih shape)

inductive Transparent {α : Type} : Program α → Prop where
  | pure (value : α) : Transparent (.pure value)
  | call {β : Type} (effect : Effect β) (next : β → Program α)
      (identity : PrimitiveFilesystem.lowerEffect effect = Program.effect effect)
      (tail : ∀ value, Transparent (next value)) : Transparent (.call effect next)

private theorem transparent_bind {α β : Type} {program : Program α} {next : α → Program β}
    (first : Transparent program) (last : ∀ value, Transparent (next value)) : Transparent (program.bind next) := by
  induction first with
  | pure value => exact last value
  | call effect continuation identity tail ih => exact .call effect _ identity ih

private theorem transparent_writer (fuel : Nat) (fd : UInt64) (bytes : ByteArray) (offset : Nat) :
    Transparent (Program.liftFilesystem (writeLoop fuel fd bytes offset)) := by
  induction fuel generalizing offset with
  | zero => exact .pure _
  | succ fuel ih =>
    unfold writeLoop
    split
    · exact .pure _
    · apply Transparent.call _ _ rfl
      intro reply
      dsimp only
      repeat' first | exact .pure _ | exact ih _ | split

theorem transparent_response_tail (response : Option (Nat × GatewayWire.Value)) :
    Transparent (responseTail response) := by
  cases response with
  | none => exact .pure _
  | some response =>
    simp only [responseTail]
    split
    · exact .pure _
    · apply transparent_bind (transparent_writer _ _ _ _)
      intro result
      cases result with
      | error => exact .pure _
      | ok result => cases result; exact .pure _

private theorem effect_returns_exact {α : Type} {effect : Effect α} {events : List Program.Event}
    {result : α} (run : Program.Returns (Program.effect effect) events result) :
    events = [.returned effect result] := by
  cases run with
  | call _ _ reply tail result rest =>
    obtain ⟨rfl, rfl⟩ := Program.returns_pure _ rest
    rfl

theorem reached_transparent {α : Type} {program after : Program α} {logical raw : List Program.Event}
    (source : PrimitiveFilesystem.Reached program logical raw after) (profile : Transparent program) : raw = logical := by
  induction source with
  | refl => rfl
  | call effect next reply inside logical raw after adapter rest ih =>
    cases profile with
    | call _ _ identity tail =>
      have chunk := effect_returns_exact (identity ▸ adapter)
      simp only [chunk, ih (tail reply), List.singleton_append]

-- §FS-host-boundary.caller: A completed deterministic source phase is prefix-free.
-- Both executions must use the same actual dependent request/reply events.
theorem returned_prefix_unique {α : Type} {program : Program α} {first last : List Program.Event}
    {value result : α} (initial : Program.Returns program first value)
    (final : Program.Returns program last result) (leading : first <+: last) :
    first = last ∧ value = result := by
  induction initial generalizing last with
  | pure value =>
    obtain ⟨rfl, rfl⟩ := Program.returns_pure _ final
    exact ⟨rfl, rfl⟩
  | call effect next reply tail value returned ih =>
    cases final with
    | call _ _ actual rest result continued =>
      obtain ⟨suffix, same⟩ := leading
      have heads := List.cons.inj same
      have values : reply = actual := by cases heads.1; rfl
      subst actual
      obtain ⟨rfl, rfl⟩ := ih continued ⟨suffix, heads.2⟩
      exact ⟨rfl, rfl⟩

theorem returned_common_prefix_unique {α : Type} {program : Program α}
    {first last common : List Program.Event} {value result : α}
    (initial : Program.Returns program first value) (final : Program.Returns program last result)
    (left : first <+: common) (right : last <+: common) : first = last ∧ value = result := by
  rcases List.prefix_or_prefix_of_prefix left right with leading | leading
  · exact returned_prefix_unique initial final leading
  · have same := returned_prefix_unique final initial leading
    exact ⟨same.1.symm, same.2.symm⟩

-- §FS-host-boundary.caller: The source response is recovered from the SAME
-- pending raw call, including the lowering's actual preceding SDK operations.
theorem pending_response_prelude {engine : EngineState} {request : Request}
    (pending : EntrypointWriterPrefix.PendingCut engine request)
    (response : EntrypointWriterPrefix.ResponseFrontier pending.occurrence.logicalBefore request none) :
    ∃ raw, raw <+: engine.events ∧
      Program.Returns (PrimitiveFilesystem.lower responsePrelude) raw (some response.context.response) := by
  have reached : PrimitiveFilesystem.Reached (responsePrelude.bind responseTail)
      (response.context.events ++ response.inside.map Program.filesystemPrefixEvent)
      pending.occurrence.rawBefore
      (.call (.filesystem pending.occurrence.primary) pending.occurrence.next) := by
    simpa only [← entrypoint_response_factor, ← response.trace] using pending.occurrence.reached
  obtain ⟨raw, rest, shape, before, after⟩ := reached_return_split
    (responded_prelude response.context) reached
  exact ⟨raw, ⟨rest, by simpa only [pending.rawTrace] using shape.symm⟩, reached_pure_returns before⟩

-- §FS-host-boundary.caller: After the response is computed, the actual lowering
-- inserts no probes. Every older response write/ACK is retained in this raw prefix.
theorem pending_response_raw {engine : EngineState} {request : Request}
    (pending : EntrypointWriterPrefix.PendingCut engine request)
    (response : EntrypointWriterPrefix.ResponseFrontier pending.occurrence.logicalBefore request none) :
    ∃ raw, Program.Returns (PrimitiveFilesystem.lower responsePrelude) raw (some response.context.response) ∧
      engine.events = raw ++ response.writer.acknowledged.map Program.filesystemEvent := by
  have reached : PrimitiveFilesystem.Reached (responsePrelude.bind responseTail)
      (response.context.events ++ response.inside.map Program.filesystemPrefixEvent)
      pending.occurrence.rawBefore
      (.call (.filesystem pending.occurrence.primary) pending.occurrence.next) := by
    simpa only [← entrypoint_response_factor, ← response.trace] using pending.occurrence.reached
  obtain ⟨raw, rest, shape, before, after⟩ := reached_return_split
    (responded_prelude response.context) reached
  have transparent := reached_transparent after (transparent_response_tail _)
  refine ⟨raw, reached_pure_returns before, ?_⟩
  calc
    engine.events = pending.occurrence.rawBefore := pending.rawTrace
    _ = raw ++ rest := shape
    _ = raw ++ response.inside.map Program.filesystemPrefixEvent := congrArg (raw ++ ·) transparent
    _ = raw ++ response.writer.acknowledged.map Program.filesystemEvent := by
      have same := congrArg (fun events => raw ++ events.map Program.filesystemPrefixEvent) response.writer.trace
      have conversion : Program.filesystemPrefixEvent ∘
          (fun event : Request × Reply => (event.1, some event.2)) = Program.filesystemEvent := rfl
      simpa only [Publication.completed, List.map_map, conversion] using same

-- §FS-host-boundary.caller: Two pending writes on one actual source prefix
-- cannot choose different engine observations, even if neither write returns.
theorem pending_response_unique {firstEngine lastEngine : EngineState} {firstRequest lastRequest : Request}
    (first : EntrypointWriterPrefix.PendingCut firstEngine firstRequest)
    (last : EntrypointWriterPrefix.PendingCut lastEngine lastRequest)
    (firstResponse : EntrypointWriterPrefix.ResponseFrontier first.occurrence.logicalBefore firstRequest none)
    (lastResponse : EntrypointWriterPrefix.ResponseFrontier last.occurrence.logicalBefore lastRequest none)
    (ordered : firstEngine.events <+: lastEngine.events) :
    firstResponse.context.response = lastResponse.context.response ∧
      firstResponse.context.bytes = lastResponse.context.bytes := by
  obtain ⟨left, earlier, before⟩ := pending_response_prelude first firstResponse
  obtain ⟨right, later, after⟩ := pending_response_prelude last lastResponse
  have same : left = right ∧ some firstResponse.context.response = some lastResponse.context.response :=
    returned_common_prefix_unique before after (earlier.trans ordered) later
  have values := Option.some.inj same.2
  exact ⟨values, congrArg (fun value : Nat × GatewayWire.Value => GatewayWire.encodeResponse value.1 value.2) values⟩

def acknowledgedExtent (events : List (Request × Reply)) : Nat := (events.map (fun event => event.2.1.toNat)).sum

theorem acknowledged_extent {fd : UInt64} {bytes : ByteArray} {first last : Nat} {events : List (Request × Reply)}
    (source : EntrypointWriterPrefix.AcknowledgedPrefix fd bytes first events last) :
    last = first + acknowledgedExtent events := by
  induction source with
  | nil => simp [acknowledgedExtent]
  | more offset reply events final inside native empty positive bounded tail ih =>
    simpa only [acknowledgedExtent, List.map_cons, List.sum_cons, Nat.add_assoc] using ih

private theorem filesystem_event_injective (first last : Request × Reply)
    (same : Program.filesystemEvent first = Program.filesystemEvent last) : first = last := by
  rcases first with ⟨first, firstReply⟩
  rcases last with ⟨last, lastReply⟩
  cases same
  rfl

-- §FS-host-boundary.caller: Earlier acknowledged writes are an actual prefix,
-- so the next source offset cannot restart, skip or invent acknowledged bytes.
theorem pending_response_sequence {firstEngine lastEngine : EngineState} {firstRequest lastRequest : Request}
    (first : EntrypointWriterPrefix.PendingCut firstEngine firstRequest)
    (last : EntrypointWriterPrefix.PendingCut lastEngine lastRequest)
    (firstResponse : EntrypointWriterPrefix.ResponseFrontier first.occurrence.logicalBefore firstRequest none)
    (lastResponse : EntrypointWriterPrefix.ResponseFrontier last.occurrence.logicalBefore lastRequest none)
    (ordered : firstEngine.events <+: lastEngine.events) :
    ∃ extra, lastResponse.writer.acknowledged = firstResponse.writer.acknowledged ++ extra ∧
      lastResponse.writer.offset = firstResponse.writer.offset + acknowledgedExtent extra := by
  obtain ⟨left, before, firstShape⟩ := pending_response_raw first firstResponse
  obtain ⟨right, after, lastShape⟩ := pending_response_raw last lastResponse
  have same := returned_common_prefix_unique before after
    (List.IsPrefix.trans (⟨_, firstShape.symm⟩ : left <+: firstEngine.events) ordered)
    (⟨_, lastShape.symm⟩ : right <+: lastEngine.events)
  have earlier : left ++ firstResponse.writer.acknowledged.map Program.filesystemEvent <+:
      left ++ lastResponse.writer.acknowledged.map Program.filesystemEvent := by
    simpa only [firstShape, lastShape, same.1] using ordered
  obtain ⟨remaining, shape⟩ := earlier
  have mapped : firstResponse.writer.acknowledged.map Program.filesystemEvent <+:
      lastResponse.writer.acknowledged.map Program.filesystemEvent :=
    ⟨remaining, List.append_cancel_left (by simpa only [List.append_assoc] using shape)⟩
  obtain ⟨prefixEvents, leading, mappedIdentity⟩ := List.prefix_map_iff.mp mapped
  have selected := (List.map_inj_right filesystem_event_injective).mp mappedIdentity
  obtain ⟨extra, trace⟩ := leading
  have older : lastResponse.writer.acknowledged = firstResponse.writer.acknowledged ++ extra := by
    simpa only [← selected] using trace.symm
  refine ⟨extra, older, ?_⟩
  have firstOffset := acknowledged_extent firstResponse.writer.progress
  have lastOffset := acknowledged_extent lastResponse.writer.progress
  rw [older] at lastOffset
  simp only [acknowledgedExtent, List.map_append, List.sum_append, Nat.zero_add] at firstOffset lastOffset
  exact lastOffset.trans (congrArg (· + acknowledgedExtent extra) firstOffset.symm)

-- §FS-host-boundary.caller: Source ordering is extracted from this SAME actor
-- journal, including all unrelated, lost and retirement steps between writes.
theorem selected_events_prefix {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {before after : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime before ticks after) {first second : Nat} {left right : ActorTick runtime}
    (ordered : first ≤ second) (leftAt : ticks[first]? = some left) (rightAt : ticks[second]? = some right)
    (actor : ActorId) (initial final : EngineState)
    (initialPresent : left.before.actors actor = some initial) (finalPresent : right.before.actors actor = some final) :
    initial.events <+: final.events := by
  induction first generalizing ticks before second with
  | zero =>
    cases journal with
    | nil => cases leftAt
    | @cons tick ticks after tail =>
      have sameTick : tick = left := Option.some.inj leftAt
      subst left
      cases second with
      | zero =>
        have sameRight : tick = right := Option.some.inj rightAt
        subst right
        have sameEngine := Option.some.inj (initialPresent.symm.trans finalPresent)
        subst initial
        exact List.prefix_rfl
      | succ second =>
        obtain ⟨middle, extra, middlePresent, shape⟩ := actor_step_event_prefix tick.operation actor initial initialPresent
        obtain ⟨leading, preceding⟩ := journal_to_selected tail rightAt
        obtain ⟨last, lastShape⟩ := actor_journal_event_prefix preceding actor middle final middlePresent finalPresent
        exact ⟨extra ++ last, by rw [lastShape, shape, List.append_assoc]⟩
  | succ first ih =>
    cases second with
    | zero => omega
    | succ second =>
      cases journal with
      | nil => cases leftAt
      | cons tail => exact ih tail (by omega) leftAt rightAt

structure EngineResponse {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {ticks : List (ActorTick runtime)} {pair : Pair} (entry : EngineWriteEntry ticks pair) where
  pending : EntrypointWriterPrefix.PendingCut entry.engine entry.request
  source : EntrypointWriterPrefix.ResponseFrontier pending.occurrence.logicalBefore entry.request none

-- §FS-host-boundary.ownership: The only input supplied by the channel mapping
-- is the actual inherited handle/object/OFD identity, not a claimed response.
theorem engine_response_from_inherited {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (introductions : DescriptionIntroductionContract kernel)
    (retirement : DescriptorRetirementContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)} {pair : Pair}
    (journal : ActorJournal runtime (Population.empty initial) ticks final) (entry : EngineWriteEntry ticks pair)
    (history : SelectedActorHistory runtime initial ticks entry.tick entry.actor entry.engine)
    (fd : UInt64) (inherited : Handle) (live : history.launch.references fd = some inherited)
    (sameObject : entry.handle.object = inherited.object) (sameDescription : entry.handle.description = inherited.description) :
    Nonempty (EngineResponse entry) := by
  obtain ⟨pending⟩ := engine_write_source journal entry
  obtain ⟨response⟩ := EntrypointWriterPrefix.inherited_response descriptors introductions retirement sdk lifetimes references
    journal entry.present history pending entry.writing live entry.input sameObject sameDescription
  exact ⟨⟨pending, response⟩⟩

theorem EngineResponse.payload {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {ticks : List (ActorTick runtime)} {pair : Pair} {entry : EngineWriteEntry ticks pair}
    (response : EngineResponse entry) :
    entry.request.first = 1 ∧ entry.request.left = response.source.context.bytes.extract response.source.writer.offset
      (min response.source.context.bytes.size (response.source.writer.offset + chunkMax)) ∧
      1 ≤ entry.request.left.size ∧ entry.request.left.size ≤ chunkMax ∧
      EntrypointWriterPrefix.acknowledgedBytes response.source.writer.acknowledged =
        response.source.context.bytes.extract 0 response.source.writer.offset := by
  obtain ⟨fd, writing, bytes, positive, bounded, acknowledged⟩ := response.source.payload
  exact ⟨fd, bytes, positive, bounded, acknowledged⟩

-- §FS-host-boundary.caller: All pending writes of the selected actual lifetime
-- use one encoded response; no completed whole engine execution is required.
theorem actual_engine_response_unique {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {before after : Population} {ticks : List (ActorTick runtime)} {pair : Pair}
    (journal : ActorJournal runtime before ticks after) (first last : EngineWriteEntry ticks pair)
    (sameActor : first.actor = last.actor) (firstResponse : EngineResponse first) (lastResponse : EngineResponse last) :
    firstResponse.source.context.response = lastResponse.source.context.response ∧
      firstResponse.source.context.bytes = lastResponse.source.context.bytes := by
  have initialPresent : first.tick.before.actors last.actor = some first.engine := by
    simpa only [sameActor] using first.present
  rcases Nat.le_total first.position last.position with ordered | ordered
  · exact pending_response_unique firstResponse.pending lastResponse.pending firstResponse.source lastResponse.source
      (selected_events_prefix journal ordered first.selected last.selected last.actor first.engine last.engine
        initialPresent last.present)
  · have same := pending_response_unique lastResponse.pending firstResponse.pending lastResponse.source firstResponse.source
      (selected_events_prefix journal ordered last.selected first.selected last.actor last.engine first.engine
        last.present initialPresent)
    exact ⟨same.1.symm, same.2.symm⟩

end LeanCage.Host.PrivateStreams
