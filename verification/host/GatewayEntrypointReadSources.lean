import GatewayApplicationReadSources
import EntrypointPendingWriter
import FilesystemLoweredReads

namespace LeanCage.Host.EntrypointReadSources
open Filesystem Kernel PrivateStreams

private theorem seal_no_read (descriptors : List UInt64) :
    RequestProgram NoRead (Startup.sealDescriptors descriptors) := by
  induction descriptors with
  | nil => exact .pure _
  | cons fd rest ih =>
    unfold Startup.sealDescriptors
    apply RequestProgram.call (by intro impossible; cases impossible)
    intro reply
    split
    · exact .pure _
    · exact ih

private theorem packet_exact_read (fuel : Nat) (fd : UInt64) (amount : Nat) (bytes : ByteArray) :
    RequestProgram (fun request => request.op = .read → request.first = fd ∧ request.third = 0)
      (Packet.readExact fuel fd amount bytes) := by
  induction fuel generalizing bytes with
  | zero => exact .pure _
  | succ fuel ih =>
    unfold Packet.readExact
    repeat' first
      | exact .pure _
      | split
      | exact ih _
      | apply RequestProgram.call (by intro; exact ⟨rfl, rfl⟩); intro reply

theorem packet_read (fd : UInt64) :
    RequestProgram (fun request => request.op = .read → request.first = fd ∧ request.third = 0) (Packet.read fd) := by
  unfold Packet.read
  apply request_bind (packet_exact_read _ _ _ _)
  intro header
  cases header with
  | error => exact .pure _
  | ok header =>
    dsimp only
    split
    · exact .pure _
    · apply request_bind (packet_exact_read _ _ _ _)
      intro payload
      cases payload with
      | error => exact .pure _
      | ok payload =>
        dsimp only
        apply RequestProgram.call (by intro; exact ⟨rfl, rfl⟩)
        intro reply
        dsimp only [Filesystem.Program.bind]
        repeat' first | exact .pure _ | split

structure MachineCut (before : List Program.Event) (request : Request) (observed : Option Reply) where
  packet : EntrypointPrefixCuts.Read
  original : GatewayWire.Request
  effective : GatewayWire.Request
  duration : Option Nat
  accepted : packet.packet = .ok original
  invocation : Commands.Invocation original effective duration
  inside : List Program.Event
  executed : Program.Prefix (execute effective duration) (inside ++ [Program.filesystemPrefixEvent (request, observed)])
  machine : MachineRead inside (Program.filesystemPrefixEvent (request, observed))
  trace : before = packet.events ++ inside

-- §FS-host-boundary.caller: The union follows all actual entrypoint branches,
-- including CLI dispatch and lost current reads. A stream role is derived;
-- a copied file stays positional even if its pathname names a socket alias.
inductive Cut (before : List Program.Event) (request : Request) (observed : Option Reply) : Type 1 where
  | positioned (offset : request.third ≠ 0) : Cut before request observed
  | packet (ready : EntrypointPrefixCuts.Ready) (inside : List Program.Event)
      (source : Program.Prefix (Program.liftFilesystem (Packet.read 0))
        (inside ++ [Program.filesystemPrefixEvent (request, observed)]))
      (trace : before = ready.events ++ inside) (descriptor : request.first = 0) (stream : request.third = 0) :
      Cut before request observed
  | machine (source : MachineCut before request observed) (stream : request.third = 0) : Cut before request observed

theorem read_cut {before : List Program.Event} {request : Request} {observed : Option Reply}
    (source : Program.Prefix Entrypoint.run (before ++ [Program.filesystemPrefixEvent (request, observed)]))
    (reading : request.op = .read) : Nonempty (Cut before request observed) := by
  by_cases stream : request.third = 0
  · obtain ⟨cut⟩ := EntrypointPrefixCuts.entrypoint_cut source
    cases cut with
    | starting source => exact False.elim ((selected_filesystem_profile (seal_no_read [0, 1, 3]) source) reading)
    | reading ready inside source trace =>
      have descriptor := selected_filesystem_profile (packet_read 0) source reading
      exact ⟨.packet ready inside source trace descriptor.1 descriptor.2⟩
    | responding packet inside source trace =>
      obtain ⟨original, accepted, commanded⟩ := EntrypointPrefixCuts.packet_response_prefix source
      obtain ⟨effective, duration, invocation, executed⟩ := Commands.run_prefix_source original commanded
      obtain ⟨machine⟩ := caller_stream_read effective duration executed reading stream
      exact ⟨.machine ⟨packet, original, effective, duration, accepted, invocation, inside, executed, machine, trace⟩ stream⟩
    | writing context inside bound source trace =>
      exact False.elim ((selected_filesystem_profile (write_loop_positioned _ _ _ _) source) reading stream)
  · exact ⟨.positioned stream⟩

-- This is the same pending raw source call, not a later successful read.
-- Its original lowered occurrence retains the exact ordinal and arguments.
structure PendingCut (engine : EngineState) (request : Request) where
  occurrence : PrimitiveFilesystem.FilesystemOccurrence Entrypoint.run engine.events request none
  primary : request = occurrence.primary
  origin : Cut occurrence.logicalBefore request none
  noGuards : occurrence.inside = []
  rawTrace : engine.events = occurrence.rawBefore

theorem pending_read_source {engine : EngineState} {request : Request} {next : Reply → Program UInt32}
    (source : Residual (PrimitiveFilesystem.lower Entrypoint.run) engine.events engine.current)
    (head : engine.current = .call (.filesystem request) next) (reading : request.op = .read) :
    Nonempty (PendingCut engine request) := by
  have raw : Program.Prefix (PrimitiveFilesystem.lower Entrypoint.run)
      (engine.events ++ [Program.filesystemPrefixEvent (request, none)]) := by
    apply residual_prefix source
    rw [head]
    exact .lost _ _
  obtain ⟨occurrence⟩ := PrimitiveFilesystem.lowered_filesystem_source Entrypoint.run raw
  have primary := PrimitiveFilesystem.filesystem_occurrence_primary occurrence
    (by simp only [reading]; intro impossible; cases impossible)
    (by simp only [reading]; intro impossible; cases impossible)
    (by simp only [reading]; intro impossible; cases impossible)
  have logical := PrimitiveFilesystem.filesystem_occurrence_logical occurrence
  rw [← primary] at logical
  obtain ⟨origin⟩ := read_cut (observed := none) logical reading
  have noGuards : occurrence.inside = [] := by
    have adapter := occurrence.adapter
    rw [← primary] at adapter
    exact Lowered.read_adapter_empty adapter reading
  exact ⟨⟨occurrence, primary, origin, noGuards,
    by simpa only [noGuards, List.map_nil, List.append_nil] using occurrence.trace⟩⟩

theorem pending_read_at {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {ticks : List (ActorTick runtime)} {final : Population}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} (selected : ticks[position]? = some tick)
    {actor : ActorId} {engine : EngineState} (present : tick.before.actors actor = some engine)
    (running : engine.running = true) {request : Request} {next : Reply → Program UInt32}
    (head : engine.current = .call (.filesystem request) next) (reading : request.op = .read) :
    Nonempty (PendingCut engine request) := by
  obtain ⟨leading, trailing, shape⟩ := selected_tick_split selected
  exact pending_read_source (selected_actor_head_for journal leading trailing tick shape present running) head reading

end LeanCage.Host.EntrypointReadSources
