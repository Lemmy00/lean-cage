import EntrypointProofs
import CommandProofs
import PrefixOrigins

namespace LeanCage.Host.EntrypointPrefixCuts
open Filesystem

structure Ready where
  starting : List (Request × Reply)
  startup : Returns Startup.descriptors starting (.ok ())

def Ready.events (context : Ready) := context.starting.map Program.filesystemEvent

structure Read where
  ready : Ready
  packet : Filesystem.Result GatewayWire.Request
  reading : List (Request × Reply)
  read : Returns (Packet.read 0) reading packet

def Read.events (context : Read) := context.ready.events ++ context.reading.map Program.filesystemEvent

structure Responded where
  read : Read
  response : Nat × GatewayWire.Value
  responding : List Program.Event
  respond : Program.Returns (Entrypoint.packetResponse read.packet) responding response

def Responded.events (context : Responded) := context.read.events ++ context.responding
def Responded.bytes (context : Responded) := GatewayWire.encodeResponse context.response.1 context.response.2

-- §FS-host-boundary.caller: Inherited endpoints and the exact parsed packet precede dispatch.
inductive Cut (before : List Program.Event) (event : Program.Event) : Type 1 where
  | starting (active : Program.Prefix (Program.liftFilesystem Startup.descriptors) (before ++ [event]))
  | reading (context : Ready) (inside : List Program.Event)
      (active : Program.Prefix (Program.liftFilesystem (Packet.read 0)) (inside ++ [event]))
      (trace : before = context.events ++ inside)
  | responding (context : Read) (inside : List Program.Event)
      (active : Program.Prefix (Entrypoint.packetResponse context.packet) (inside ++ [event]))
      (trace : before = context.events ++ inside)
  | writing (context : Responded) (inside : List Program.Event)
      (bound : context.bytes.size ≤ GatewayWire.responseMax)
      (active : Program.Prefix (Program.liftFilesystem
        (writeLoop (context.bytes.size + 1) 1 context.bytes 0)) (inside ++ [event]))
      (trace : before = context.events ++ inside)

-- §FS-host-boundary.acceptance: The executable's actual prefixes retain loss and denied setup.
theorem entrypoint_cut {before : List Program.Event} {event : Program.Event}
    (active : Program.Prefix Entrypoint.run (before ++ [event])) : Nonempty (Cut before event) := by
  unfold Entrypoint.run at active
  rcases Program.last_bind_split _ _ active with starting |
      ⟨starting, started, afterStart, startup, rest, startupShape⟩
  · exact ⟨.starting starting⟩
  · cases started with
    | error error => exact False.elim (Program.pure_has_no_last _ _ _ rest)
    | ok startedValue =>
      cases startedValue
      obtain ⟨startSource, startRun, startEvents⟩ := Program.lift_filesystem_source _ startup
      let ready : Ready := ⟨startSource, startRun⟩
      have readyShape : before = ready.events ++ afterStart := by
        simpa only [Ready.events, ready, startEvents] using startupShape
      rcases Program.last_bind_split _ _ rest with reading |
          ⟨reading, packet, afterRead, read, rest, readShape⟩
      · exact ⟨.reading ready afterStart reading readyShape⟩
      · obtain ⟨readSource, readRun, readEvents⟩ := Program.lift_filesystem_source _ read
        let context : Read := ⟨ready, packet, readSource, readRun⟩
        have readShape : before = context.events ++ afterRead := by
          simp only [Read.events, context, readyShape, readShape, readEvents, List.append_assoc]
        rcases Program.last_bind_split _ _ rest with responding |
            ⟨responding, response, afterResponse, respond, rest, responseShape⟩
        · exact ⟨.responding context afterRead responding readShape⟩
        · let responded : Responded := ⟨context, response, responding, respond⟩
          have respondedShape : before = responded.events ++ afterResponse := by
            simp only [Responded.events, responded, readShape, responseShape, List.append_assoc]
          dsimp only at rest
          split at rest
          · exact False.elim (Program.pure_has_no_last _ _ _ rest)
          · rename_i bounded
            rcases Program.last_bind_split _ _ rest with writing |
                ⟨writing, written, afterWrite, write, last, writeShape⟩
            · exact ⟨.writing responded afterResponse (by exact Nat.le_of_not_gt bounded) writing respondedShape⟩
            · cases written <;> exact False.elim (Program.pure_has_no_last _ _ _ last)

-- §FS-host-boundary.caller: A rejected packet has no application events, including lost calls.
theorem packet_response_prefix {raw : Filesystem.Result GatewayWire.Request}
    {before : List Program.Event} {event : Program.Event}
    (active : Program.Prefix (Entrypoint.packetResponse raw) (before ++ [event])) :
    ∃ request, raw = .ok request ∧ Program.Prefix (Commands.run request) (before ++ [event]) := by
  cases raw with
  | error error => exact False.elim (Program.pure_has_no_last _ _ _ active)
  | ok request => exact ⟨request, rfl, active⟩

end LeanCage.Host.EntrypointPrefixCuts

namespace LeanCage.Host.Commands

theorem dispatch_prefix_source (request : GatewayWire.Request) (duration : Option Nat)
    {before : List Program.Event} {event : Program.Event}
    (active : Program.Prefix (dispatch request duration) (before ++ [event])) :
    Program.Prefix (execute request duration) (before ++ [event]) := by
  unfold dispatch at active
  rcases Program.last_bind_split _ _ active with initial |
      ⟨initial, result, inside, invoked, last, shape⟩
  · exact initial
  · cases result <;> exact False.elim (Program.pure_has_no_last _ _ _ last)

inductive Invocation (original : GatewayWire.Request) : GatewayWire.Request → Option Nat → Prop where
  | native (command : original.command ≠ GatewayWire.cliCommand) : Invocation original original none
  | cli (parsed : Cli.Parsed) (command : original.command = GatewayWire.cliCommand)
      (parse : Cli.parse original = .ok (.command parsed)) :
      Invocation original parsed.request parsed.timeoutNanoseconds

-- §FS-host-boundary.caller: CLI argv bytes and direct callers reach the same application prefix.
theorem run_prefix_source (original : GatewayWire.Request)
    {before : List Program.Event} {event : Program.Event}
    (active : Program.Prefix (Commands.run original) (before ++ [event])) :
    ∃ effective duration, Invocation original effective duration ∧
      Program.Prefix (execute effective duration) (before ++ [event]) := by
  unfold Commands.run at active
  split at active
  · rename_i command
    have command : original.command = GatewayWire.cliCommand := by simpa using command
    unfold Commands.cli at active
    cases parsed : Cli.parse original with
    | error error =>
      rw [parsed] at active
      exact False.elim (Program.pure_has_no_last _ _ _ active)
    | ok action =>
      cases action with
      | help =>
        rw [parsed] at active
        exact False.elim (Program.pure_has_no_last _ _ _ active)
      | command request =>
        rw [parsed] at active
        rcases Program.last_bind_split _ _ active with dispatching |
            ⟨dispatching, response, inside, invoked, last, shape⟩
        · exact ⟨request.request, request.timeoutNanoseconds, .cli request command parsed,
            dispatch_prefix_source _ _ dispatching⟩
        · rcases response with ⟨status, value⟩
          exact False.elim (Program.pure_has_no_last _ _ _ last)
  · rename_i command
    exact ⟨original, none, .native (by simpa using command), dispatch_prefix_source _ _ active⟩

end LeanCage.Host.Commands
