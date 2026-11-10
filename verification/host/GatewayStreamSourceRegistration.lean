import GatewayWriterRegistration

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

-- §AR-host-boundary.interfaces.gateway: Source call identities and immutable
-- raw arguments are data. Their registration never asserts a kernel effect.
abbrev SourceToken := CallKey × WriteDescription

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)} {pair : Pair}

def Primitive.with_source_engine_entries
    (samples : Primitive process child native hostUid before after callers next ticks pair SourceToken)
    (identity : ∀ token, samples.input token = token) :
    Primitive process child native hostUid before after callers next ticks pair SourceToken :=
  { samples with
    enteredEngine := fun token entry => token = (entry.key, entry.description)
    engineInput := by intro token entry entered; rw [identity, entered] }

def pure_engine_tokens
    (samples : Primitive process child native hostUid before after callers next ticks pair SourceToken)
    (identity : ∀ token, samples.input token = token) :
    EngineTokens (samples.with_source_engine_entries identity) :=
  ⟨fun entry => (entry.key, entry.description), fun _ => rfl⟩

-- This constructor discharges source-registration coverage without a trusted
-- role predicate, SDK success premise, writer return or expected response.
theorem actual_source_engine_registration
    (samples : Primitive process child native hostUid before after callers next ticks pair SourceToken)
    (identity : ∀ token, samples.input token = token)
    {position : Nat} {tick : ActorTick runtime} (selected : ticks[position]? = some tick)
    (initial : PhysicalState) :
    Nonempty (EngineRegistration (samples.with_source_engine_entries identity) position tick initial) :=
  actual_engine_registration (pure_engine_tokens samples identity) selected initial

end LeanCage.Host.PrivateStreams
