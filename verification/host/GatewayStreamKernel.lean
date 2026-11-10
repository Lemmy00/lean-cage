import GatewayStreamSources

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

-- §AR-host-boundary.primitives: A token identifies one actual SDK invocation,
-- including its pending kernel progress, rather than a guessed FD or reply.
structure Primitive {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (process : ProcessContract runtime) (child : ChildPrimitive kernel) (native : NativePrimitive kernel)
    (hostUid : Nat) (before after : Processes) (callers next : NativeProcesses)
    (ticks : List (ActorTick runtime)) (pair : Pair) (Token : Type) where
  input : Token → CallKey × WriteDescription
  enteredEngine : Token → EngineWriteEntry ticks pair → Prop
  enteredNative : Token → NativeWriteEntry process child native hostUid before after callers next ticks pair → Prop
  engineInput : ∀ token entry, enteredEngine token entry → input token = (entry.key, entry.description)
  nativeInput : ∀ token entry, enteredNative token entry → input token = (entry.key, entry.description)
  progress : Nat → Token → WriteProgress → Nat → State → State → Prop
  progressLaw : ∀ position token current last initial final,
    progress position token current last initial final →
    current.input = (input token).2 ∧ current.canCommit ∧
    current.committed < last ∧ last ≤ (input token).2.bytes.length ∧
      initial.writeClosed (input token).2.sender = false ∧
      final = initial.enqueue (input token).2.sender (segment (input token).2.bytes current.committed last)
  observation : Nat → Token → WriteProgress → Option Reply → State → State → Prop
  observationLaw : ∀ position token current reply initial final,
    observation position token current reply initial final →
    current.input = (input token).2 ∧ current.observation = .pending ∧ final = initial ∧
      ∀ value, reply = some value → nativeError value = false → current.committed = value.1.toNat
  read : NativeReadEntry process child native hostUid before after callers next ticks pair → State → State → Prop
  readLaw : ∀ entry initial final, read entry initial final → entry.flags = 0 →
    entry.bytes.size ≤ entry.extent.toNat ∧
      ∃ remaining, initial.incoming entry.receiver = entry.bytes.data.toList ++ remaining ∧
        final = initial.setIncoming entry.receiver remaining
  birth : PairBirthEntry process child native hostUid before after callers next ticks pair → Option State → Option State → Prop
  birthLaw : ∀ entry initial final, birth entry initial final → initial = none ∧ final = some .empty
  other : Nat → Action → Option State → Option State → Prop
  otherLaw : ∀ position action initial final, other position action initial final →
    Step initial action final ∧ (∀ sender bytes, action ≠ .write sender bytes) ∧ action ≠ .born

-- §FS-host-boundary.caller: This adapter consumes one actual progress sample
-- and the source-bound input registry; it assumes no completed response/ACK.
theorem engine_progress_step {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
    {ticks : List (ActorTick runtime)} {pair : Pair} {Token : Type}
    (primitive : Primitive process child native hostUid before after callers next ticks pair Token)
    (position : Nat) (entry : EngineWriteEntry ticks pair) (token : Token) (current : WriteProgress)
    (physical : PhysicalState) (initial final : State) (extent : Nat)
    (_entered : primitive.enteredEngine token entry) (selected : physical.ledger entry.key = some current)
    (live : physical.stream = some initial)
    (actual : primitive.progress position token current extent initial final) :
    ProgressStep physical (.commit entry.key extent)
      [.write current.input.sender (segment current.input.bytes current.committed extent)]
      { stream := some final
        ledger := physical.ledger.set entry.key
          { current with
            committed := extent
            bounded := by
              have result := primitive.progressLaw _ _ _ _ _ _ actual
              exact result.1.symm ▸ result.2.2.2.1 } } := by
  obtain ⟨identity, unreturned, increase, bound, writable, state⟩ := primitive.progressLaw _ _ _ _ _ _ actual
  have identity := identity.symm
  rw [identity] at bound writable state
  subst final
  simpa only [identity] using
    (ProgressStep.commit physical entry.key current initial extent selected live unreturned increase bound writable)

theorem token_progress_step {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
    {ticks : List (ActorTick runtime)} {pair : Pair} {Token : Type}
    (primitive : Primitive process child native hostUid before after callers next ticks pair Token)
    (position : Nat) (token : Token) (current : WriteProgress) (physical : PhysicalState)
    (initial final : State) (extent : Nat)
    (selected : physical.ledger (primitive.input token).1 = some current) (live : physical.stream = some initial)
    (actual : primitive.progress position token current extent initial final) :
    ProgressStep physical (.commit (primitive.input token).1 extent)
      [.write current.input.sender (segment current.input.bytes current.committed extent)]
      { stream := some final
        ledger := physical.ledger.set (primitive.input token).1
          { current with
            committed := extent
            bounded := by
              have result := primitive.progressLaw _ _ _ _ _ _ actual
              exact result.1.symm ▸ result.2.2.2.1 } } := by
  obtain ⟨input, unreturned, increase, bound, writable, state⟩ := primitive.progressLaw _ _ _ _ _ _ actual
  rw [← input] at bound writable state
  subst final
  simpa only [← input] using
    ProgressStep.commit physical _ current initial extent selected live unreturned increase bound writable

def observed (previous : WriteProgress) : Option Reply → WriteProgress
  | none => { previous with observation := .lost }
  | some reply => { previous with observation := .returned reply }

def observationEvent (key : CallKey) : Option Reply → ProgressEvent
  | none => .lost key
  | some reply => .returned key reply

theorem token_observation_step {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
    {ticks : List (ActorTick runtime)} {pair : Pair} {Token : Type}
    (primitive : Primitive process child native hostUid before after callers next ticks pair Token)
    (position : Nat) (token : Token) (current : WriteProgress) (physical : PhysicalState)
    (initial final : State) (reply : Option Reply)
    (selected : physical.ledger (primitive.input token).1 = some current) (live : physical.stream = some initial)
    (actual : primitive.observation position token current reply initial final) :
    ProgressStep physical (observationEvent (primitive.input token).1 reply) []
      { stream := some final
        ledger := physical.ledger.set (primitive.input token).1 (observed current reply) } := by
  obtain ⟨input, pending, state, count⟩ := primitive.observationLaw _ _ _ _ _ _ actual
  subst final
  cases reply with
  | none => simpa only [observationEvent, observed, ← live] using ProgressStep.lost physical _ current selected pending
  | some reply =>
    simpa only [observationEvent, observed, ← live] using
      ProgressStep.returned physical _ current reply selected pending (count reply rfl)

theorem native_read_step {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
    {ticks : List (ActorTick runtime)} {pair : Pair} {Token : Type}
    (primitive : Primitive process child native hostUid before after callers next ticks pair Token)
    (entry : NativeReadEntry process child native hostUid before after callers next ticks pair)
    (physical : PhysicalState) (initial final : State)
    (live : physical.stream = some initial) (flags : entry.flags = 0)
    (actual : primitive.read entry initial final) :
    ProgressStep physical (.channel (.read entry.receiver entry.bytes.data.toList))
      [.read entry.receiver entry.bytes.data.toList] { physical with stream := some final } := by
  obtain ⟨bound, remaining, contents, state⟩ := primitive.readLaw entry initial final actual flags
  subst final
  apply ProgressStep.channel
  · rw [live]
    exact .read _ _ _ _ contents
  · intro sender bytes impossible
    cases impossible

theorem pair_birth_step {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
    {ticks : List (ActorTick runtime)} {pair : Pair} {Token : Type}
    (primitive : Primitive process child native hostUid before after callers next ticks pair Token)
    (entry : PairBirthEntry process child native hostUid before after callers next ticks pair)
    (physical : PhysicalState) (final : Option State)
    (actual : primitive.birth entry physical.stream final) :
    ProgressStep physical (.channel .born) [.born] { physical with stream := final } := by
  obtain ⟨initial, finalState⟩ := primitive.birthLaw entry physical.stream final actual
  apply ProgressStep.channel
  · rw [initial, finalState]
    exact .born
  · intro sender bytes impossible
    cases impossible

theorem other_step {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
    {ticks : List (ActorTick runtime)} {pair : Pair} {Token : Type}
    (primitive : Primitive process child native hostUid before after callers next ticks pair Token)
    (position : Nat) (physical : PhysicalState) (action : Action) (final : Option State)
    (actual : primitive.other position action physical.stream final) :
    ProgressStep physical (.channel action) [action] { physical with stream := final } := by
  have law := primitive.otherLaw _ _ _ _ actual
  exact .channel physical action final law.1 law.2.1

end LeanCage.Host.PrivateStreams
