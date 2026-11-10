import GatewayWriterReturnedOrdinal

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)} {pair : Pair} {Token : Type}

-- §FS-host-boundary.caller: Process the actual source step and its mandatory
-- matching ACK together. Only an actual source return advances a live writer;
-- a lost call stays eligible for pending progress and creates no next write.
theorem ReturnedSourceAligned.advance
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {initialWorld : World} {finalPopulation : Population}
    (journal : ActorJournal runtime (Population.empty initialWorld) ticks finalPopulation)
    {position : Nat} {tick : ActorTick runtime} (selectedTick : ticks[position]? = some tick)
    {initial final : PhysicalState} {records : List Record}
    (row : EngineRow primitive position tick initial records final)
    (registered : Registered primitive position initial)
    (aligned : ReturnedSourceAligned tick.before initial.ledger) : ReturnedSourceAligned tick.after final.ledger := by
  intro query observed finalAt
  have retained := fun actor ordinal (before : OlderReturned actor ordinal initial.ledger) =>
    row.older_returned actor ordinal before
  cases tick with
  | mk action before after step =>
    cases step with
    | @launch population actor references flags cwd fresh absent inherited =>
      by_cases same : query = actor
      · subst query
        simp only [Population.launch, Population.install, ite_true, Option.some.injEq] at finalAt
        subst observed
        intro older bound current stored
        simp only [EngineState.initialFrom, returnedOrdinal] at bound
        omega
      · have present : before.actors query = some observed := by
          simpa only [Population.launch, Population.install, ite_eq_right same] using finalAt
        exact retained query (returnedOrdinal observed.events) (aligned query observed present)
    | @returned β population actor engine effect next reply world present alive head actual =>
      by_cases same : query = actor
      · subst query
        simp only [Population.advance, Population.install, ite_true, Option.some.injEq] at finalAt
        subst observed
        have returnedCount := actual_running_returned_ordinal journal selectedTick actor engine present alive
        have previous := retained actor engine.events.length
          (by simpa only [returnedCount] using aligned actor engine present)
        intro older bound current stored
        have length : returnedOrdinal (engine.returned effect reply next world).events = engine.events.length + 1 := by
          simp [EngineState.returned, returned_ordinal_append, returnedOrdinal, returnedCount]
        rw [length] at bound
        by_cases earlier : older < engine.events.length
        · exact previous older earlier current stored
        · have ordinal : older = engine.events.length := by omega
          subst older
          obtain ⟨prior, priorAt⟩ := row.entry_existed _ current stored
          obtain ⟨entry, token, entered, key, input, order⟩ :=
            registered_engine_source registered actor engine.events.length prior priorAt
          have fields := CallKey.engine.inj key
          have atActor : before.actors entry.actor = some engine := by simpa only [fields.1] using present
          have sameHead := actual_same_ordinal_head journal entry selectedTick engine atActor alive fields.2.symm
          have typed := congrArg filesystemHead sameHead
          rw [head, entry.head] at typed
          cases effect with
          | filesystem request =>
            simp only [filesystemHead, Option.some.injEq] at typed
            have writing : request.op = .write := typed ▸ entry.writing
            have scan := write_observation_complete
              (⟨.returned actor (.filesystem request) reply, before,
                before.advance actor (engine.returned (.filesystem request) reply next world) world,
                .returned present alive head actual⟩ : ActorTick runtime)
              actor engine present request (some reply) writing (by simp [ActorAction.eventFor, Program.filesystemPrefixEvent])
            refine ⟨reply, ?_⟩
            exact row.returned_key ⟨actor, engine.events.length, request, some reply⟩ scan reply rfl current stored
          | spawn | read | wait | terminate | tryWait | descriptor => simp [filesystemHead] at typed
      · have initialAt : before.actors query = some observed := by
          simpa only [Population.advance, Population.install, ite_eq_right same] using finalAt
        exact retained query (returnedOrdinal observed.events) (aligned query observed initialAt)
    | @lost β population actor engine effect next world present alive head actual =>
      by_cases same : query = actor
      · subst query
        simp only [Population.advance, Population.install, ite_true, Option.some.injEq] at finalAt
        subst observed
        simpa only [EngineState.lost, returned_ordinal_append, returnedOrdinal, Nat.add_zero] using
          retained actor (returnedOrdinal engine.events) (aligned actor engine present)
      · have initialAt : before.actors query = some observed := by
          simpa only [Population.advance, Population.install, ite_eq_right same] using finalAt
        exact retained query (returnedOrdinal observed.events) (aligned query observed initialAt)
    | foreign actual => exact retained query (returnedOrdinal observed.events) (aligned query observed finalAt)
    | @retire population actor engine observation world present actual =>
      by_cases same : query = actor
      · subst query
        simp only [Population.advance, Population.install, ite_true, Option.some.injEq] at finalAt
        subst observed
        simpa only [EngineState.retired] using
          retained actor (returnedOrdinal engine.events) (aligned actor engine present)
      · have initialAt : before.actors query = some observed := by
          simpa only [Population.advance, Population.install, ite_eq_right same] using finalAt
        exact retained query (returnedOrdinal observed.events) (aligned query observed initialAt)
    | nativeRetire actual => exact retained query (returnedOrdinal observed.events) (aligned query observed finalAt)

end LeanCage.Host.PrivateStreams
