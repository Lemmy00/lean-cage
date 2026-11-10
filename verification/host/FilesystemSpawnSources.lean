import FilesystemSourceOrigins

namespace LeanCage.Host.Kernel
open Filesystem

inductive SpawnUse (arguments : IO.Process.SpawnArgs) : Program.Event → Prop where
  | returned (reply : Except String (IO.Process.Child arguments.toStdioConfig)) :
      SpawnUse arguments (.returned (.spawn arguments) reply)
  | lost : SpawnUse arguments (.lost (.spawn arguments))

private def spawnEffect {α : Type} : Effect α → Bool
  | .spawn _ => true
  | _ => false

private def spawnEvent : Program.Event → Bool
  | .returned effect _ => spawnEffect effect
  | .lost effect => spawnEffect effect

private theorem spawn_event_true {arguments : IO.Process.SpawnArgs} {event : Program.Event}
    (source : SpawnUse arguments event) : spawnEvent event = true := by
  cases source <;> rfl

private theorem filesystem_no_spawn {α : Type} (program : Filesystem.Program α)
    {before : List Program.Event} {event : Program.Event} {arguments : IO.Process.SpawnArgs}
    (active : Program.Prefix (Program.liftFilesystem program) (before ++ [event]))
    (spawn : SpawnUse arguments event) : False := by
  obtain ⟨events, source, shape⟩ := Program.lift_filesystem_prefix_source program active
  have member : event ∈ events.map Program.filesystemPrefixEvent := by rw [← shape]; simp
  obtain ⟨actual, member, same⟩ := List.mem_map.mp member
  subst event
  rcases actual with ⟨request, observed⟩
  have impossible := spawn_event_true spawn
  cases observed <;> cases impossible

private theorem observation_stream_profile {allowed : IO.Process.SpawnArgs → Prop}
    (fuel : Nat) (handle : IO.FS.Handle) (limit : Nat) (bytes : ByteArray) :
    VirtualMachine.SourceProfile allowed (readStream fuel handle limit bytes) := by
  induction fuel generalizing bytes with
  | zero => exact .pure _
  | succ fuel ih =>
    unfold readStream
    split
    · exact .pure _
    · apply VirtualMachine.SourceProfile.call (.read handle (min chunkMax (limit + 1 - bytes.size))) _ (by trivial)
      intro reply
      cases reply with
      | error => exact .pure _
      | ok bytes => repeat' first | exact .pure _ | exact ih _ | split

private theorem validator_observation_profile {allowed : IO.Process.SpawnArgs → Prop}
    (raw : ByteArray) (child : Except String Validation.ValidatorChild) :
    VirtualMachine.SourceProfile allowed (Validation.observeChild raw child) := by
  cases child with
  | error => exact .pure _
  | ok child =>
    unfold Validation.observeChild
    apply VirtualMachine.source_profile_bind (observation_stream_profile _ _ _ _)
    intro output
    apply VirtualMachine.source_profile_bind (.call (.wait child) _ (by trivial) (fun _ => .pure _))
    intro code
    exact .pure _

private theorem profile_spawn {α : Type} {program : Program α} {allowed : IO.Process.SpawnArgs → Prop}
    (profile : VirtualMachine.SourceProfile allowed program) {before : List Program.Event}
    {event : Program.Event} {arguments : IO.Process.SpawnArgs}
    (active : Program.Prefix program (before ++ [event])) (spawn : SpawnUse arguments event) : allowed arguments := by
  have selected := VirtualMachine.source_profile_prefix profile active event (by simp)
  cases spawn <;> exact selected

-- §FS-host-boundary.ownership: Child roles retain their actual earlier allocation and fixed args.
inductive SpawnRole (bundle : Validation.Bundle) (arguments : IO.Process.SpawnArgs) (before : List Program.Event) (event : Program.Event) : Type 1 where
  | validator (raw : ByteArray) (context : ValidatorPrefixCuts.Written raw)
      (outside inside : List Program.Event)
      (active : Program.Prefix (context.allocated.spawnProgram bundle) (inside ++ [event]))
      (trace : before = outside ++ context.events ++ inside)
      (argumentSource : arguments = Validation.validatorArguments bundle (context.allocated.directory.path ++ "/policy.json"))
  | vm (request : GatewayWire.Request) (override : Option Nat)
      (context : RunPrefixCuts.Imaged request bundle override) (outside inside : List Program.Event)
      (active : Program.Prefix context.dispatchProgram (inside ++ [event]))
      (trace : before = outside ++ context.events ++ inside)
      (argumentSource : arguments = VirtualMachine.arguments bundle context.allocated.directory.path)

def prepend_spawn_role {bundle : Validation.Bundle} {arguments : IO.Process.SpawnArgs} {before : List Program.Event} {event : Program.Event}
    (leading : List Program.Event) (source : SpawnRole bundle arguments before event) :
    SpawnRole bundle arguments (leading ++ before) event := by
  cases source with
  | validator raw context outside inside active trace argumentSource =>
    exact .validator raw context (leading ++ outside) inside active
      (by simpa only [List.append_assoc] using congrArg (leading ++ ·) trace) argumentSource
  | vm request override context outside inside active trace argumentSource =>
    exact .vm request override context (leading ++ outside) inside active
      (by simpa only [List.append_assoc] using congrArg (leading ++ ·) trace) argumentSource

theorem validator_spawn_source (bundle : Validation.Bundle) (raw : ByteArray)
    {before : List Program.Event} {event : Program.Event} {arguments : IO.Process.SpawnArgs}
    (active : Program.Prefix (Validation.validateCopied bundle raw) (before ++ [event]))
    (spawn : SpawnUse arguments event) : Nonempty (SpawnRole bundle arguments before event) := by
  obtain ⟨cut⟩ := ValidatorPrefixCuts.validate_copied_cut bundle raw active
  cases cut with
  | allocating selected => exact False.elim (filesystem_no_spawn _ selected spawn)
  | writing context inside selected trace => exact False.elim (filesystem_no_spawn _ selected spawn)
  | spawning context inside selected trace =>
    have argumentSource := profile_spawn
      (allowed := fun args => args = Validation.validatorArguments bundle (context.allocated.directory.path ++ "/policy.json"))
      (.call (.spawn (Validation.validatorArguments bundle (context.allocated.directory.path ++ "/policy.json")))
        _ rfl (fun _ => .pure _)) selected spawn
    exact ⟨.validator raw context [] inside selected (by simpa using trace) argumentSource⟩
  | observing context inside selected trace =>
    exact False.elim (profile_spawn (validator_observation_profile (allowed := fun _ => False) _ _) selected spawn)
  | cleaningFailedWrite context writing error written inside selected trace =>
    exact False.elim (filesystem_no_spawn _ selected spawn)
  | cleaningObserved context inside reaped selected trace => exact False.elim (filesystem_no_spawn _ selected spawn)
  | releasingUnknown context inside unknown selected trace => exact False.elim (filesystem_no_spawn _ selected spawn)

theorem preparation_spawn_source (request : GatewayWire.Request) (bundle : Validation.Bundle)
    {before : List Program.Event} {event : Program.Event} {arguments : IO.Process.SpawnArgs}
    (active : Program.Prefix (preparePolicy request bundle).run (before ++ [event]))
    (spawn : SpawnUse arguments event) : Nonempty (SpawnRole bundle arguments before event) := by
  obtain ⟨cut⟩ := PreparationPrefixCuts.prepare_policy_cut request bundle active
  cases cut with
  | loading selected => exact False.elim (filesystem_no_spawn _ selected spawn)
  | validating context inside selected trace =>
    obtain ⟨source⟩ := validator_spawn_source bundle context.raw selected spawn
    exact ⟨trace ▸ prepend_spawn_role context.events source⟩
  | copying context inside selected trace => exact False.elim (filesystem_no_spawn _ selected spawn)
  | revalidating context inside selected trace =>
    obtain ⟨source⟩ := validator_spawn_source bundle context.policy.raw selected spawn
    exact ⟨trace ▸ prepend_spawn_role context.events source⟩

theorem dispatch_spawn_arguments (identity : String) (bundle : Validation.Bundle) (preflight : Bool)
    (policy : Policy.Accepted) (run : RunDirectory.Owned) (duration : Nat)
    (transport : Transport.State) (image : Result Unit) {before : List Program.Event}
    {event : Program.Event} {arguments : IO.Process.SpawnArgs}
    (active : Program.Prefix (dispatchImage identity bundle preflight policy run duration transport image)
      (before ++ [event])) (spawn : SpawnUse arguments event) :
    arguments = VirtualMachine.arguments bundle run.path := by
  cases image with
  | error error => exact False.elim (Program.pure_has_no_last _ _ _ active)
  | ok image =>
    unfold dispatchImage at active
    rcases Program.last_bind_split _ _ active with running |
        ⟨running, result, inside, ran, following, shape⟩
    · have source := VirtualMachine.actual_prefix_spawn_arguments _ _ _ _ running event (by simp)
      cases spawn <;> exact source
    · exact False.elim (filesystem_no_spawn _ following spawn)

private theorem cleanup_no_spawn (run : RunDirectory.Owned) (input : Publication.Input)
    {before : List Program.Event} {event : Program.Event} {arguments : IO.Process.SpawnArgs}
    (active : Program.Prefix (cleanupRun run input) (before ++ [event])) (spawn : SpawnUse arguments event) : False := by
  unfold cleanupRun at active
  split at active
  · rcases Program.last_bind_split _ _ active with first |
        ⟨first, result, inside, returned, following, shape⟩
    · exact filesystem_no_spawn _ first spawn
    · rcases Program.last_bind_split _ _ following with second |
          ⟨second, value, last, returned, ending, shape⟩
      · exact filesystem_no_spawn _ second spawn
      · exact Program.pure_has_no_last _ _ _ ending
  · exact filesystem_no_spawn _ active spawn

theorem run_spawn_source (request : GatewayWire.Request) (bundle : Validation.Bundle) (override : Option Nat)
    {before : List Program.Event} {event : Program.Event} {arguments : IO.Process.SpawnArgs}
    (active : Program.Prefix (executeRun request bundle override).run (before ++ [event]))
    (spawn : SpawnUse arguments event) : Nonempty (SpawnRole bundle arguments before event) := by
  obtain ⟨cut⟩ := RunPrefixCuts.execute_run_cut request bundle override active
  cases cut with
  | preparing selected => exact preparation_spawn_source request bundle selected spawn
  | randomizing policy frozen preparing inside prepare selected trace => exact False.elim (filesystem_no_spawn _ selected spawn)
  | allocating context inside selected trace => exact False.elim (filesystem_no_spawn _ selected spawn)
  | imaging context inside selected trace => exact False.elim (filesystem_no_spawn _ selected spawn)
  | dispatching context inside selected trace =>
    exact ⟨.vm request override context [] inside selected (by simpa using trace)
      (dispatch_spawn_arguments _ _ _ _ _ _ _ _ selected spawn)⟩
  | cleaning context inside selected trace => exact False.elim (cleanup_no_spawn _ _ selected spawn)
  | publishing context inside selected trace => exact False.elim (filesystem_no_spawn _ selected spawn)

structure CallerSpawn (request : GatewayWire.Request) (duration : Option Nat)
    (before : List Program.Event) (arguments : IO.Process.SpawnArgs) (event : Program.Event) where
  context : CallerPrefixCuts.Authenticated request
  afterGate : List Program.Event
  gate : before = context.events ++ afterGate
  role : SpawnRole context.bundle arguments before event

theorem caller_spawn_source (request : GatewayWire.Request) (duration : Option Nat)
    {before : List Program.Event} {event : Program.Event} {arguments : IO.Process.SpawnArgs}
    (active : Program.Prefix (execute request duration) (before ++ [event])) (spawn : SpawnUse arguments event) :
    Nonempty (CallerSpawn request duration before arguments event) := by
  obtain ⟨cut⟩ := CallerPrefixCuts.execute_checked_cut request duration active
  cases cut with
  | selecting selected => exact False.elim (filesystem_no_spawn _ selected spawn)
  | checking context inside selected trace => exact False.elim (filesystem_no_spawn _ selected spawn)
  | identifying context inside selected trace => exact False.elim (filesystem_no_spawn _ selected spawn)
  | authenticating context inside selected trace => exact False.elim (filesystem_no_spawn _ selected spawn)
  | loadingPolicy context inside selected trace => exact False.elim (filesystem_no_spawn _ selected spawn)
  | validating context raw loading loaded inside selected trace =>
    obtain ⟨source⟩ := validator_spawn_source context.bundle raw selected spawn
    refine ⟨⟨context, loading.map Program.filesystemEvent ++ inside, ?_, ?_⟩⟩
    · simpa only [List.append_assoc] using trace
    · exact trace ▸ prepend_spawn_role (context.events ++ loading.map Program.filesystemEvent) source
  | executing context inside command selected trace =>
    obtain ⟨source⟩ := run_spawn_source request context.bundle duration selected spawn
    exact ⟨⟨context, inside, trace, trace ▸ prepend_spawn_role context.events source⟩⟩
  | retrieving context inside command selected trace => exact False.elim (filesystem_no_spawn _ selected spawn)

structure EntrySpawn (before : List Program.Event) (arguments : IO.Process.SpawnArgs) (event : Program.Event) where
  packet : EntrypointPrefixCuts.Read
  original : GatewayWire.Request
  effective : GatewayWire.Request
  duration : Option Nat
  accepted : packet.packet = .ok original
  invocation : Commands.Invocation original effective duration
  inside : List Program.Event
  caller : CallerSpawn effective duration inside arguments event
  trace : before = packet.events ++ inside

-- §FS-host-boundary.caller: Actual packet/CLI interpretation supplies each child process role.
theorem entrypoint_spawn_source {before : List Program.Event} {event : Program.Event} {arguments : IO.Process.SpawnArgs}
    (active : Program.Prefix Entrypoint.run (before ++ [event])) (spawn : SpawnUse arguments event) :
    Nonempty (EntrySpawn before arguments event) := by
  obtain ⟨cut⟩ := EntrypointPrefixCuts.entrypoint_cut active
  cases cut with
  | starting selected => exact False.elim (filesystem_no_spawn _ selected spawn)
  | reading context inside selected trace => exact False.elim (filesystem_no_spawn _ selected spawn)
  | responding context inside selected trace =>
    obtain ⟨original, packet, command⟩ := EntrypointPrefixCuts.packet_response_prefix selected
    obtain ⟨effective, duration, invocation, executed⟩ := Commands.run_prefix_source original command
    obtain ⟨source⟩ := caller_spawn_source effective duration executed spawn
    exact ⟨⟨context, original, effective, duration, packet, invocation, inside, source, trace⟩⟩
  | writing context inside bound selected trace => exact False.elim (filesystem_no_spawn _ selected spawn)

theorem selected_spawn_source {kernel : Contract} {runtime : ActorRuntime kernel}
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {event : Program.Event} {arguments : IO.Process.SpawnArgs}
    (selected : ticks[position]? = some tick) (action : tick.action.eventFor actor = some event)
    (present : tick.before.actors actor = some engine) (spawn : SpawnUse arguments event) :
    Nonempty (EntrySpawn engine.events arguments event) :=
  entrypoint_spawn_source (selected_source_prefix journal selected action present) spawn

end LeanCage.Host.Kernel
