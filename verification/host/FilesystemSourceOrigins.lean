import FilesystemSourceKinds

namespace LeanCage.Host.Kernel
open Filesystem

private theorem filesystem_prefix_event_injective (first last : Request × Option Reply)
    (same : Program.filesystemPrefixEvent first = Program.filesystemPrefixEvent last) : first = last := by
  rcases first with ⟨first, firstReply⟩
  rcases last with ⟨last, lastReply⟩
  cases firstReply <;> cases lastReply <;> cases same <;> rfl

theorem selected_filesystem_source {α : Type} {program : Filesystem.Program α}
    {before : List Program.Event} {request : Request} {observed : Option Reply}
    (active : Program.Prefix (Program.liftFilesystem program)
      (before ++ [Program.filesystemPrefixEvent (request, observed)])) :
    ∃ earlier, Prefix program (earlier ++ [(request, observed)]) ∧
      before = earlier.map Program.filesystemPrefixEvent := by
  obtain ⟨events, source, shape⟩ := Program.lift_filesystem_prefix_source _ active
  rcases List.eq_nil_or_concat events with empty | ⟨earlier, event, eventShape⟩
  · subst events
    have length := congrArg List.length shape
    simp only [List.length_append, List.length_singleton, List.map_nil, List.length_nil] at length
    omega
  · rw [List.concat_eq_append] at eventShape
    rw [eventShape, List.map_append, List.map_singleton] at shape
    have concatenated : List.concat before (Program.filesystemPrefixEvent (request, observed)) =
        List.concat (earlier.map Program.filesystemPrefixEvent) (Program.filesystemPrefixEvent event) := by
      simpa only [List.concat_eq_append] using shape
    have same := List.of_concat_eq_concat concatenated
    have sameEvent := filesystem_prefix_event_injective _ _ same.2.symm
    subst event
    exact ⟨earlier, eventShape ▸ source, same.1⟩

-- §FS-host-boundary.acceptance: Inspect this same selected request, including a lost last reply.
theorem selected_filesystem_profile {α : Type} {program : Filesystem.Program α} {allowed : Request → Prop}
    (profile : RequestProgram allowed program) {before : List Program.Event} {request : Request}
    {observed : Option Reply}
    (active : Program.Prefix (Program.liftFilesystem program)
      (before ++ [Program.filesystemPrefixEvent (request, observed)])) : allowed request := by
  obtain ⟨events, source, shape⟩ := Program.lift_filesystem_prefix_source _ active
  have member : Program.filesystemPrefixEvent (request, observed) ∈ events.map Program.filesystemPrefixEvent := by
    rw [← shape]
    simp
  obtain ⟨event, occurs, same⟩ := List.mem_map.mp member
  have sameEvent := filesystem_prefix_event_injective _ _ same
  subst event
  exact request_prefix profile source (request, observed) occurs

inductive CallerMutation (request : GatewayWire.Request) (duration : Option Nat)
    (before : List Program.Event) (event : Program.Event) : Type 1 where
  | validating (context : CallerPrefixCuts.Authenticated request) (raw : ByteArray)
      (loading : List (Request × Reply))
      (load : Returns (Validation.loadPolicy request) loading (.ok raw)) (inside : List Program.Event)
      (active : Program.Prefix (Validation.validateCopied context.bundle raw) (inside ++ [event]))
      (trace : before = context.events ++ loading.map Program.filesystemEvent ++ inside)
  | executing (context : CallerPrefixCuts.Authenticated request) (inside : List Program.Event)
      (command : request.command = GatewayWire.runCommand ∨ request.command = GatewayWire.checkCommand)
      (active : Program.Prefix (executeRun request context.bundle duration).run (inside ++ [event]))
      (trace : before = context.events ++ inside)

-- §FS-host-boundary.ownership: Bootstrap, policy loading and retrieval cannot supply a mutation.
theorem caller_mutation_origin (request : GatewayWire.Request) (duration : Option Nat)
    {before : List Program.Event} {operation : Request} {observed : Option Reply}
    (active : Program.Prefix (execute request duration)
      (before ++ [Program.filesystemPrefixEvent (operation, observed)]))
    (mutating : ¬ NamespacePassive operation) :
    Nonempty (CallerMutation request duration before (Program.filesystemPrefixEvent (operation, observed))) := by
  obtain ⟨cut⟩ := CallerPrefixCuts.execute_checked_cut request duration active
  cases cut with
  | selecting selected =>
    exact False.elim (mutating (selected_filesystem_profile (load_bundle_namespace_passive _) selected))
  | checking context inside selected trace =>
    exact False.elim (mutating (selected_filesystem_profile (check_bundle_namespace_passive _) selected))
  | identifying context inside selected trace =>
    exact False.elim (mutating (selected_filesystem_profile (engine_identity_namespace_passive _) selected))
  | authenticating context inside selected trace =>
    exact False.elim (mutating (selected_filesystem_profile (key_gate_namespace_passive _) selected))
  | loadingPolicy context inside selected trace =>
    exact False.elim (mutating (selected_filesystem_profile (load_policy_namespace_passive _) selected))
  | validating context raw loading loaded inside selected trace =>
    exact ⟨.validating context raw loading loaded inside selected trace⟩
  | executing context inside command selected trace => exact ⟨.executing context inside command selected trace⟩
  | retrieving context inside command selected trace =>
    exact False.elim (mutating (selected_filesystem_profile
      (read_only_namespace_passive (Retrieval.report_readOnly _ _)) selected))

structure EntryMutation (before : List Program.Event) (event : Program.Event) where
  packet : EntrypointPrefixCuts.Read
  original : GatewayWire.Request
  effective : GatewayWire.Request
  duration : Option Nat
  accepted : packet.packet = .ok original
  invocation : Commands.Invocation original effective duration
  inside : List Program.Event
  source : CallerMutation effective duration inside event
  trace : before = packet.events ++ inside

-- §FS-host-boundary.caller: Actual packet/CLI interpretation and key gates precede each mutation.
theorem entrypoint_mutation_origin {before : List Program.Event} {operation : Request} {observed : Option Reply}
    (active : Program.Prefix Entrypoint.run
      (before ++ [Program.filesystemPrefixEvent (operation, observed)]))
    (mutating : ¬ NamespacePassive operation) :
    Nonempty (EntryMutation before (Program.filesystemPrefixEvent (operation, observed))) := by
  obtain ⟨cut⟩ := EntrypointPrefixCuts.entrypoint_cut active
  cases cut with
  | starting selected =>
    exact False.elim (mutating (selected_filesystem_profile (seal_namespace_passive [0, 1, 3]) selected))
  | reading context inside selected trace =>
    exact False.elim (mutating (selected_filesystem_profile (packet_namespace_passive _) selected))
  | responding context inside selected trace =>
    obtain ⟨original, packet, command⟩ := EntrypointPrefixCuts.packet_response_prefix selected
    obtain ⟨effective, duration, invocation, executed⟩ := Commands.run_prefix_source original command
    obtain ⟨source⟩ := caller_mutation_origin effective duration executed mutating
    exact ⟨⟨context, original, effective, duration, packet, invocation, inside, source, trace⟩⟩
  | writing context inside bound selected trace =>
    exact False.elim (mutating (selected_filesystem_profile (write_loop_namespace_passive _ _ _ _) selected))

-- §FS-host-boundary.acceptance: No free source-phase label is supplied at the physical boundary.
theorem selected_namespace_origin {kernel : Contract} {runtime : ActorRuntime kernel}
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply}
    (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) (mutating : ¬ NamespacePassive request) :
    Nonempty (EntryMutation engine.events (Program.filesystemPrefixEvent (request, observed))) :=
  entrypoint_mutation_origin (selected_source_prefix journal selected action present) mutating

private theorem runtime_only_no_filesystem {α : Type} {program : Program α}
    (profile : Program.RuntimeOnly program) {before : List Program.Event} {request : Request}
    {observed : Option Reply}
    (active : Program.Prefix program (before ++ [Program.filesystemPrefixEvent (request, observed)])) : False := by
  have selected := Program.runtime_only_prefix profile active (Program.filesystemPrefixEvent (request, observed))
    (by simp)
  cases observed <;> exact selected

inductive ValidatorMutation (bundle : Validation.Bundle) (raw : ByteArray)
    (before : List Program.Event) (event : Program.Event) : Type 1 where
  | allocating (active : Program.Prefix (Program.liftFilesystem RunDirectory.create) (before ++ [event]))
  | writing (context : ValidatorPrefixCuts.Allocated) (inside : List Program.Event)
      (active : Program.Prefix (Program.liftFilesystem (context.writeProgram raw)) (inside ++ [event]))
      (trace : before = context.events ++ inside)
  | cleaningFailedWrite (context : ValidatorPrefixCuts.Allocated) (writing : List (Request × Reply)) (error : Failure)
      (written : Returns (context.writeProgram raw) writing (.error error)) (inside : List Program.Event)
      (active : Program.Prefix (Program.liftFilesystem (RunDirectory.cleanup context.directory)) (inside ++ [event]))
      (trace : before = context.events ++ writing.map Program.filesystemEvent ++ inside)
  | cleaningObserved (context : ValidatorPrefixCuts.Observed bundle raw) (inside : List Program.Event)
      (reaped : context.result.reaped = true)
      (active : Program.Prefix (Program.liftFilesystem
        (RunDirectory.cleanup context.spawned.written.allocated.directory)) (inside ++ [event]))
      (trace : before = context.events ++ inside)
  | releasingUnknown (context : ValidatorPrefixCuts.Observed bundle raw) (inside : List Program.Event)
      (unknown : context.result.reaped = false)
      (active : Program.Prefix (Program.liftFilesystem
        (Validation.releaseDirectory context.spawned.written.allocated.directory)) (inside ++ [event]))
      (trace : before = context.events ++ inside)

theorem validator_mutation_origin (bundle : Validation.Bundle) (raw : ByteArray)
    {before : List Program.Event} {operation : Request} {observed : Option Reply}
    (active : Program.Prefix (Validation.validateCopied bundle raw)
      (before ++ [Program.filesystemPrefixEvent (operation, observed)])) :
    Nonempty (ValidatorMutation bundle raw before (Program.filesystemPrefixEvent (operation, observed))) := by
  obtain ⟨cut⟩ := ValidatorPrefixCuts.validate_copied_cut bundle raw active
  cases cut with
  | allocating selected => exact ⟨.allocating selected⟩
  | writing context inside selected trace => exact ⟨.writing context inside selected trace⟩
  | spawning context inside selected trace =>
    exact False.elim (runtime_only_no_filesystem
      (.call (.spawn (Validation.validatorArguments bundle (context.allocated.directory.path ++ "/policy.json")))
        _ trivial (fun _ => .pure _)) selected)
  | observing context inside selected trace =>
    exact False.elim (runtime_only_no_filesystem (observe_child_runtime_only _ _) selected)
  | cleaningFailedWrite context writing error written inside selected trace =>
    exact ⟨.cleaningFailedWrite context writing error written inside selected trace⟩
  | cleaningObserved context inside reaped selected trace => exact ⟨.cleaningObserved context inside reaped selected trace⟩
  | releasingUnknown context inside unknown selected trace =>
    exact ⟨.releasingUnknown context inside unknown selected trace⟩

inductive PreparationMutation (request : GatewayWire.Request) (bundle : Validation.Bundle)
    (before : List Program.Event) (event : Program.Event) : Type 1 where
  | validating (context : PreparationPrefixCuts.Loaded request) (inside : List Program.Event)
      (source : ValidatorMutation bundle context.raw inside event)
      (trace : before = context.events ++ inside)
  | revalidating (context : PreparationPrefixCuts.Bound request bundle) (inside : List Program.Event)
      (source : ValidatorMutation bundle context.policy.raw inside event)
      (trace : before = context.events ++ inside)

theorem preparation_mutation_origin (request : GatewayWire.Request) (bundle : Validation.Bundle)
    {before : List Program.Event} {operation : Request} {observed : Option Reply}
    (active : Program.Prefix (preparePolicy request bundle).run
      (before ++ [Program.filesystemPrefixEvent (operation, observed)]))
    (mutating : ¬ NamespacePassive operation) :
    Nonempty (PreparationMutation request bundle before (Program.filesystemPrefixEvent (operation, observed))) := by
  obtain ⟨cut⟩ := PreparationPrefixCuts.prepare_policy_cut request bundle active
  cases cut with
  | loading selected =>
    exact False.elim (mutating (selected_filesystem_profile (load_policy_namespace_passive _) selected))
  | validating context inside selected trace =>
    obtain ⟨source⟩ := validator_mutation_origin bundle context.raw selected
    exact ⟨.validating context inside source trace⟩
  | copying context inside selected trace =>
    exact False.elim (mutating (selected_filesystem_profile
      (input_namespace_passive (Snapshot.freeze_input _ _ _)) selected))
  | revalidating context inside selected trace =>
    obtain ⟨source⟩ := validator_mutation_origin bundle context.policy.raw selected
    exact ⟨.revalidating context inside source trace⟩

inductive RunMutation (request : GatewayWire.Request) (bundle : Validation.Bundle) (override : Option Nat)
    (before : List Program.Event) (event : Program.Event) : Type 1 where
  | preparing (source : PreparationMutation request bundle before event)
  | allocating (context : RunPrefixCuts.Setup request bundle override) (inside : List Program.Event)
      (active : Program.Prefix (Program.liftFilesystem RunDirectory.create) (inside ++ [event]))
      (trace : before = context.events ++ inside)
  | imaging (context : RunPrefixCuts.Allocated request bundle override) (inside : List Program.Event)
      (active : Program.Prefix (Program.liftFilesystem context.imageProgram) (inside ++ [event]))
      (trace : before = context.events ++ inside)
  | dispatching (context : RunPrefixCuts.Imaged request bundle override) (inside : List Program.Event)
      (active : Program.Prefix context.dispatchProgram (inside ++ [event]))
      (trace : before = context.events ++ inside)
  | cleaning (context : RunPrefixCuts.Dispatched request bundle override) (inside : List Program.Event)
      (active : Program.Prefix (cleanupRun context.imaged.allocated.directory context.input) (inside ++ [event]))
      (trace : before = context.events ++ inside)
  | publishing (context : RunPrefixCuts.Cleaned request bundle override) (inside : List Program.Event)
      (active : Program.Prefix (Program.liftFilesystem
        (Publication.publish request bundle context.dispatched.input)) (inside ++ [event]))
      (trace : before = context.events ++ inside)

theorem run_mutation_origin (request : GatewayWire.Request) (bundle : Validation.Bundle) (override : Option Nat)
    {before : List Program.Event} {operation : Request} {observed : Option Reply}
    (active : Program.Prefix (executeRun request bundle override).run
      (before ++ [Program.filesystemPrefixEvent (operation, observed)]))
    (mutating : ¬ NamespacePassive operation) :
    Nonempty (RunMutation request bundle override before (Program.filesystemPrefixEvent (operation, observed))) := by
  obtain ⟨cut⟩ := RunPrefixCuts.execute_run_cut request bundle override active
  cases cut with
  | preparing selected =>
    obtain ⟨source⟩ := preparation_mutation_origin request bundle selected mutating
    exact ⟨.preparing source⟩
  | randomizing policy frozen preparing inside prepare selected trace =>
    exact False.elim (mutating (selected_filesystem_profile (random_namespace_passive _ _ _) selected))
  | allocating context inside selected trace => exact ⟨.allocating context inside selected trace⟩
  | imaging context inside selected trace => exact ⟨.imaging context inside selected trace⟩
  | dispatching context inside selected trace => exact ⟨.dispatching context inside selected trace⟩
  | cleaning context inside selected trace => exact ⟨.cleaning context inside selected trace⟩
  | publishing context inside selected trace => exact ⟨.publishing context inside selected trace⟩

theorem vm_namespace_passive (bundle : Validation.Bundle) (directory : String) (duration : Nat)
    (transport : Transport.State) {before : List Program.Event} {request : Request} {observed : Option Reply}
    (active : Program.Prefix (VirtualMachine.run bundle directory duration transport)
      (before ++ [Program.filesystemPrefixEvent (request, observed)])) : NamespacePassive request := by
  have bounded := VirtualMachine.actual_prefix_read_bounds bundle directory duration transport active
    (Program.filesystemPrefixEvent (request, observed)) (by simp)
  cases observed <;> exact bounded.2

-- §FS-host-boundary.ownership: VM/control and artifact validation emit no namespace mutation.
theorem dispatch_namespace_passive (identity : String) (bundle : Validation.Bundle) (preflight : Bool)
    (policy : Policy.Accepted) (run : RunDirectory.Owned) (duration : Nat)
    (transport : Transport.State) (image : Result Unit) {before : List Program.Event}
    {request : Request} {observed : Option Reply}
    (active : Program.Prefix (dispatchImage identity bundle preflight policy run duration transport image)
      (before ++ [Program.filesystemPrefixEvent (request, observed)])) : NamespacePassive request := by
  cases image with
  | error error => exact False.elim (Program.pure_has_no_last _ _ _ active)
  | ok image =>
    unfold dispatchImage at active
    rcases Program.last_bind_split _ _ active with running |
        ⟨running, result, inside, ran, following, shape⟩
    · exact vm_namespace_passive _ _ _ _ running
    · exact selected_filesystem_profile
        (read_only_namespace_passive (Retrieval.readOnly_hashOnly (ReceiveProofs.receive_hashOnly _ _ _ _ _))) following

theorem cleanup_no_rename (run : RunDirectory.Owned) (input : Publication.Input)
    {before : List Program.Event} {request : Request} {observed : Option Reply}
    (active : Program.Prefix (cleanupRun run input)
      (before ++ [Program.filesystemPrefixEvent (request, observed)])) : request.op ≠ .renameNew := by
  unfold cleanupRun at active
  split at active
  · rcases Program.last_bind_split _ _ active with first |
        ⟨first, result, inside, returned, following, shape⟩
    · exact selected_filesystem_profile (allowed := fun request => request.op ≠ .renameNew)
        (.call (by change Op.close ≠ Op.renameNew; decide) (fun _ => .pure _)) first
    · rcases Program.last_bind_split _ _ following with second |
          ⟨second, value, last, returned, ending, shape⟩
      · exact selected_filesystem_profile (allowed := fun request => request.op ≠ .renameNew)
          (.call (by change Op.close ≠ Op.renameNew; decide) (fun _ => .pure _)) second
      · exact False.elim (Program.pure_has_no_last _ _ _ ending)
  · exact selected_filesystem_profile (run_cleanup_no_rename run) active

theorem validator_mutation_no_rename {bundle : Validation.Bundle} {raw : ByteArray}
    {before : List Program.Event} {request : Request} {observed : Option Reply}
    (source : ValidatorMutation bundle raw before (Program.filesystemPrefixEvent (request, observed))) :
    request.op ≠ .renameNew := by
  cases source with
  | allocating active => exact selected_filesystem_profile run_create_no_rename active
  | writing context inside active trace =>
    exact selected_filesystem_profile (safe_program_no_rename (Publication.writeNew_safe _ _ _ _)) active
  | cleaningFailedWrite context writing error written inside active trace =>
    exact selected_filesystem_profile (run_cleanup_no_rename _) active
  | cleaningObserved context inside reaped active trace => exact selected_filesystem_profile (run_cleanup_no_rename _) active
  | releasingUnknown context inside unknown active trace =>
    exact namespace_passive_no_rename _ (selected_filesystem_profile (validator_release_passive _) active)

structure RunPublicationCall (request : GatewayWire.Request) (bundle : Validation.Bundle) (override : Option Nat)
    (before : List Program.Event) (event : Program.Event) where
  context : RunPrefixCuts.Cleaned request bundle override
  inside : List Program.Event
  active : Program.Prefix (Program.liftFilesystem
    (Publication.publish request bundle context.dispatched.input)) (inside ++ [event])
  trace : before = context.events ++ inside

theorem run_rename_publication (request : GatewayWire.Request) (bundle : Validation.Bundle) (override : Option Nat)
    {before : List Program.Event} {operation : Request} {observed : Option Reply}
    (active : Program.Prefix (executeRun request bundle override).run
      (before ++ [Program.filesystemPrefixEvent (operation, observed)])) (rename : operation.op = .renameNew) :
    Nonempty (RunPublicationCall request bundle override before (Program.filesystemPrefixEvent (operation, observed))) := by
  have mutating : ¬ NamespacePassive operation := by
    intro passive
    exact namespace_passive_no_rename operation passive rename
  obtain ⟨source⟩ := run_mutation_origin request bundle override active mutating
  cases source with
  | preparing source =>
    cases source with
    | validating context inside source trace => exact False.elim (validator_mutation_no_rename source rename)
    | revalidating context inside source trace => exact False.elim (validator_mutation_no_rename source rename)
  | allocating context inside active trace => exact False.elim (selected_filesystem_profile run_create_no_rename active rename)
  | imaging context inside active trace => exact False.elim (selected_filesystem_profile (image_no_rename _ _ _) active rename)
  | dispatching context inside active trace =>
    exact False.elim (mutating (dispatch_namespace_passive _ _ _ _ _ _ _ _ active))
  | cleaning context inside active trace => exact False.elim (cleanup_no_rename _ _ active rename)
  | publishing context inside active trace => exact ⟨⟨context, inside, active, trace⟩⟩

structure EntryPublicationCall (before : List Program.Event) (event : Program.Event) where
  packet : EntrypointPrefixCuts.Read
  original : GatewayWire.Request
  effective : GatewayWire.Request
  duration : Option Nat
  accepted : packet.packet = .ok original
  invocation : Commands.Invocation original effective duration
  authenticated : CallerPrefixCuts.Authenticated effective
  command : effective.command = GatewayWire.runCommand ∨ effective.command = GatewayWire.checkCommand
  runBefore : List Program.Event
  run : RunPublicationCall effective authenticated.bundle duration runBefore event
  trace : before = packet.events ++ authenticated.events ++ runBefore

-- §FS-host-boundary.publication: The only actual rename is this authenticated request's commit.
theorem entrypoint_rename_publication {before : List Program.Event} {operation : Request} {observed : Option Reply}
    (active : Program.Prefix Entrypoint.run (before ++ [Program.filesystemPrefixEvent (operation, observed)]))
    (rename : operation.op = .renameNew) :
    Nonempty (EntryPublicationCall before (Program.filesystemPrefixEvent (operation, observed))) := by
  obtain ⟨entry⟩ := entrypoint_mutation_origin active (fun passive => namespace_passive_no_rename operation passive rename)
  have source := entry.source
  cases source with
  | validating context raw loading loaded inside active trace =>
    obtain ⟨source⟩ := validator_mutation_origin _ _ active
    exact False.elim (validator_mutation_no_rename source rename)
  | executing context inside command active trace =>
    obtain ⟨run⟩ := run_rename_publication _ _ _ active rename
    exact ⟨⟨entry.packet, entry.original, entry.effective, entry.duration, entry.accepted, entry.invocation,
      context, command, inside, run, by
        simpa only [List.append_assoc] using (entry.trace.trans (congrArg (entry.packet.events ++ ·) trace))⟩⟩

end LeanCage.Host.Kernel
