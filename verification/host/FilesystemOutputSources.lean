import FilesystemOutputSources.Application

namespace LeanCage.Host.Kernel.Lowered
open Filesystem

variable {kernel : Contract} {sourceProgram : Program UInt32} {runtime : ActorRuntime kernel sourceProgram}

theorem execute_checked_borrow (laws : DescriptorContract kernel)
    (directories : DirectoryRetirementContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (actor : ActorId) (held : UInt64) (handle : Handle) (raw : handle.rawOwned = true)
    (request : GatewayWire.Request) (override : Option Nat) :
    ActorBorrowPost runtime actor held handle (fun _ => True)
      (PrimitiveFilesystem.lower (executeChecked request override).run) := by
  unfold executeChecked
  apply actor_checked_bind (pre := fun _ => True)
  · unfold checkRequest
    split <;> exact .pure True.intro
  · intro ignored _
    apply actor_checked_bind
    · exact actor_filesystem actor (load_bundle_borrow laws held handle _)
    · intro bundle _
      apply actor_checked_bind
      · exact actor_filesystem actor (check_bundle_borrow laws held handle _)
      · intro ignored _
        apply actor_checked_bind
        · exact actor_filesystem actor (running_image_borrow laws held handle _)
        · intro ignored _
          apply actor_checked_bind (pre := fun _ => True)
          · apply actor_filesystem actor
            apply borrow_bind (authentication_key_borrow laws held handle _)
            intro key _
            exact .pure True.intro
          · intro ignored _
            split
            · exact .pure True.intro
            · split
              · apply actor_checked_bind
                · exact actor_filesystem actor (policy_load_borrow laws held handle _)
                · intro rawPolicy _
                  apply actor_checked_bind
                  · exact validator_borrow laws sdk actor held handle raw bundle rawPolicy
                  · intro value _
                    exact .pure True.intro
              · split
                · exact execute_run_borrow laws directories sdk actor held handle raw _ _ _
                · split
                  · exact actor_filesystem actor (retrieval_report_borrow laws held handle _ _)
                  · exact .pure True.intro

theorem dispatch_borrow (laws : DescriptorContract kernel)
    (directories : DirectoryRetirementContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (actor : ActorId) (held : UInt64) (handle : Handle) (raw : handle.rawOwned = true)
    (request : GatewayWire.Request) (override : Option Nat) :
    ActorBorrowPost runtime actor held handle (fun _ => True)
      (PrimitiveFilesystem.lower (Commands.dispatch request override)) := by
  unfold Commands.dispatch execute
  apply actor_bind (execute_checked_borrow laws directories sdk actor held handle raw _ _)
  intro result _
  cases result <;> exact .pure True.intro

theorem cli_borrow (laws : DescriptorContract kernel)
    (directories : DirectoryRetirementContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (actor : ActorId) (held : UInt64) (handle : Handle) (raw : handle.rawOwned = true)
    (request : GatewayWire.Request) :
    ActorBorrowPost runtime actor held handle (fun _ => True) (PrimitiveFilesystem.lower (Commands.cli request)) := by
  unfold Commands.cli
  split
  · exact .pure True.intro
  · exact .pure True.intro
  · apply actor_bind (dispatch_borrow laws directories sdk actor held handle raw _ _)
    intro result _
    exact .pure True.intro

theorem commands_borrow (laws : DescriptorContract kernel)
    (directories : DirectoryRetirementContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (actor : ActorId) (held : UInt64) (handle : Handle) (raw : handle.rawOwned = true)
    (request : GatewayWire.Request) :
    ActorBorrowPost runtime actor held handle (fun _ => True) (PrimitiveFilesystem.lower (Commands.run request)) := by
  unfold Commands.run
  split
  · exact cli_borrow laws directories sdk actor held handle raw _
  · exact dispatch_borrow laws directories sdk actor held handle raw _ _

-- §FS-host-boundary.caller: The real startup/packet/command/response source retains a
-- raw inherited FD. Every temporary close is justified by its source-produced fresh FD.
theorem entrypoint_borrow (laws : DescriptorContract kernel)
    (directories : DirectoryRetirementContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (actor : ActorId) (held : UInt64) (handle : Handle) (raw : handle.rawOwned = true) :
    ActorBorrowPost runtime actor held handle (fun _ => True) (PrimitiveFilesystem.lower Entrypoint.run) := by
  unfold Entrypoint.run
  apply actor_bind (actor_filesystem actor (seal_borrow laws held handle [0, 1, 3]))
  intro ready _
  cases ready with
  | error => exact .pure True.intro
  | ok ready =>
    apply actor_bind (actor_filesystem actor (packet_read_borrow laws held handle 0))
    intro request _
    apply actor_bind (first := fun _ => True)
    · cases request with
      | error => exact .pure True.intro
      | ok request => exact commands_borrow laws directories sdk actor held handle raw _
    · intro response _
      dsimp only
      split
      · exact .pure True.intro
      · apply actor_bind (actor_filesystem actor (writeLoop_borrow laws held handle _ _ _ _))
        intro written _
        cases written <;> exact .pure True.intro

end LeanCage.Host.Kernel.Lowered

namespace LeanCage.Host.Kernel

-- §FS-host-boundary.acceptance: The current reference is derived from the SAME launch
-- and ordered source history. Later loss/retirement does not erase this earlier input fact.
theorem actual_live_inherited_reference {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (directories : DirectoryRetirementContract kernel)
    (sdk : RuntimeDescriptorContract runtime)
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    (history : SelectedActorHistory runtime initial all tick actor engine)
    (present : tick.before.actors actor = some engine) (running : engine.running = true)
    {held : UInt64} {handle : Handle} (inherited : history.launch.references held = some handle) :
    engine.references held = some handle := by
  have raw := sdk.initial_raw _ _ _ _ _ history.launch.inherited held handle inherited
  have source := Lowered.entrypoint_borrow descriptors directories sdk actor held handle raw
  have reached := selected_actor_head_for journal history.preceding history.following tick history.shape present running
  exact (selected_borrowed_reference history source reached inherited).1

-- §FS-host-boundary.acceptance: The selected operation's own output world retains the
-- inherited FD for either returned or lost observation. Later process exit remains separate.
theorem actual_inherited_operation_reference {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (directories : DirectoryRetirementContract kernel)
    (sdk : RuntimeDescriptorContract runtime)
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    (history : SelectedActorHistory runtime initial all tick actor engine)
    (present : tick.before.actors actor = some engine) (running : engine.running = true)
    {held : UInt64} {handle : Handle} (inherited : history.launch.references held = some handle)
    {β : Type} {effect : Effect β} {next : β → Program UInt32}
    (head : engine.current = .call effect next) {observed : Option β} {after : World}
    (actual : ActorOperation runtime actor effect observed (tick.before.project engine) after) :
    after.handles held = some handle := by
  have raw := sdk.initial_raw _ _ _ _ _ history.launch.inherited held handle inherited
  have source := Lowered.entrypoint_borrow descriptors directories sdk actor held handle raw
  have reached := selected_actor_head_for journal history.preceding history.following tick history.shape present running
  obtain ⟨live, residual⟩ := selected_borrowed_reference history source reached inherited
  rw [head] at residual
  cases residual with
  | call preserve following => exact preserve _ _ _ actual live

end LeanCage.Host.Kernel
