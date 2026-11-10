import ControllerValidation
import FilesystemProcesses

namespace LeanCage.Application.ControllerFilesystem
open LeanCageM3

-- §AR-host-boundary.coverage: This is the actual shared reader interpreted by the child.
theorem actual_metadata_interpreter (path : System.FilePath) :
    LeanCageM3.readBounded path 65536 = (do
      let inspected ← (do
        return Metadata.inspection (← (Metadata.bounded path.toString 65536).interpret
          (m := BaseIO) Metadata.call) : IO (Except IO.Error ByteArray))
      match inspected with
      | .ok bytes => pure bytes
      | .error error => throw error) := rfl

-- §FS-host-boundary.caller: The same host-selected argv reaches only the validation command.
theorem actual_spawned_validator (bundle : LeanCage.Host.Validation.Bundle) (path : String)
    (arguments : IO.Process.SpawnArgs)
    (source : arguments = LeanCage.Host.Validation.validatorArguments bundle path) :
    _root_.main arguments.args.toList = ControllerValidation.validationOnly path := by
  subst arguments
  exact ControllerValidation.actual_validator_command path

def Allowed (path : String) (request : Metadata.Request) : Prop :=
  match request.op with
  | .open => request.path = path ∧ request.fd = 0 ∧ request.amount = 0
  | .read => request.path = "" ∧ request.fd.toNat ≤ 2147483647 ∧
      0 < request.amount.toNat ∧ request.amount.toNat ≤ 4096
  | .close => request.path = "" ∧ request.fd.toNat ≤ 2147483647 ∧ request.amount = 0

inductive Profile (path : String) {α : Type} : Metadata.Program α → Prop where
  | pure (value : α) : Profile path (.pure value)
  | call {request : Metadata.Request} {next : Metadata.Reply → Metadata.Program α}
      (allowed : Allowed path request) (following : ∀ reply, Profile path (next reply)) :
      Profile path (.call request next)

private theorem profile_bind {α β : Type} {path : String} {program : Metadata.Program α}
    {next : α → Metadata.Program β} (source : Profile path program)
    (later : ∀ value, Profile path (next value)) : Profile path (program.bind next) := by
  induction source with
  | pure => exact later _
  | call allowed following ih => exact .call allowed ih

theorem loop_profile (fuel : Nat) (path : String) (fd : UInt32) (limit : Nat) (bytes : ByteArray)
    (fits : fd.toNat ≤ 2147483647) : Profile path (Metadata.loop fuel path fd limit bytes) := by
  induction fuel generalizing bytes with
  | zero => unfold Metadata.loop; split <;> exact .pure _
  | succ fuel ih =>
    unfold Metadata.loop
    split
    · exact .pure _
    · rename_i bounded
      apply Profile.call
      · refine ⟨rfl, fits, ?_, ?_⟩
        all_goals
          have upper : Metadata.readAmount limit bytes.size ≤ 4096 := Nat.min_le_left _ _
          have positive : 0 < Metadata.readAmount limit bytes.size := by
            unfold Metadata.readAmount
            apply Nat.lt_min.mpr
            constructor
            · decide
            · omega
          have word : Metadata.readAmount limit bytes.size < 2 ^ 64 := by omega
          simpa only [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt word] using
            (by assumption)
      · intro reply
        repeat' first | exact .pure _ | exact ih _ | split

theorem finish_profile (path : String) (fd : UInt32) (result : Metadata.Result)
    (fits : fd.toNat ≤ 2147483647) : Profile path (Metadata.finish path fd result) := by
  unfold Metadata.finish
  apply Profile.call
  · exact ⟨rfl, fits, rfl⟩
  · intro reply
    cases result with
    | error => exact .pure _
    | ok => dsimp only; repeat' first | exact .pure _ | split

private theorem descriptor_fits (reply : Metadata.Reply) (fd : UInt32)
    (opened : Metadata.openDescriptor reply = some fd) : fd.toNat ≤ 2147483647 := by
  unfold Metadata.openDescriptor at opened
  split at opened
  · cases opened
  · rename_i passed
    have fits : reply.1.toNat ≤ 2147483647 := by
      by_cases within : reply.1.toNat ≤ 2147483647
      · exact within
      · have large : reply.1.toNat > 2147483647 := by omega
        exact False.elim (passed (by simp [large]))
    cases opened
    rw [UInt64.toNat_toUInt32]
    exact Nat.le_trans (Nat.mod_le _ _) fits

-- §FS-host-boundary.ownership: Every child file request is read-only and stays on its chosen FD.
theorem bounded_profile (path : String) (limit : Nat) : Profile path (Metadata.bounded path limit) := by
  unfold Metadata.bounded
  split
  · exact .pure _
  · apply Profile.call
    · exact ⟨rfl, rfl, rfl⟩
    · intro reply
      split
      · exact .pure _
      · rename_i fd opened
        exact profile_bind (loop_profile _ _ _ _ _ (descriptor_fits _ _ opened))
          (fun result => finish_profile path fd result (descriptor_fits _ _ opened))

-- §FS-host-boundary.acceptance: This relation retains every reply and a lost final call.
inductive Prefix {α : Type} : Metadata.Program α → List (Metadata.Request × Option Metadata.Reply) → Prop where
  | stop (program : Metadata.Program α) : Prefix program []
  | returned (request : Metadata.Request) (next : Metadata.Reply → Metadata.Program α) (reply : Metadata.Reply)
      (events : List (Metadata.Request × Option Metadata.Reply))
      (following : Prefix (next reply) events) : Prefix (.call request next) ((request, some reply) :: events)
  | lost (request : Metadata.Request) (next : Metadata.Reply → Metadata.Program α) :
      Prefix (.call request next) [(request, none)]

theorem profile_prefix {α : Type} {path : String} {program : Metadata.Program α}
    {events : List (Metadata.Request × Option Metadata.Reply)}
    (source : Profile path program) (active : Prefix program events) : ∀ event ∈ events, Allowed path event.1 := by
  induction active with
  | stop => simp
  | returned request next reply events following ih =>
    cases source with
    | call permitted later =>
      intro event member
      rcases List.mem_cons.mp member with rfl | tail
      · exact permitted
      · exact ih (later reply) event tail
  | lost request next => cases source with | call permitted following => simpa using permitted

theorem actual_metadata_prefix (path : String) (limit : Nat)
    {events : List (Metadata.Request × Option Metadata.Reply)}
    (active : Prefix (Metadata.bounded path limit) events) : ∀ event ∈ events, Allowed path event.1 :=
  profile_prefix (bounded_profile path limit) active

open LeanCage.Host
open LeanCage.Host.Kernel

inductive ChildProgramSource (bundle : Validation.Bundle) (arguments : IO.Process.SpawnArgs) : Type 1 where
  | validator (raw : ByteArray) (context : ValidatorPrefixCuts.Written raw)
      (argumentSource : arguments = Validation.validatorArguments bundle (context.allocated.directory.path ++ "/policy.json"))
      (command : _root_.main arguments.args.toList =
        ControllerValidation.validationOnly (context.allocated.directory.path ++ "/policy.json"))
      (input : Profile (context.allocated.directory.path ++ "/policy.json")
        (Metadata.bounded (context.allocated.directory.path ++ "/policy.json") 65536))
  | vm (request : GatewayWire.Request) (override : Option Nat)
      (context : RunPrefixCuts.Imaged request bundle override)
      (argumentSource : arguments = VirtualMachine.arguments bundle context.allocated.directory.path)

theorem actual_child_program {bundle : Validation.Bundle} {arguments : IO.Process.SpawnArgs}
    {before : List Program.Event} {event : Program.Event} (role : SpawnRole bundle arguments before event) :
    Nonempty (ChildProgramSource bundle arguments) := by
  cases role with
  | validator raw context outside inside active trace argumentSource =>
    exact ⟨.validator raw context argumentSource (actual_spawned_validator _ _ _ argumentSource) (bounded_profile _ _)⟩
  | vm request override context outside inside active trace argumentSource => exact ⟨.vm request override context argumentSource⟩

-- §FS-host-boundary.ownership: Child birth, checked bundle and actual source agree.
theorem actual_recorded_child_program {kernel : Contract} {runtime : ActorRuntime kernel}
    {contract : ProcessContract runtime} {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final) {token : ProcessToken}
    (birth : RecordedProcessBirth contract ticks token) :
    ∃ actor arguments event engine,
      birth.tick.action.eventFor actor = some event ∧ SpawnUse arguments event ∧
      birth.tick.before.actors actor = some engine ∧ birth.after.owner token = some actor ∧
      birth.after.launchArguments token = some arguments ∧
      ∃ source : EntrySpawn engine.events arguments event,
        Nonempty (ChildProgramSource source.caller.context.bundle arguments) := by
  obtain ⟨actor, arguments, event, engine, action, spawn, present, owner, launched, ⟨source⟩⟩ :=
    recorded_process_source journal birth
  exact ⟨actor, arguments, event, engine, action, spawn, present, owner, launched,
    source, actual_child_program source.caller.role⟩

end LeanCage.Application.ControllerFilesystem
