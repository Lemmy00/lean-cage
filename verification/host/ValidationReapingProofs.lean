import RuntimeEffects
import RunDirectoryProofs.Requests

namespace LeanCage.Host.Validation
open Filesystem

theorem result_reaped_exact (raw : ByteArray) (code : Except String UInt32) (output : Except String ByteArray) :
    (validationResult raw code output).reaped = true ↔ ∃ status, code = .ok status := by
  cases code <;> simp [validationResult]

-- §FS-host-boundary.ownership: Reaping is produced by the same actual successful wait call.
theorem observe_reaped_source (raw : ByteArray) (returnedChild : Except String ValidatorChild)
    {events : List Program.Event} {observed : ChildObservation}
    (source : Program.Returns (observeChild raw returnedChild) events observed) (reaped : observed.reaped = true) :
    ∃ child output status reading,
      returnedChild = .ok child ∧
      Program.Returns (readStream (reportMax + 1) child.stdout reportMax .empty) reading output ∧
      events = reading ++ [.returned (.wait child) (.ok status)] ∧
      observed = validationResult raw (.ok status) output := by
  cases returnedChild with
  | error error =>
    obtain ⟨_, same⟩ := Program.returns_pure _ source
    cases same
    cases reaped
  | ok child =>
    unfold observeChild at source
    obtain ⟨reading, output, later, read, rest, shape⟩ := Program.returns_bind_split _ _ source
    obtain ⟨waiting, code, finalEvents, wait, finished, waitShape⟩ := Program.returns_bind_split _ _ rest
    obtain ⟨rfl, same⟩ := Program.returns_pure _ finished
    cases same
    obtain ⟨status, rfl⟩ := (result_reaped_exact raw code output).mp reaped
    have exactWait : waiting = [.returned (.wait child) (.ok status)] := by
      cases wait with
      | call _ _ reply tail value returned =>
        obtain ⟨rfl, rfl⟩ := Program.returns_pure _ returned
        rfl
    exact ⟨child, output, status, reading, rfl, read, by
      simpa only [waitShape, exactWait, List.append_nil] using shape, rfl⟩

def ReleaseRequest (directory : RunDirectory.Owned) (request : Request) : Prop :=
  request.op = .close ∧ (request.first = directory.directory.fd ∨ request.first = directory.container.fd)

theorem release_requests (directory : RunDirectory.Owned) :
    RequestProgram (ReleaseRequest directory) (releaseDirectory directory) := by
  unfold releaseDirectory
  apply RequestProgram.call
  · exact ⟨rfl, .inl rfl⟩
  · intro reply
    dsimp only [Filesystem.Program.bind]
    apply RequestProgram.call
    · exact ⟨rfl, .inr rfl⟩
    · intro reply
      exact .pure _

-- §FS-host-boundary.ownership: Unknown child lifetime removes neither backing files nor root.
theorem unknown_finish_prefix (directory : RunDirectory.Owned) (observed : ChildObservation)
    (unknown : observed.reaped = false) {events : List Program.Event}
    (active : Program.Prefix (finishValidation directory observed) events) :
    ∀ event ∈ events, ∃ request reply,
      event = Program.filesystemPrefixEvent (request, reply) ∧ ReleaseRequest directory request := by
  have same : finishValidation directory observed = Program.liftFilesystem
      ((releaseDirectory directory).bind (fun _ => .pure observed.result)) := by
    unfold finishValidation
    rw [unknown]
    rfl
  rw [same] at active
  obtain ⟨source, prefixSource, shape⟩ := Program.lift_filesystem_prefix_source _ active
  have requests := request_prefix (request_bind (release_requests directory) (fun _ => .pure _)) prefixSource
  intro event member
  rw [shape] at member
  obtain ⟨call, occurs, sameEvent⟩ := List.mem_map.mp member
  exact ⟨call.1, call.2, sameEvent.symm, requests call occurs⟩

-- §FS-host-boundary.ownership: A rejected policy's successful wait still allows normal cleanup.
theorem rejected_status_reaped (raw diagnostic : ByteArray) (status : UInt32) :
    (validationResult raw (.ok status) (.ok diagnostic)).reaped = true := by
  exact (result_reaped_exact _ _ _).mpr ⟨status, rfl⟩

theorem unknown_wait_not_reaped (raw : ByteArray) (error : String) (output : Except String ByteArray) :
    (validationResult raw (.error error) output).reaped = false := rfl

theorem failed_spawn_not_reaped (raw : ByteArray) (error : String) {events : List Program.Event}
    {observed : ChildObservation} (source : Program.Returns (observeChild raw (.error error)) events observed) :
    observed.reaped = false := by
  obtain ⟨_, same⟩ := Program.returns_pure _ source
  cases same
  rfl

end LeanCage.Host.Validation
