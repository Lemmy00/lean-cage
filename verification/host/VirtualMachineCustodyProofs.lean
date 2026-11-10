import LeanCageHost.Application
import VirtualMachineProofs
import ValidationReapingProofs

namespace LeanCage.Host.VirtualMachine
open Filesystem

def spawnErrorResult (transport : Transport.State) : Result :=
  ⟨transport, .empty, none, "unknown", some "VM process creation failed"⟩

-- §FS-host-boundary.ownership: The actual error branch retains the same stream and uncertainty.
theorem spawn_error_source (bundle : Validation.Bundle) (directory : String) (duration : Nat)
    (transport : Transport.State) (error : String) :
    Program.Returns (run bundle directory duration transport)
      [.returned (.spawn (arguments bundle directory)) (.error error)] (spawnErrorResult transport) := by
  apply Program.Returns.call
  exact .pure _

def spawnErrorInput (request : String) (bundle : Validation.Bundle) (preflight : Bool)
    (policy : Policy.Accepted) (transport : Transport.State) : Publication.Input := {
  outcome := incomplete request bundle.identity preflight "unknown"
    (transport.report?.bind (Artifacts.knownReport preflight)) (some "VM process creation failed")
  policy
  boot := .empty
  rawReport := transport.report?
  received := none
  validated := none }

-- §FS-host-boundary.artifacts: The real dispatcher retains every already recognized report.
theorem dispatch_spawn_error_source (request : String) (bundle : Validation.Bundle) (preflight : Bool)
    (policy : Policy.Accepted) (directory : RunDirectory.Owned) (duration : Nat)
    (transport : Transport.State) (error : String) :
    Program.Returns (dispatchImage request bundle preflight policy directory duration transport (.ok ()))
      [.returned (.spawn (arguments bundle directory.path)) (.error error)]
      (spawnErrorInput request bundle preflight policy transport) := by
  apply Program.Returns.call
  exact .pure _

theorem spawn_error_report_preserved (request : String) (bundle : Validation.Bundle) (preflight : Bool)
    (policy : Policy.Accepted) (transport : Transport.State) :
    (spawnErrorInput request bundle preflight policy transport).outcome.report =
      transport.report?.bind (Artifacts.knownReport preflight) ∧
    (spawnErrorInput request bundle preflight policy transport).rawReport = transport.report? ∧
    (spawnErrorInput request bundle preflight policy transport).outcome.vmCleanup = "unknown" :=
  ⟨rfl, rfl, rfl⟩

-- §FS-host-boundary.ownership: Even error/lost cleanup prefixes close only the two owned FDs.
theorem unknown_cleanup_prefix (directory : RunDirectory.Owned) (input : Publication.Input)
    (unknown : input.outcome.vmCleanup = "unknown") {events : List Program.Event}
    (source : Program.Prefix (cleanupRun directory input) events) :
    ∀ event ∈ events, ∃ request reply,
      event = Program.filesystemPrefixEvent (request, reply) ∧ Validation.ReleaseRequest directory request := by
  have same : cleanupRun directory input = Program.liftFilesystem (Validation.releaseDirectory directory) := by
    unfold cleanupRun
    rw [unknown]
    rfl
  rw [same] at source
  obtain ⟨calls, prefixSource, shape⟩ := Program.lift_filesystem_prefix_source _ source
  have requests := request_prefix (Validation.release_requests directory) prefixSource
  intro event member
  rw [shape] at member
  obtain ⟨call, occurs, sameEvent⟩ := List.mem_map.mp member
  exact ⟨call.1, call.2, sameEvent.symm, requests call occurs⟩

theorem spawn_error_cleanup_prefix (request : String) (bundle : Validation.Bundle) (preflight : Bool)
    (policy : Policy.Accepted) (directory : RunDirectory.Owned) (transport : Transport.State)
    {events : List Program.Event}
    (source : Program.Prefix (cleanupRun directory (spawnErrorInput request bundle preflight policy transport)) events) :
    ∀ event ∈ events, ∃ request reply,
      event = Program.filesystemPrefixEvent (request, reply) ∧ Validation.ReleaseRequest directory request :=
  unknown_cleanup_prefix _ _ rfl source

end LeanCage.Host.VirtualMachine
