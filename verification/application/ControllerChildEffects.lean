import ControllerFilesystem
import FilesystemGlobalAuthority

namespace LeanCage.Application.ControllerFilesystem
open LeanCageM3
open LeanCage.Host
open LeanCage.Host.Filesystem
open LeanCage.Host.Kernel

-- §AR-metadata.primitives: Preserve the real three-dispatch ABI, including open's exact flags.
def metadataRequest (request : Metadata.Request) : Request :=
  match request.op with
  | .open => {
      op := .openAt
      first := cwd
      second := 524288
      left := request.path.toUTF8 }
  | .read => { op := .read, first := request.fd.toUInt64, second := request.amount }
  | .close => { op := .close, first := request.fd.toUInt64 }

theorem metadata_authority_safe (request : Metadata.Request) : AuthoritySafeRequest (metadataRequest request) := by
  cases op : request.op <;> simp [AuthoritySafeRequest, metadataRequest, op]

-- §AR-host-boundary.primitives: These are individual SDK operations, not child-lifetime frames.
structure ControllerRuntimeContract where
  observed : ProcessToken → World → ChildOperation → Option Reply → World → Prop
  authority : ∀ token before operation reply after,
    observed token before operation reply after → ChildAuthoritySafe operation

-- §AR-host-boundary.primitives: QEMU observations are bound to the actual fixed spawn arguments.
structure VmmRuntimeContract where
  observed : IO.Process.SpawnArgs → ProcessToken → World → ChildOperation → Option Reply → World → Prop
  authority : ∀ bundle directory token before operation reply after,
    observed (VirtualMachine.arguments bundle directory) token before operation reply after →
    ChildAuthoritySafe operation

inductive ControllerCallSource {kernel : Contract} {runtime : ActorRuntime kernel}
    {contract : ProcessContract runtime} {primitive : ChildPrimitive kernel}
    (sdk : ControllerRuntimeContract) {ticks : List (ActorTick runtime)} {position : Nat} {tick : ActorTick runtime}
    (source : OwnedChildCall contract primitive ticks position tick) (path : String) : Type 1 where
  | metadata (request : Metadata.Request) (before : List (Metadata.Request × Option Metadata.Reply))
      (reply : Option Metadata.Reply)
      (active : Prefix (Metadata.bounded path 65536) (before ++ [(request, reply)]))
      (operation : source.call.operation = .adapted (metadataRequest request))
      (sameReply : source.call.reply = reply) : ControllerCallSource sdk source path
  | runtime (observed : sdk.observed source.call.token
      (source.call.beforeReferences.project tick.before.shared) source.call.operation source.call.reply
      (source.call.afterReferences.project tick.after.shared)) : ControllerCallSource sdk source path

-- §FS-host-boundary.ownership: The controller's maintained reader cannot emit an ACL setter.
theorem actual_controller_authority {kernel : Contract} {runtime : ActorRuntime kernel}
    {contract : ProcessContract runtime} {primitive : ChildPrimitive kernel}
    (sdk : ControllerRuntimeContract) {ticks : List (ActorTick runtime)} {position : Nat} {tick : ActorTick runtime}
    (source : OwnedChildCall contract primitive ticks position tick) (path : String)
    (recorded : ControllerCallSource sdk source path) : ChildAuthoritySafe source.call.operation := by
  cases recorded with
  | metadata request before reply active operation sameReply =>
    rw [operation]
    exact metadata_authority_safe request
  | runtime observed => exact sdk.authority _ _ _ _ _ observed

-- §FS-host-boundary.acceptance: Both branches use this child's actual earlier maintained spawn.
theorem backend_authority_from_actual_programs {kernel : Contract} {runtime : ActorRuntime kernel}
    {contract : ProcessContract runtime} {primitive : ChildPrimitive kernel}
    (sdk : ControllerRuntimeContract) (vmm : VmmRuntimeContract) (ticks : List (ActorTick runtime))
    (controller : ∀ position tick, ∀ source : OwnedChildCall contract primitive ticks position tick,
      ∀ bundle raw (context : ValidatorPrefixCuts.Written raw),
      source.source.arguments = Validation.validatorArguments bundle (context.allocated.directory.path ++ "/policy.json") →
      Nonempty (ControllerCallSource sdk source (context.allocated.directory.path ++ "/policy.json")))
    (virtualMachine : ∀ position tick, ∀ source : OwnedChildCall contract primitive ticks position tick,
      ∀ bundle directory, source.source.arguments = VirtualMachine.arguments bundle directory →
      vmm.observed source.source.arguments source.call.token
        (source.call.beforeReferences.project tick.before.shared) source.call.operation source.call.reply
        (source.call.afterReferences.project tick.after.shared)) :
    BackendAuthorityProducer contract primitive ticks := by
  intro position tick source
  have role := source.source.source.caller.role
  cases role with
  | validator raw context outside inside active trace argumentSource =>
    obtain ⟨recorded⟩ := controller position tick source _ raw context argumentSource
    exact actual_controller_authority sdk source _ recorded
  | vm request override context outside inside active trace argumentSource =>
    have observed := virtualMachine position tick source _ context.allocated.directory.path argumentSource
    rw [argumentSource] at observed
    exact vmm.authority _ _ _ _ _ _ _ observed

end LeanCage.Application.ControllerFilesystem
