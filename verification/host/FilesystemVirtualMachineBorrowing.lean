import FilesystemVirtualMachineBorrowing.Run
import FilesystemActorBorrowing

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: Every actual VM prefix keeps the same borrowed directory/OFD.
theorem vm_prefix_retains_reference {kernel : Contract} {runtime : ActorRuntime kernel}
    (laws : DescriptorContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (actor : ActorId) (held : UInt64) (handle : Handle) (raw : handle.rawOwned = true)
    (bundle : Validation.Bundle) (directory : String) (duration : Nat) (transport : Transport.State)
    {before after : World} {events : List Program.Event}
    (run : ActorPhysicalPrefix runtime actor (VirtualMachine.run bundle directory duration transport)
      before events after) (live : before.handles held = some handle) :
    after.handles held = some handle :=
  actor_borrow_physical_prefix (VirtualMachine.run_borrow laws sdk actor held handle raw
    bundle directory duration transport) run live

theorem vm_return_retains_reference {kernel : Contract} {runtime : ActorRuntime kernel}
    (laws : DescriptorContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (actor : ActorId) (held : UInt64) (handle : Handle) (raw : handle.rawOwned = true)
    (bundle : Validation.Bundle) (directory : String) (duration : Nat) (transport : Transport.State)
    {before after : World} {events : List Program.Event} {result : VirtualMachine.Result}
    (history : ActorReturnsHistory runtime actor before events after)
    (source : Program.Returns (VirtualMachine.run bundle directory duration transport) events result)
    (live : before.handles held = some handle) : after.handles held = some handle :=
  (actor_borrow_returns (VirtualMachine.run_borrow laws sdk actor held handle raw
    bundle directory duration transport) history source live).1

end LeanCage.Host.Kernel
