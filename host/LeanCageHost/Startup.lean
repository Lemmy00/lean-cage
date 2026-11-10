import LeanCageHost.Files

namespace LeanCage.Host.Startup
open Filesystem

def sealDescriptors : List UInt64 → Program (Result Unit)
  | [] => pure (.ok ())
  | fd :: rest => .call { op := .closeOnExec, first := fd } fun reply =>
    if reply.1 != 0 || !reply.2.isEmpty then
      pure (.error (failure "IPC descriptor disposition" reply))
    else sealDescriptors rest

-- §FS-host-boundary.caller: Only the engine retains its three private inherited IPC descriptors.
def descriptors : Program (Result Unit) := sealDescriptors [0, 1, 3]

end LeanCage.Host.Startup
