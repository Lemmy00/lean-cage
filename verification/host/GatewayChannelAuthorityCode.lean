import GatewayChannelCode

namespace LeanCage.Host.ChannelCode

-- §FS-host-boundary.ownership: This is the exact field predicate produced by
-- the native descriptor fold. Its definition grants no source or reader role.
def AliasesCloseExec (references : NativeCode.References) (object : Nat) : Prop :=
  ∀ fd handle, references.handles fd = some handle → handle.object = object →
    references.closeOnExec fd = true

end LeanCage.Host.ChannelCode
