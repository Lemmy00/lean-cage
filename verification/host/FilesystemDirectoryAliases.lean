import FilesystemContracts

namespace LeanCage.Host.Kernel
open Filesystem

-- §AR-host-boundary.primitives: Literal dot-open preserves the retained directory inode.
-- This does not assert exact-name framing for arbitrary hostile public pathname operations.
structure DirectoryAliasContract (kernel : Contract) : Prop where
  dot : ∀ before after request reply parent fd,
    kernel.step before request (some reply) after → request.op = .openAt →
    request.second = directoryFlags → before.handles request.first = some parent →
    request.left = ".".toUTF8 → descriptor reply = some fd →
    ∃ handle, after.handles fd = some handle ∧ handle.object = parent.object

end LeanCage.Host.Kernel
