import EntrypointProofs
import HostMain

namespace LeanCage.Host.Entrypoint

-- §FS-host-boundary.caller: Keep executable identity separate from composable caller proofs.
theorem main_source : _root_.main = (Program.interpret Entrypoint.run : IO UInt32) := rfl

end LeanCage.Host.Entrypoint
