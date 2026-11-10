import LeanCageHost.Commands
import LeanCageHost.Packet
import LeanCageHost.Startup

namespace LeanCage.Host.Entrypoint

def packetResponse (raw : Filesystem.Result GatewayWire.Request) : Program (Nat × GatewayWire.Value) :=
  match raw with
  | .error failure => pure (Commands.failureValue failure)
  | .ok request => Commands.run request

-- §FS-host-boundary.caller: Startup, exact input, application and output use one shared program.
def run : Program UInt32 := do
  let ready ← Program.liftFilesystem Startup.descriptors
  if let .error _ := ready then return 126
  let raw ← Program.liftFilesystem (Packet.read 0)
  let response ← packetResponse raw
  let encoded := GatewayWire.encodeResponse response.1 response.2
  if encoded.size > GatewayWire.responseMax then return 126
  let written ← Program.liftFilesystem (Filesystem.writeLoop (encoded.size + 1) 1 encoded 0)
  match written with
  | .error _ => return 126
  | .ok () => return 0

end LeanCage.Host.Entrypoint
