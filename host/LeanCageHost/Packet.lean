import LeanCageHost.GatewayWire
import LeanCageHost.Files

namespace LeanCage.Host.Packet
open Filesystem

-- §AR-host-boundary.interfaces.gateway: Consume the exact packet before dispatch.
def readExact : Nat → UInt64 → Nat → ByteArray → Program (Result ByteArray)
  | 0, _, _, _ => pure (.error "host packet made no bounded progress")
  | fuel + 1, fd, amount, bytes =>
    if bytes.size > amount then pure (.error "host packet exceeded its declared length")
    else if bytes.size == amount then pure (.ok bytes)
    else
      let requested := min chunkMax (amount - bytes.size)
      .call { op := .read, first := fd, second := requested.toUInt64 } fun reply =>
        if nativeError reply then pure (.error (failure "packet read" reply))
        else if reply.1.toNat != reply.2.size || reply.2.size > requested then
          pure (.error "host packet returned invalid bytes")
        else if reply.2.isEmpty then pure (.error "truncated host request packet")
        else readExact fuel fd amount (bytes ++ reply.2)

def payloadLength (header : ByteArray) : Except String Nat := do
  if header.size != GatewayWire.requestHeader ||
      header.extract 0 8 != GatewayWire.requestMagic then throw "invalid host request header"
  let mut size := 0
  for index in List.range 8 do
    let length := fromLittleEndian (header.extract (20 + 12 * index) (28 + 12 * index))
    if length > GatewayWire.fieldMax index then throw "host request field exceeds its bound"
    size := size + length
  if size > GatewayWire.requestMax - GatewayWire.requestHeader then
    throw "host request exceeds its bound"
  return size

def read (fd : UInt64) : Program (Result GatewayWire.Request) := do
  let header ← readExact (GatewayWire.requestHeader + 1) fd GatewayWire.requestHeader .empty
  match header with
  | .error error => return .error error
  | .ok header =>
    match payloadLength header with
    | .error error => return .error (error : Failure)
    | .ok amount =>
      let payload ← readExact (amount + 1) fd amount .empty
      match payload with
      | .error error => return .error error
      | .ok payload =>
        let tail ← Program.effect { op := .read, first := fd, second := 1 }
        if tail.1 != 0 || !tail.2.isEmpty then
          return .error "trailing bytes or read failure after host request packet"
        match GatewayWire.decodeRequest (header ++ payload) with
        | .error error => return .error (error : Failure)
        | .ok request => return .ok request

end LeanCage.Host.Packet
