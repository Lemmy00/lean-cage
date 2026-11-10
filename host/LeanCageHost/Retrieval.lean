import LeanCageHost.Retrieval.Stored

namespace LeanCage.Host.Retrieval

open Filesystem

def destination (request : GatewayWire.Request) (bundle : Validation.Bundle) :
    Filesystem.Program (Result (ByteArray × Option String)) := do
  let lookup := (request.field GatewayWire.lookupSlot).bytes
  if lookup.size == 32 && Transport.lowerHex lookup then
    match String.fromUTF8? lookup with
    | none => return .error "invalid request identity encoding"
    | some identity =>
      let target ← Publication.destination request bundle identity
      return target.map (fun target => (target, some identity))
  else return .ok (lookup, none)

def atDestination (bundle : Validation.Bundle) (path : ByteArray) (identity : Option String) :
    Filesystem.Program (Result GatewayWire.Value) := do
  let parent ← Directories.parent path false
  match parent with
  | .error error => return .error error
  | .ok parent =>
    let target ← Directories.publicAt parent.uid parent.directory.fd parent.name false
    match target with
    | .error error => closeResult parent.directory.fd (.error error)
    | .ok target =>
      let observed ← (readStored bundle parent target identity).run
      let closed ← closeResult target.fd observed
      closeResult parent.directory.fd closed

-- §FS-host-boundary.publication: Both report callers consume the same checked stored metadata.
def report (request : GatewayWire.Request) (bundle : Validation.Bundle) :
    Filesystem.Program (Result GatewayWire.Value) := do
  if !request.valid || request.command != GatewayWire.reportCommand then
    return .error "invalid stored report request"
  let selected ← destination request bundle
  match selected with
  | .error error => return .error error
  | .ok (path, identity) => atDestination bundle path identity

end LeanCage.Host.Retrieval
