import LeanCage.Linux.FilterDecoder
import LeanCage.Launch.Model

namespace LeanCage.Linux

open Filter

-- §FS-filter-loading.installation.binding: Native input carries the actual decoder receipt.
structure PreparedFilter where
  bytes : ByteArray
  program : Program
  accepted : decode nativeAbi bytes = .ok program

-- §FS-filter-loading.installation.model: The verdict comes from decoding and entry checks.
def validationVerdict (abi : Abi) (bytes : ByteArray) (entryAccepted : Bool) : Bool :=
  match decode abi bytes with
  | .error _ => false
  | .ok _ => entryAccepted

-- §FS-filter-loading.installation.binding: A failed decoder never reaches the native call.
def prepareFilter (bytes : ByteArray) : Except DecodeError PreparedFilter :=
  match h : decode nativeAbi bytes with
  | .error error => .error error
  | .ok program => .ok ⟨bytes, program, h⟩

-- §AR-m1-launch.binding: The fallback fails closed; native correspondence remains an assumption.
@[extern "leancage_m1_launch"]
def nativeLaunch (_bytes : @& ByteArray) (_path : @& String) (_mode : UInt32) : IO UInt64 :=
  throw (IO.userError "M1 native binding is unavailable")

-- §FS-filter-loading.installation.binding: Only decoder-accepted bytes enter the native binding.
def launch (bytes : ByteArray) (path : String) (mode : UInt32) : IO (Except DecodeError UInt64) := do
  match prepareFilter bytes with
  | .error error => return .error error
  | .ok prepared => return .ok (← nativeLaunch prepared.bytes path mode)

end LeanCage.Linux
