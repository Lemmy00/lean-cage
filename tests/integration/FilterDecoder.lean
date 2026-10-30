import LeanCage

-- §AR-filter-decoder.checks: Pure executable checks supplement the universally quantified proofs.
namespace LeanCage.Tests.FilterDecoder

open LeanCage.Linux.Filter

private def accepts (abi : Abi) (bytes : ByteArray) : Bool :=
  match decode abi bytes with
  | .ok .denyGetppid => true
  | .error _ => false

private def rejects (abi : Abi) (bytes : ByteArray) (expected : DecodeError) : Bool :=
  match decode abi bytes with
  | .ok _ => false
  | .error error => error == expected

private def zeros (count : Nat) : ByteArray := ⟨Array.replicate count 0⟩

-- §AR-filter-decoder.checks: Success and ABI checks include x32's shared audit architecture.
#guard accepts nativeAbi canonicalBytes
#guard accepts nativeAbi ((ByteArray.mk #[0xaa] ++ canonicalBytes).extract 1 73)
#guard rejects ⟨0x40000003, 32, 32, .littleEndian⟩ canonicalBytes
  (.unsupportedAbi ⟨0x40000003, 32, 32, .littleEndian⟩)
#guard rejects ⟨0xc000003e, 32, 32, .littleEndian⟩ canonicalBytes
  (.unsupportedAbi ⟨0xc000003e, 32, 32, .littleEndian⟩)
#guard rejects ⟨0xc000003e, 64, 32, .littleEndian⟩ canonicalBytes
  (.unsupportedAbi ⟨0xc000003e, 64, 32, .littleEndian⟩)
#guard rejects ⟨0xc000003e, 64, 64, .bigEndian⟩ canonicalBytes
  (.unsupportedAbi ⟨0xc000003e, 64, 64, .bigEndian⟩)

-- §AR-filter-decoder.checks: Every truncated prefix has the required first error.
#guard (List.range 72).all fun count =>
  let expected := if count == 0 then DecodeError.emptyInput
                  else if count % 8 != 0 then .misalignedInput count
                  else .unsupportedLength (count / 8)
  rejects nativeAbi (canonicalBytes.extract 0 count) expected

-- §AR-filter-decoder.checks: Extra payload is never treated as padding or ignored.
#guard (List.range 8).all fun extra =>
  let count := 73 + extra
  let expected := if count % 8 != 0 then DecodeError.misalignedInput count
                  else .unsupportedLength (count / 8)
  rejects nativeAbi (canonicalBytes ++ zeros (extra + 1)) expected

-- §AR-filter-decoder.checks: Exercise the general limit and a wrapping 16-bit count attack.
#guard rejects nativeAbi (zeros 32767) (.misalignedInput 32767)
#guard rejects nativeAbi (zeros 32768) (.unsupportedLength 4096)
#guard rejects nativeAbi (zeros 32769) (.oversizedInput 32769)
#guard rejects nativeAbi (canonicalBytes ++ zeros 524288) (.oversizedInput 524360)
#guard rejects ⟨0, 64, 64, .littleEndian⟩ (zeros 0)
  (.unsupportedAbi ⟨0, 64, 64, .littleEndian⟩)
#guard rejects ⟨0, 64, 64, .littleEndian⟩ (zeros 32769)
  (.unsupportedAbi ⟨0, 64, 64, .littleEndian⟩)

-- §AR-filter-decoder.checks: Every alternate byte value must fail at its instruction index.
#guard (List.range 72).all fun index =>
  (List.range 256).all fun value =>
    let byte := UInt8.ofNat value
    let changed := canonicalBytes.set! index byte
    if byte == canonicalBytes[index]! then accepts nativeAbi changed
    else rejects nativeAbi changed (.unsupportedInstruction (index / 8))

-- §AR-filter-decoder.checks: Earlier mismatches win even when later instructions are malformed.
#guard rejects nativeAbi ((canonicalBytes.set! 60 0xff).set! 19 0xff)
  (.unsupportedInstruction 2)
#guard rejects nativeAbi ((canonicalBytes.set! 0 0).set! 1 0x20)
  (.unsupportedInstruction 0)
#guard rejects nativeAbi ((canonicalBytes.set! 12 0xc0).set! 15 0x3e)
  (.unsupportedInstruction 1)

-- §AR-filter-decoder.checks: Unsigned word boundaries include the highest bit and all bits set.
#guard decodeU16LE 0xff 0xff == 0xffff
#guard decodeU32LE 0xff 0xff 0xff 0xff == 0xffffffff
#guard decodeU32LE 0 0 0 0x80 == 0x80000000

end LeanCage.Tests.FilterDecoder
