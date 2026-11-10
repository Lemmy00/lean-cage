import BytesProofs
import LeanCageHost.GatewayChecks

namespace LeanCage.Host.GatewayWords

-- §AR-host-boundary.interfaces: A strict Nat-list view is proved equal to actual byte operations.
def encode (width value : Nat) : List Nat :=
  (List.range width).map (fun index => value / 256 ^ index % 256)

def decode (bytes : List Nat) : Nat := bytes.foldr (fun byte value => byte + 256 * value) 0

def Encoding (width value : Nat) (bytes : List Nat) : Prop :=
  bytes.length = width ∧ (∀ byte ∈ bytes, byte < 256) ∧ decode bytes = value

theorem encode_actual (width value : Nat) :
    ((littleEndian width value).data.toList.map UInt8.toNat) = encode width value := by
  simp [littleEndian, encode, Function.comp_def, UInt8.toNat_ofNat']

theorem decode_actual (bytes : ByteArray) :
    decode (bytes.data.toList.map UInt8.toNat) = fromLittleEndian bytes := by
  simp only [decode, fromLittleEndian, List.foldr_map]

theorem encode_length (width value : Nat) : (encode width value).length = width := by
  simp only [encode, List.length_map, List.length_range]

theorem encode_bounded (width value : Nat) : ∀ byte ∈ encode width value, byte < 256 := by
  intro byte member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  exact Nat.mod_lt _ (by decide)

-- §FS-host-boundary.caller: The native codec preserves every UInt32/UInt64 bit.
theorem decode_encode (width value : Nat) : decode (encode width value) = value % 256 ^ width := by
  rw [← encode_actual, decode_actual, fromLittleEndian_littleEndian]

theorem decode_encode_exact (width value : Nat) (bound : value < 256 ^ width) :
    decode (encode width value) = value := by
  rw [decode_encode, Nat.mod_eq_of_lt bound]

theorem encoded_actual_roundtrip (bytes : ByteArray) :
    littleEndian bytes.size (decode (bytes.data.toList.map UInt8.toNat)) = bytes := by
  rw [decode_actual, littleEndian_fromLittleEndian]

-- §FS-host-boundary.caller: A source-produced Encoding determines the actual byte array uniquely.
theorem encoding_actual (width value : Nat) (bytes : ByteArray)
    (source : Encoding width value (bytes.data.toList.map UInt8.toNat)) :
    bytes.size = width ∧ littleEndian width value = bytes := by
  have size : bytes.size = width := by
    simpa only [List.length_map, Array.length_toList, ByteArray.size_data] using source.1
  have value : fromLittleEndian bytes = value := by simpa only [decode_actual] using source.2.2
  exact ⟨size, by rw [← size, ← value, littleEndian_fromLittleEndian]⟩

theorem encode_encoding (width value : Nat) (bound : value < 256 ^ width) :
    Encoding width value (encode width value) :=
  ⟨encode_length width value, encode_bounded width value, decode_encode_exact width value bound⟩

end LeanCage.Host.GatewayWords
