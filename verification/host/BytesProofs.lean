import LeanCageHost.Bytes
import Std

namespace LeanCage.Host

-- §FS-host-boundary.transport: The executed encoding has exactly its requested ABI width.
theorem littleEndian_size (width value : Nat) : (littleEndian width value).size = width := by
  simp [littleEndian, ByteArray.size]

private theorem littleEndian_list_succ (width value : Nat) :
    (littleEndian (width + 1) value).data.toList =
      UInt8.ofNat value :: (littleEndian width (value / 256)).data.toList := by
  simp [littleEndian, List.range_succ_eq_map, List.map_map, Nat.pow_succ,
    Nat.div_div_eq_div_mul, Nat.mul_comm]

private theorem readList_bound (bytes : List UInt8) :
    bytes.foldr (fun byte value => byte.toNat + 256 * value) 0 < 256 ^ bytes.length := by
  induction bytes with
  | nil => simp
  | cons byte bytes ih =>
    have byteBound : byte.toNat < 256 := byte.toNat_lt_size
    simp only [List.foldr_cons, List.length_cons, Nat.pow_succ]
    omega

-- §FS-host-boundary.transport: Nat decoding exposes all bits and cannot wrap at UInt64 width.
theorem fromLittleEndian_bound (bytes : ByteArray) :
    fromLittleEndian bytes < 256 ^ bytes.size := by
  change bytes.data.toList.foldr (fun byte value => byte.toNat + 256 * value) 0 < 256 ^ bytes.data.size
  simpa only [Array.length_toList] using readList_bound bytes.data.toList

theorem fromLittleEndian_littleEndian (width value : Nat) :
    fromLittleEndian (littleEndian width value) = value % 256 ^ width := by
  induction width generalizing value with
  | zero =>
    change 0 = value % 1
    exact (Nat.mod_one value).symm
  | succ width ih =>
    unfold fromLittleEndian
    rw [littleEndian_list_succ]
    simp only [List.foldr_cons, UInt8.toNat_ofNat']
    change value % 256 + 256 * fromLittleEndian (littleEndian width (value / 256)) =
      value % 256 ^ (width + 1)
    rw [ih, Nat.pow_succ, Nat.mul_comm (256 ^ width) 256, Nat.mod_mul]

theorem fromLittleEndian_littleEndian_exact (width value : Nat) (bound : value < 256 ^ width) :
    fromLittleEndian (littleEndian width value) = value := by
  rw [fromLittleEndian_littleEndian, Nat.mod_eq_of_lt bound]

private theorem encode_read_list (bytes : List UInt8) :
    (littleEndian bytes.length (bytes.foldr (fun byte value => byte.toNat + 256 * value) 0)).data.toList = bytes := by
  induction bytes with
  | nil => simp [littleEndian]
  | cons byte bytes ih =>
    simp only [List.length_cons, List.foldr_cons]
    rw [littleEndian_list_succ]
    have byteBound : byte.toNat < 256 := byte.toNat_lt_size
    have first : UInt8.ofNat (byte.toNat + 256 * bytes.foldr
        (fun byte value => byte.toNat + 256 * value) 0) = byte := by
      apply UInt8.toNat.inj
      simp only [UInt8.toNat_ofNat']
      change (byte.toNat + 256 * _) % 256 = byte.toNat
      omega
    have rest : (byte.toNat + 256 * bytes.foldr
        (fun byte value => byte.toNat + 256 * value) 0) / 256 =
        bytes.foldr (fun byte value => byte.toNat + 256 * value) 0 := by omega
    rw [first, rest, ih]

theorem littleEndian_fromLittleEndian (bytes : ByteArray) :
    littleEndian bytes.size (fromLittleEndian bytes) = bytes := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  change (littleEndian bytes.data.size (bytes.data.toList.foldr
    (fun byte value => byte.toNat + 256 * value) 0)).data.toList = bytes.data.toList
  simpa only [Array.length_toList] using encode_read_list bytes.data.toList

theorem littleEndian_injective (width first second : Nat)
    (firstBound : first < 256 ^ width) (secondBound : second < 256 ^ width)
    (same : littleEndian width first = littleEndian width second) : first = second := by
  have decoded := congrArg fromLittleEndian same
  simpa only [fromLittleEndian_littleEndian_exact width first firstBound,
    fromLittleEndian_littleEndian_exact width second secondBound] using decoded

end LeanCage.Host
