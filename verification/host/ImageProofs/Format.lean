import ImageProofs.Inputs

namespace LeanCage.Host.Image

inductive HexDigits : List Char → List Nat → Prop where
  | empty : HexDigits [] []
  | next (character : Char) (value : Nat) (text : List Char) (digits : List Nat)
      (digit : Snapshot.HexDigit character value) (tail : HexDigits text digits) :
      HexDigits (character :: text) (value :: digits)

-- §FS-host-boundary.snapshot: Hex words independently denote eight ordinary big-endian digits.
def HexWord (value : Nat) (text : List Char) : Prop :=
  ∃ digits : List Nat, digits.length = 8 ∧ HexDigits text digits ∧
    value = digits.foldl (fun previous digit => 16 * previous + digit) 0

private theorem nibble_digit (value : Nat) :
    Snapshot.HexDigit (Snapshot.hexChar (value % 16)) (value % 16) := by
  unfold Snapshot.hexChar Snapshot.HexDigit
  split
  · exact ⟨Nat.mod_lt _ (by decide), .inl ⟨by assumption, rfl⟩⟩
  · exact ⟨Nat.mod_lt _ (by decide), .inr ⟨by omega, rfl⟩⟩

-- §FS-host-boundary.snapshot: The executed word encoder retains every bit when the field fits32.
theorem hex8_meaning (value : Nat) : HexWord (value % 2 ^ 32) (hex8 value).toList := by
  let digits := [value / 268435456 % 16, value / 16777216 % 16, value / 1048576 % 16,
    value / 65536 % 16, value / 4096 % 16, value / 256 % 16, value / 16 % 16, value / 1 % 16]
  refine ⟨digits, rfl, ?_, ?_⟩
  · unfold hex8
    rw [String.toList_ofList]
    change HexDigits
      [Snapshot.hexChar (value / 268435456 % 16), Snapshot.hexChar (value / 16777216 % 16),
       Snapshot.hexChar (value / 1048576 % 16), Snapshot.hexChar (value / 65536 % 16),
       Snapshot.hexChar (value / 4096 % 16), Snapshot.hexChar (value / 256 % 16),
       Snapshot.hexChar (value / 16 % 16), Snapshot.hexChar (value / 1 % 16)] digits
    repeat' apply HexDigits.next _ _ _ _ (nibble_digit _)
    exact .empty
  · simp only [digits, List.foldl_cons, List.foldl_nil, Nat.mul_zero, Nat.zero_add, Nat.div_one]
    omega

theorem hex8_exact (value : Nat) (bounded : value < 2 ^ 32) : HexWord value (hex8 value).toList := by
  simpa only [Nat.mod_eq_of_lt bounded] using hex8_meaning value

def HeaderFields (inode : Nat) (entry : Entry) : List Nat :=
  [inode, entry.mode, 0, 0, 1, 0, entry.bytes.size, 0, 0, 0, 0, entry.name.toUTF8.size + 1, 0]

-- §FS-host-boundary.snapshot: Source headers encode these exact fields, name, NUL and alignment.
theorem header_fields (inode : Nat) (entry : Entry) :
    header inode entry = "070701".toUTF8 ++ (String.join ((HeaderFields inode entry).map hex8)).toUTF8 ++
      entry.name.toUTF8 ++ zeros 1 ++ pad4 (110 + entry.name.toUTF8.size + 1) := rfl

theorem header_numeric_fields (inode : Nat) (entry : Entry) (inodeBound : inode < 2 ^ 32)
    (modeBound : entry.mode < 2 ^ 32) (sizeBound : entry.bytes.size < 2 ^ 32)
    (nameBound : entry.name.toUTF8.size + 1 < 2 ^ 32) :
    ∀ field ∈ HeaderFields inode entry, HexWord field (hex8 field).toList := by
  intro field member
  have bounded : field < 2 ^ 32 := by
    simp only [HeaderFields, List.mem_cons] at member
    repeat' first | omega | (rcases member with rfl | member) | (cases member)
  exact hex8_exact _ bounded

end LeanCage.Host.Image

namespace LeanCage.Host.Image
open Filesystem

inductive CheckedArchiveWrites (fd : UInt64) : Nat → List Entry → List (Request × Reply) → Prop where
  | empty (inode : Nat) : CheckedArchiveWrites fd inode [] []
  | next (inode : Nat) (entry : Entry) (rest : List Entry)
      (headers data padding following : List (Request × Reply))
      (meaning : ∀ field ∈ HeaderFields inode entry, HexWord field (hex8 field).toList)
      (headerBytes : Publication.AcknowledgedWrites fd (header inode entry) 0 headers)
      (dataBytes : Publication.AcknowledgedWrites fd entry.bytes 0 data)
      (paddingBytes : Publication.AcknowledgedWrites fd (pad4 entry.bytes.size) 0 padding)
      (tail : CheckedArchiveWrites fd (inode + 1) rest following) :
      CheckedArchiveWrites fd inode (entry :: rest) (headers ++ data ++ padding ++ following)

private theorem checked_archive {fd : UInt64} {inode : Nat} {overlay : List Entry}
    {events : List (Request × Reply)} (source : ArchiveWrites fd inode overlay events)
    (fields : ∀ entry ∈ overlay,
      entry.mode < 2 ^ 32 ∧ entry.bytes.size < 2 ^ 32 ∧ entry.name.toUTF8.size + 1 < 2 ^ 32)
    (bound : inode + overlay.length ≤ 2 ^ 32) : CheckedArchiveWrites fd inode overlay events := by
  induction source with
  | empty inode => exact .empty _
  | next inode entry rest headers data padding following headerBytes dataBytes paddingBytes tail ih =>
    have first := fields entry (by simp)
    apply CheckedArchiveWrites.next inode entry rest headers data padding following
    · exact header_numeric_fields _ _ (by simp only [List.length_cons] at bound; omega)
        first.1 first.2.1 first.2.2
    · exact headerBytes
    · exact dataBytes
    · exact paddingBytes
    · exact ih (fun entry member => fields entry (by simp [member])) (by
        simp only [List.length_cons] at bound
        omega)

-- §FS-host-boundary.snapshot: Every actual header represents its source value without truncation.
theorem create_headers_meaning (runFd : UInt64) (bundle : Validation.Bundle) (overlay : List Entry)
    {events : List (Request × Reply)} (run : Returns (create runFd bundle overlay) events (.ok ())) :
    ∃ fd selected, CheckedArchiveWrites fd 1 (overlay ++ [⟨"TRAILER!!!", 0, .empty⟩]) selected ∧
      ∀ event ∈ selected, event ∈ events := by
  obtain ⟨bounded, base, fd, copied, opened, writing, closing, shape, baseFrom, recognized, contentFrom, closed⟩ :=
    create_source _ _ _ run
  obtain ⟨baseWrites, padding, selected, contentShape, baseBytes, paddingBytes, source⟩ := contentFrom
  have bounds := overlay_header_fields overlay bounded
  have fields : ∀ entry ∈ overlay ++ [⟨"TRAILER!!!", 0, .empty⟩],
      entry.mode < 2 ^ 32 ∧ entry.bytes.size < 2 ^ 32 ∧ entry.name.toUTF8.size + 1 < 2 ^ 32 := by
    intro entry member
    rcases List.mem_append.mp member with old | trailer
    · exact bounds.2 entry old
    · simp only [List.mem_singleton] at trailer
      cases trailer
      decide
  refine ⟨fd, selected, checked_archive source fields ?_, ?_⟩
  · simp only [List.length_append, List.length_singleton]
    omega
  · intro event member
    rw [shape, contentShape]
    simp [member]

end LeanCage.Host.Image
