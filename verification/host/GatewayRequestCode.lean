import GatewayWordCode
import LeanCageHost.GatewayWire

namespace LeanCage.Host.GatewayRequestCode

-- §AR-host-boundary.interfaces.gateway: Source witnesses retain every slot's actual bytes.
structure Field where
  kind : Nat
  bytes : List Nat

structure Request where
  command : Nat
  fault : Nat
  fields : List Field

def magic : List Nat := [76, 67, 72, 82, 69, 81, 49, 0]

def headerPrefix (request : Request) : List Nat :=
  magic ++ GatewayWords.encode 4 request.command ++ GatewayWords.encode 4 request.fault

def descriptor (bytes : List Nat) (field : Field) : List Nat :=
  bytes ++ GatewayWords.encode 4 field.kind ++ GatewayWords.encode 8 field.bytes.length

def encode (request : Request) : List Nat :=
  request.fields.foldl (fun bytes field => bytes ++ field.bytes)
    (request.fields.foldl descriptor (headerPrefix request))

def byteView (bytes : ByteArray) : List Nat := bytes.data.toList.map UInt8.toNat

def fieldView (field : GatewayWire.Field) : Field := ⟨field.kind, byteView field.bytes⟩

def view (request : GatewayWire.Request) : Request :=
  ⟨request.command, request.fault, (List.range 8).map (fun index => fieldView (request.field index))⟩

theorem byteView_append (first second : ByteArray) :
    byteView (first ++ second) = byteView first ++ byteView second := by
  simp [byteView, ByteArray.data_append]

theorem byteView_length (bytes : ByteArray) : (byteView bytes).length = bytes.size := by
  simp [byteView]

theorem magic_actual : byteView GatewayWire.requestMagic = magic := by decide

private theorem descriptor_fold_actual (fields : List GatewayWire.Field) (before : ByteArray) :
    byteView (fields.foldl (fun bytes field =>
      bytes ++ littleEndian 4 field.kind ++ littleEndian 8 field.bytes.size) before) =
    (fields.map fieldView).foldl descriptor (byteView before) := by
  induction fields generalizing before with
  | nil => rfl
  | cons field rest ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih]
    congr 1
    simp [descriptor, fieldView, byteView, GatewayWords.encode_actual]

private theorem payload_fold_actual (fields : List GatewayWire.Field) (before : ByteArray) :
    byteView (fields.foldl (fun bytes field => bytes ++ field.bytes) before) =
    (fields.map fieldView).foldl (fun bytes field => bytes ++ field.bytes) (byteView before) := by
  induction fields generalizing before with
  | nil => rfl
  | cons field rest ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih]
    congr 1
    exact byteView_append before field.bytes

-- §FS-host-boundary.caller: This view encodes the actual maintained request, not a parallel codec.
theorem encode_actual (request : GatewayWire.Request) :
    byteView (GatewayWire.encodeRequest request) = encode (view request) := by
  unfold GatewayWire.encodeRequest
  rw [payload_fold_actual, descriptor_fold_actual]
  simp only [encode, view, headerPrefix, List.map_map]
  congr 2

theorem view_has_eight_fields (request : GatewayWire.Request) : (view request).fields.length = 8 := by
  simp [view]

theorem fields_have_bytes (request : GatewayWire.Request) :
    ∀ field ∈ (view request).fields, ∀ byte ∈ field.bytes, byte < 256 := by
  intro field member byte inBytes
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  obtain ⟨value, _, rfl⟩ := List.mem_map.mp inBytes
  exact value.toNat_lt_size



open GatewayWire

-- §FS-host-boundary.caller: The recursive decoder preserves every former loop guard and failure.
def originalFieldLoop (bytes : ByteArray) (indices : List Nat) (position : Nat)
    (fields : Array GatewayWire.Field) : Except String (Nat × Array GatewayWire.Field) :=
  forIn indices (position, fields) fun index state => do
    let kind := fromLittleEndian (bytes.extract (16 + 12 * index) ((16 + 12 * index) + 4))
    let size := fromLittleEndian (bytes.extract (20 + 12 * index) ((20 + 12 * index) + 8))
    if size > GatewayWire.fieldMax index || size > bytes.size - state.1 then
      throw "host request field exceeds its bound"
    pure (.yield (state.1 + size, state.2.push ⟨kind,
      bytes.extract state.1 (state.1 + size)⟩))

theorem decodeFields_matches_original_loop (bytes : ByteArray) (indices : List Nat) (position : Nat)
    (fields : Array GatewayWire.Field) :
    GatewayWire.decodeFields bytes indices position fields = originalFieldLoop bytes indices position fields := by
  induction indices generalizing position fields with
  | nil => rfl
  | cons index rest ih =>
    unfold originalFieldLoop
    rw [List.forIn_cons]
    simp only [GatewayWire.decodeFields]
    split
    · rename_i h
      change (decide (fromLittleEndian (bytes.extract (20 + 12 * index)
        ((20 + 12 * index) + 8)) > GatewayWire.fieldMax index) ||
        decide (fromLittleEndian (bytes.extract (20 + 12 * index)
        ((20 + 12 * index) + 8)) > bytes.size - position)) = true at h
      simp only [ite_eq_left h]
      rfl
    · rename_i h
      change ¬(decide (fromLittleEndian (bytes.extract (20 + 12 * index)
        ((20 + 12 * index) + 8)) > GatewayWire.fieldMax index) ||
        decide (fromLittleEndian (bytes.extract (20 + 12 * index)
        ((20 + 12 * index) + 8)) > bytes.size - position)) = true at h
      simp only [ite_eq_right h]
      exact ih _ _

-- The previous executable loop is retained here only as the behavior-preservation witness.
def originalDecodeRequest (bytes : ByteArray) : Except String GatewayWire.Request := do
  if bytes.size < requestHeader || bytes.size > requestMax ||
      bytes.extract 0 8 != requestMagic then throw "invalid host request header"
  let command := fromLittleEndian (bytes.extract 8 12)
  let fault := fromLittleEndian (bytes.extract 12 16)
  let (position, fields) ← originalFieldLoop bytes (List.range 8) requestHeader #[]
  let request := GatewayWire.Request.mk command fault fields
  if position != bytes.size || !request.valid then throw "inconsistent host request"
  return request

theorem decodeRequest_preserves_original (bytes : ByteArray) :
    GatewayWire.decodeRequest bytes = originalDecodeRequest bytes := by
  unfold GatewayWire.decodeRequest originalDecodeRequest
  rw [decodeFields_matches_original_loop]
  rfl

-- §AR-host-boundary.interfaces.gateway: Raw layout facts feed the actual packet decoder.
def payloadSize : List GatewayWire.Field → Nat
  | [] => 0
  | first :: rest => first.bytes.size + payloadSize rest

def FieldsLayout (bytes : ByteArray) : List Nat → Nat → List GatewayWire.Field → Prop
  | [], _, [] => True
  | index :: indices, position, field :: rest =>
    fromLittleEndian (bytes.extract (16 + 12 * index) ((16 + 12 * index) + 4)) = field.kind ∧
    fromLittleEndian (bytes.extract (20 + 12 * index) ((20 + 12 * index) + 8)) = field.bytes.size ∧
    field.bytes.size ≤ fieldMax index ∧ field.bytes.size ≤ bytes.size - position ∧
    bytes.extract position (position + field.bytes.size) = field.bytes ∧
    FieldsLayout bytes indices (position + field.bytes.size) rest
  | _, _, _ => False

theorem decodeFields_of_layout (bytes : ByteArray) (indices : List Nat) (fields : List GatewayWire.Field)
    (position : Nat) (initial : Array GatewayWire.Field)
    (layout : FieldsLayout bytes indices position fields) :
    decodeFields bytes indices position initial =
      .ok (position + payloadSize fields, initial ++ fields.toArray) := by
  induction indices generalizing fields position initial with
  | nil =>
    cases fields with
    | nil => simp [decodeFields, payloadSize]
    | cons _ _ => cases layout
  | cons index indices ih =>
    cases fields with
    | nil => cases layout
    | cons field fields =>
      obtain ⟨kind, size, bound, fits, payload, rest⟩ := layout
      simp only [decodeFields]
      change (if (decide (fromLittleEndian (bytes.extract (20 + 12 * index)
        ((20 + 12 * index) + 8)) > fieldMax index) ||
        decide (fromLittleEndian (bytes.extract (20 + 12 * index)
        ((20 + 12 * index) + 8)) > bytes.size - position)) = true then
          .error "host request field exceeds its bound"
        else decodeFields bytes indices
          (position + fromLittleEndian (bytes.extract (20 + 12 * index) ((20 + 12 * index) + 8)))
          (initial.push ⟨fromLittleEndian (bytes.extract (16 + 12 * index) ((16 + 12 * index) + 4)),
            bytes.extract position (position + fromLittleEndian
              (bytes.extract (20 + 12 * index) ((20 + 12 * index) + 8)))⟩)) = _
      rw [kind, size]
      rw [payload]
      simp only [Nat.not_lt.mpr bound, Nat.not_lt.mpr fits, decide_false, Bool.or_false,
        Bool.false_eq_true, ↓reduceIte]
      rw [ih fields (position + field.bytes.size) (initial.push field) rest]
      simp only [payloadSize, Nat.add_assoc]
      congr 2
      apply Array.toList_inj.mp
      simp
theorem decodeFields_sound (bytes : ByteArray) (indices : List Nat) (position next : Nat)
    (initial final : Array GatewayWire.Field) (within : position ≤ bytes.size)
    (decoded : decodeFields bytes indices position initial = .ok (next, final)) :
    ∃ fields, final = initial ++ fields.toArray ∧ next = position + payloadSize fields ∧
      FieldsLayout bytes indices position fields := by
  induction indices generalizing position next initial final with
  | nil =>
    simp only [decodeFields, Except.ok.injEq, Prod.mk.injEq] at decoded
    obtain ⟨rfl, rfl⟩ := decoded
    exact ⟨[], by simp, by simp [payloadSize], trivial⟩
  | cons index indices ih =>
    simp only [decodeFields] at decoded
    split at decoded
    · cases decoded
    · rename_i allowed
      let kind := fromLittleEndian (bytes.extract (16 + 12 * index) ((16 + 12 * index) + 4))
      let size := fromLittleEndian (bytes.extract (20 + 12 * index) ((20 + 12 * index) + 8))
      change ¬(decide (size > fieldMax index) || decide (size > bytes.size - position)) = true at allowed
      have bound : size ≤ fieldMax index := by simp_all
      have fits : size ≤ bytes.size - position := by simp_all
      have sliceSize : (bytes.extract position (position + size)).size = size := by
        rw [ByteArray.size_extract]
        omega
      let field : GatewayWire.Field := ⟨kind, bytes.extract position (position + size)⟩
      have fieldSize : field.bytes.size = size := sliceSize
      change decodeFields bytes indices (position + size) (initial.push field) = .ok (next, final) at decoded
      obtain ⟨fields, finalEq, nextEq, rest⟩ := ih (position + size) next (initial.push field) final
        (by omega) decoded
      refine ⟨field :: fields, ?_, ?_, ?_⟩
      · rw [finalEq]
        apply Array.toList_inj.mp
        simp
      · simp only [payloadSize, fieldSize]
        omega
      · exact ⟨rfl, fieldSize.symm, by simpa only [fieldSize] using bound,
          by simpa only [fieldSize] using fits, by rw [fieldSize],
          by simpa only [fieldSize] using rest⟩

-- Every input in this receipt is a raw byte/width/field equation or an executable guard.
structure RequestLayout (bytes : ByteArray) (request : GatewayWire.Request) : Prop where
  lower : requestHeader ≤ bytes.size
  upper : bytes.size ≤ requestMax
  magic : bytes.extract 0 8 = requestMagic
  command : fromLittleEndian (bytes.extract 8 12) = request.command
  fault : fromLittleEndian (bytes.extract 12 16) = request.fault
  fields : FieldsLayout bytes (List.range 8) requestHeader request.fields.toList
  complete : requestHeader + payloadSize request.fields.toList = bytes.size

theorem decodeRequest_of_layout (bytes : ByteArray) (request : GatewayWire.Request)
    (layout : RequestLayout bytes request) (valid : request.valid = true) :
    GatewayWire.decodeRequest bytes = .ok request := by
  have fields := decodeFields_of_layout bytes (List.range 8) request.fields.toList
    requestHeader #[] layout.fields
  simp only [Array.toArray_toList, Array.empty_append] at fields
  unfold GatewayWire.decodeRequest
  split
  · rename_i bad
    simp only [Nat.not_lt.mpr layout.lower, Nat.not_lt.mpr layout.upper, decide_false,
      layout.magic, Bool.or_self] at bad
    cases bad
  · dsimp only
    rw [fields]
    change (if (requestHeader + payloadSize request.fields.toList != bytes.size ||
      !({command := fromLittleEndian (bytes.extract 8 12),
          fault := fromLittleEndian (bytes.extract 12 16), fields := request.fields} :
          GatewayWire.Request).valid) = true then Except.error "inconsistent host request"
      else Except.ok (GatewayWire.Request.mk (fromLittleEndian (bytes.extract 8 12))
        (fromLittleEndian (bytes.extract 12 16)) request.fields)) = Except.ok request
    rw [layout.command, layout.fault, layout.complete]
    cases request
    simp_all

private theorem bind_ok {ε α β : Type} {first : Except ε α} {rest : α → Except ε β}
    {value : β} (h : first.bind rest = .ok value) :
    ∃ middle, first = .ok middle ∧ rest middle = .ok value := by
  cases first with
  | error _ => cases h
  | ok middle => exact ⟨middle, rfl, h⟩

private theorem byteArray_eq_of_bne_false (a b : ByteArray) (same : (a != b) = false) : a = b := by
  have equal : (a.data == b.data) = true := by
    change (!(a.data == b.data)) = false at same
    cases h : (a.data == b.data) <;> simp_all
  exact ByteArray.ext (eq_of_beq equal)

theorem decodeRequest_sound (bytes : ByteArray) (request : GatewayWire.Request)
    (decoded : GatewayWire.decodeRequest bytes = .ok request) :
    RequestLayout bytes request ∧ request.valid = true := by
  unfold GatewayWire.decodeRequest at decoded
  split at decoded
  · cases decoded
  · rename_i allowed
    have lower : requestHeader ≤ bytes.size := by simp_all
    have upper : bytes.size ≤ requestMax := by simp_all
    have magic : bytes.extract 0 8 = requestMagic := by
      apply byteArray_eq_of_bne_false
      simp_all
    dsimp only at decoded
    change Except.bind _ _ = Except.ok request at decoded
    obtain ⟨⟨position, fields⟩, fieldsDecoded, returned⟩ := bind_ok decoded
    split at returned
    · cases returned
    · rename_i consistent
      injection returned with requestEq
      subst request
      have complete : position = bytes.size := by simp_all
      have valid : (GatewayWire.Request.mk
        (fromLittleEndian (bytes.extract 8 12)) (fromLittleEndian (bytes.extract 12 16)) fields).valid = true := by
        have checked := consistent
        simp at checked
        exact checked.2
      obtain ⟨raw, final, cursor, layout⟩ := decodeFields_sound bytes (List.range 8)
        requestHeader position #[] fields lower fieldsDecoded
      have rawEq : raw = fields.toList := by rw [final]; simp
      subst raw
      constructor
      · exact ⟨lower, upper, magic, rfl, rfl, layout, by change requestHeader + payloadSize fields.toList = bytes.size; omega⟩
      · exact valid


-- §FS-host-boundary.caller: Successful parsing and raw bounded layout are equivalent.
theorem decodeRequest_exact_iff (bytes : ByteArray) (request : GatewayWire.Request) :
    GatewayWire.decodeRequest bytes = .ok request ↔
      RequestLayout bytes request ∧ request.valid = true :=
  ⟨decodeRequest_sound bytes request, fun ⟨layout, valid⟩ =>
    decodeRequest_of_layout bytes request layout valid⟩

end LeanCage.Host.GatewayRequestCode
