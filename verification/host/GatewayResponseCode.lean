import GatewayRequestCode

namespace LeanCage.Host.GatewayResponseCode
open GatewayRequestCode (byteView byteView_append byteView_length)

-- §AR-host-boundary.interfaces.gateway: Native response proofs retain exact scalar and key bytes.
inductive Value where
  | null
  | boolean (value : Bool)
  | scalar (tag : Nat) (bytes : List Nat)
  | array (values : List Value)
  | object (fields : List (Value × Value))

def magic : List Nat := [76, 67, 72, 82, 69, 83, 49, 0]

def encodeSpec : Value → List Nat
  | .null => [0]
  | .boolean value => [if value then 2 else 1]
  | .scalar tag bytes => [tag] ++ GatewayWords.encode (if tag == 3 then 4 else 8) bytes.length ++ bytes
  | .array values => values.foldl (fun bytes value => bytes ++ encodeSpec value)
      ([7] ++ GatewayWords.encode 4 values.length)
  | .object fields => fields.foldl (fun bytes field => bytes ++ encodeSpec field.1 ++ encodeSpec field.2)
      ([8] ++ GatewayWords.encode 4 fields.length)
termination_by value => sizeOf value
decreasing_by
  all_goals
    simp only [Value.array.sizeOf_spec, Value.object.sizeOf_spec]
    have smaller := List.sizeOf_lt_of_mem ‹_ ∈ _›
    first
    | omega
    | cases field; simp only [Prod.mk.sizeOf_spec] at *; omega

def view : GatewayWire.Value → Value
  | .null => .null
  | .boolean value => .boolean value
  | .integer value => .scalar 3 (byteView (toString value).toUTF8)
  | .string value => .scalar 4 (byteView value.toUTF8)
  | .bytes value => .scalar 5 (byteView value)
  | .path value => .scalar 6 (byteView value)
  | .number lexical => .scalar 9 (byteView lexical)
  | .array values => .array (values.map view)
  | .object fields => .object (fields.map (fun field => (.scalar 4 (byteView field.1.toUTF8), view field.2)))
termination_by value => sizeOf value
decreasing_by
  all_goals
    simp only [GatewayWire.Value.array.sizeOf_spec, GatewayWire.Value.object.sizeOf_spec]
    have smaller := List.sizeOf_lt_of_mem ‹_ ∈ _›
    first
    | omega
    | cases field; simp only [Prod.mk.sizeOf_spec] at *; omega

inductive Subject where
  | value (value : Value)
  | values (values : List Value)
  | fields (fields : List (Value × Value))

inductive Encoded : Subject → List Nat → Prop where
  | null : Encoded (.value .null) [0]
  | boolean (value : Bool) : Encoded (.value (.boolean value)) [if value then 2 else 1]
  | scalar (tag : Nat) (bytes : List Nat) : Encoded (.value (.scalar tag bytes))
      ([tag] ++ GatewayWords.encode (if tag == 3 then 4 else 8) bytes.length ++ bytes)
  | array (values : List Value) (bytes : List Nat) : Encoded (.values values) bytes →
      Encoded (.value (.array values)) ([7] ++ GatewayWords.encode 4 values.length ++ bytes)
  | object (fields : List (Value × Value)) (bytes : List Nat) : Encoded (.fields fields) bytes →
      Encoded (.value (.object fields)) ([8] ++ GatewayWords.encode 4 fields.length ++ bytes)
  | valuesNil : Encoded (.values []) []
  | valuesCons (value : Value) (values : List Value) (bytes rest : List Nat) :
      Encoded (.value value) bytes → Encoded (.values values) rest →
        Encoded (.values (value :: values)) (bytes ++ rest)
  | fieldsNil : Encoded (.fields []) []
  | fieldsCons (key value : Value) (fields : List (Value × Value)) (keyBytes valueBytes rest : List Nat) :
      Encoded (.value key) keyBytes → Encoded (.value value) valueBytes → Encoded (.fields fields) rest →
        Encoded (.fields ((key, value) :: fields)) (keyBytes ++ valueBytes ++ rest)

def Encoding (value : Value) (bytes : List Nat) : Prop := Encoded (.value value) bytes

def ResponseEncoding (status : Nat) (value : Value) (bytes : List Nat) : Prop :=
  ∃ payload, Encoding value payload ∧ bytes =
    magic ++ GatewayWords.encode 4 status ++ GatewayWords.encode 4 0 ++
      GatewayWords.encode 8 payload.length ++ payload

private theorem fold_append {α : Type} (values : List α) (encode : α → List Nat) (before : List Nat) :
    values.foldl (fun bytes value => bytes ++ encode value) before = before ++ values.flatMap encode := by
  induction values generalizing before with
  | nil => simp
  | cons value rest ih => simp only [List.foldl_cons, List.flatMap_cons, ih, List.append_assoc]

private theorem encodings_spec (values : List Value)
    (children : ∀ value ∈ values, Encoding value (encodeSpec value)) :
    Encoded (.values values) (values.flatMap encodeSpec) := by
  induction values with
  | nil => exact .valuesNil
  | cons value rest ih =>
    exact .valuesCons value rest _ _ (children value (by simp))
      (ih fun child member => children child (by simp [member]))

private theorem field_encodings_spec (fields : List (Value × Value))
    (children : ∀ field ∈ fields, Encoding field.1 (encodeSpec field.1) ∧
      Encoding field.2 (encodeSpec field.2)) :
    Encoded (.fields fields) (fields.flatMap fun field => encodeSpec field.1 ++ encodeSpec field.2) := by
  induction fields with
  | nil => exact .fieldsNil
  | cons field rest ih =>
    exact .fieldsCons field.1 field.2 rest _ _ _ (children field (by simp)).1
      (children field (by simp)).2 (ih fun child member => children child (by simp [member]))

theorem encoding_spec (value : Value) : Encoding value (encodeSpec value) := by
  cases value with
  | null => rw [encodeSpec]; exact .null
  | boolean value => rw [encodeSpec]; exact .boolean value
  | scalar tag bytes => rw [encodeSpec]; exact .scalar tag bytes
  | array values =>
    rw [encodeSpec, fold_append]
    exact .array values _ (encodings_spec values fun child _ => encoding_spec child)
  | object fields =>
    rw [encodeSpec]
    simp only [List.append_assoc]
    rw [fold_append]
    exact .object fields _ (field_encodings_spec fields fun field _ =>
      ⟨encoding_spec field.1, encoding_spec field.2⟩)
termination_by sizeOf value
decreasing_by
  all_goals
    simp only [Value.array.sizeOf_spec, Value.object.sizeOf_spec]
    have smaller := List.sizeOf_lt_of_mem ‹_ ∈ _›
    first
    | omega
    | cases field; simp only [Prod.mk.sizeOf_spec] at *; omega

private theorem byteView_literal (tag : UInt8) :
    byteView (ByteArray.mk #[tag]) = [tag.toNat] := rfl

private theorem byteView_word (width value : Nat) :
    byteView (littleEndian width value) = GatewayWords.encode width value :=
  GatewayWords.encode_actual width value

private theorem array_actual (values : List GatewayWire.Value) (before : ByteArray)
    (children : ∀ child ∈ values, byteView (GatewayWire.encodeValue child) = encodeSpec (view child)) :
    byteView (values.foldl (fun bytes value => bytes ++ GatewayWire.encodeValue value) before) =
      (values.map view).foldl (fun bytes value => bytes ++ encodeSpec value) (byteView before) := by
  induction values generalizing before with
  | nil => rfl
  | cons first rest ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih _ (fun child member => children child (by simp [member]))]
    rw [byteView_append, children first (by simp)]

private theorem fields_actual (fields : List (String × GatewayWire.Value)) (before : ByteArray)
    (children : ∀ field ∈ fields, byteView (GatewayWire.encodeValue field.2) = encodeSpec (view field.2)) :
    byteView (fields.foldl (fun bytes field =>
      bytes ++ ByteArray.mk #[4] ++ littleEndian 8 field.1.toUTF8.size ++ field.1.toUTF8 ++
        GatewayWire.encodeValue field.2) before) =
    (fields.map (fun field => (.scalar 4 (byteView field.1.toUTF8), view field.2))).foldl
      (fun bytes field => bytes ++ encodeSpec field.1 ++ encodeSpec field.2) (byteView before) := by
  induction fields generalizing before with
  | nil => rfl
  | cons first rest ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih _ (fun field member => children field (by simp [member]))]
    simp [byteView_append, byteView_word, children first (by simp), encodeSpec,
      byteView_literal, byteView_length, List.append_assoc]

-- §FS-host-boundary.caller: The native tree representation encodes the actual engine value.
theorem encode_spec_actual (value : GatewayWire.Value) :
    byteView (GatewayWire.encodeValue value) = encodeSpec (view value) := by
  cases value with
  | null => rw [GatewayWire.encodeValue, view, encodeSpec]; rfl
  | boolean value => rw [GatewayWire.encodeValue, view, encodeSpec]; cases value <;> rfl
  | integer value =>
    rw [GatewayWire.encodeValue]
    change byteView (ByteArray.mk #[3] ++ littleEndian 4 (toString value).toUTF8.size ++
      (toString value).toUTF8) = _
    simp only [view, encodeSpec, byteView_append, byteView_literal, byteView_word,
      byteView_length]
    rfl
  | string value =>
    rw [GatewayWire.encodeValue]
    change byteView (ByteArray.mk #[4] ++ littleEndian 8 value.toUTF8.size ++ value.toUTF8) = _
    simp only [view, encodeSpec, byteView_append, byteView_literal, byteView_word, byteView_length]
    rfl
  | bytes value =>
    rw [GatewayWire.encodeValue]
    change byteView (ByteArray.mk #[5] ++ littleEndian 8 value.size ++ value) = _
    simp only [view, encodeSpec, byteView_append, byteView_literal, byteView_word, byteView_length]
    rfl
  | path value =>
    rw [GatewayWire.encodeValue]
    change byteView (ByteArray.mk #[6] ++ littleEndian 8 value.size ++ value) = _
    simp only [view, encodeSpec, byteView_append, byteView_literal, byteView_word, byteView_length]
    rfl
  | number lexical =>
    rw [GatewayWire.encodeValue]
    change byteView (ByteArray.mk #[9] ++ littleEndian 8 lexical.size ++ lexical) = _
    simp only [view, encodeSpec, byteView_append, byteView_literal, byteView_word, byteView_length]
    rfl
  | array values =>
    rw [GatewayWire.encodeValue]
    change byteView (values.foldl (fun bytes value => bytes ++ GatewayWire.encodeValue value)
      (ByteArray.mk #[7] ++ littleEndian 4 values.length)) = _
    rw [array_actual values _ (fun child member => encode_spec_actual child)]
    simp only [view, encodeSpec, List.length_map, byteView_append, byteView_literal, byteView_word]
    rfl
  | object fields =>
    rw [GatewayWire.encodeValue]
    change byteView (fields.foldl (fun bytes field =>
      bytes ++ (ByteArray.mk #[4] ++ littleEndian 8 field.1.toUTF8.size ++ field.1.toUTF8) ++
        GatewayWire.encodeValue field.2) (ByteArray.mk #[8] ++ littleEndian 4 fields.length)) = _
    simp only [← ByteArray.append_assoc]
    rw [fields_actual fields _ (fun field member => encode_spec_actual field.2)]
    simp only [view, encodeSpec, List.length_map, byteView_append, byteView_literal, byteView_word]
    rfl
termination_by sizeOf value
decreasing_by
  all_goals
    simp only [GatewayWire.Value.array.sizeOf_spec, GatewayWire.Value.object.sizeOf_spec]
    have smaller := List.sizeOf_lt_of_mem ‹_ ∈ _›
    first
    | omega
    | cases field; simp only [Prod.mk.sizeOf_spec] at *; omega

theorem encoding_actual (value : GatewayWire.Value) :
    Encoding (view value) (byteView (GatewayWire.encodeValue value)) := by
  rw [encode_spec_actual]
  exact encoding_spec (view value)

theorem magic_actual : byteView GatewayWire.responseMagic = magic := by decide

theorem response_actual (status : Nat) (value : GatewayWire.Value) :
    ResponseEncoding status (view value) (byteView (GatewayWire.encodeResponse status value)) := by
  refine ⟨byteView (GatewayWire.encodeValue value), encoding_actual value, ?_⟩
  simp only [GatewayWire.encodeResponse, byteView_append, magic_actual, byteView_word, byteView_length]

-- §FS-host-boundary.transport: These values are the same maintained executable bounds.
theorem scalar_limits : reportMax = 65536 ∧ manifestMax = 16777216 ∧ workspaceMax = 268435456 ∧
    GatewayWire.pathMax = 4095 ∧ GatewayWire.valueDepthMax = 72 ∧ GatewayWire.valueNodeMax = 1048576 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end LeanCage.Host.GatewayResponseCode
