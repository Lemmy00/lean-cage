import GatewayResponseCode

namespace LeanCage.Host.GatewayResponseWords
open GatewayResponseCode

-- §AR-host-boundary.interfaces.gateway: The adapter consumes the actual shared word relation.
theorem word_encoding_unique {width value : Nat} {bytes : List Nat}
    (source : GatewayWords.Encoding width value bytes) : bytes = GatewayWords.encode width value := by
  let packed : ByteArray := ⟨(bytes.map UInt8.ofNat).toArray⟩
  have packedBytes : GatewayRequestCode.byteView packed = bytes := by
    simp only [GatewayRequestCode.byteView, packed, List.map_map]
    change bytes.map (fun value => (UInt8.ofNat value).toNat) = bytes
    calc
      bytes.map (fun value => (UInt8.ofNat value).toNat) = bytes.map id := by
        apply List.map_congr_left
        intro byte member
        simp only [UInt8.toNat_ofNat', id_eq]
        exact Nat.mod_eq_of_lt (source.2.1 byte member)
      _ = bytes := List.map_id bytes
  have actual : GatewayWords.Encoding width value
      (packed.data.toList.map UInt8.toNat) := by
    change GatewayWords.Encoding width value (GatewayRequestCode.byteView packed)
    rw [packedBytes]
    exact source
  have equality := (GatewayWords.encoding_actual width value packed actual).2
  have view := congrArg GatewayRequestCode.byteView equality
  change (littleEndian width value).data.toList.map UInt8.toNat =
    GatewayRequestCode.byteView packed at view
  rw [GatewayWords.encode_actual, packedBytes] at view
  exact view.symm

theorem encode_one_small (value : Nat) (bound : value < 256) : GatewayWords.encode 1 value = [value] := by
  simp [GatewayWords.encode, Nat.mod_eq_of_lt bound]

-- §FS-host-boundary.caller: Native parser receipts keep every actual length and tag word.
inductive SourceEncoded : Subject → List Nat → Prop where
  | null (tagBytes : List Nat) (tag : GatewayWords.Encoding 1 0 tagBytes) :
      SourceEncoded (.value .null) tagBytes
  | boolean (value : Bool) (tagBytes : List Nat)
      (tag : GatewayWords.Encoding 1 (if value then 2 else 1) tagBytes) :
      SourceEncoded (.value (.boolean value)) tagBytes
  | scalar (tag : Nat) (bytes tagBytes sizeBytes : List Nat)
      (tagWord : GatewayWords.Encoding 1 tag tagBytes) (small : tag < 256)
      (sizeWord : GatewayWords.Encoding (if tag == 3 then 4 else 8) bytes.length sizeBytes) :
      SourceEncoded (.value (.scalar tag bytes)) (tagBytes ++ sizeBytes ++ bytes)
  | array (values : List Value) (tagBytes sizeBytes bytes : List Nat)
      (tag : GatewayWords.Encoding 1 7 tagBytes) (size : GatewayWords.Encoding 4 values.length sizeBytes)
      (body : SourceEncoded (.values values) bytes) :
      SourceEncoded (.value (.array values)) (tagBytes ++ sizeBytes ++ bytes)
  | object (fields : List (Value × Value)) (tagBytes sizeBytes bytes : List Nat)
      (tag : GatewayWords.Encoding 1 8 tagBytes) (size : GatewayWords.Encoding 4 fields.length sizeBytes)
      (body : SourceEncoded (.fields fields) bytes) :
      SourceEncoded (.value (.object fields)) (tagBytes ++ sizeBytes ++ bytes)
  | valuesNil : SourceEncoded (.values []) []
  | valuesCons (value : Value) (values : List Value) (bytes rest : List Nat)
      (first : SourceEncoded (.value value) bytes) (remaining : SourceEncoded (.values values) rest) :
      SourceEncoded (.values (value :: values)) (bytes ++ rest)
  | fieldsNil : SourceEncoded (.fields []) []
  | fieldsCons (key value : Value) (fields : List (Value × Value)) (keyBytes valueBytes rest : List Nat)
      (keyBody : SourceEncoded (.value key) keyBytes) (valueBody : SourceEncoded (.value value) valueBytes)
      (remaining : SourceEncoded (.fields fields) rest) :
      SourceEncoded (.fields ((key, value) :: fields)) (keyBytes ++ valueBytes ++ rest)

-- §FS-host-boundary.caller: The source relation implies the unchanged actual response encoding.
theorem source_encoded_original {subject : Subject} {bytes : List Nat}
    (source : SourceEncoded subject bytes) : Encoded subject bytes := by
  induction source with
  | null tagBytes tag =>
      rw [word_encoding_unique tag, encode_one_small 0 (by decide)]
      exact .null
  | boolean value tagBytes tag =>
      rw [word_encoding_unique tag, encode_one_small _ (by cases value <;> decide)]
      exact .boolean value
  | scalar tag bytes tagBytes sizeBytes tagWord small sizeWord =>
      rw [word_encoding_unique tagWord, encode_one_small tag small, word_encoding_unique sizeWord]
      exact .scalar tag bytes
  | array values tagBytes sizeBytes bytes tag size body ih =>
      rw [word_encoding_unique tag, encode_one_small 7 (by decide), word_encoding_unique size]
      exact .array values bytes ih
  | object fields tagBytes sizeBytes bytes tag size body ih =>
      rw [word_encoding_unique tag, encode_one_small 8 (by decide), word_encoding_unique size]
      exact .object fields bytes ih
  | valuesNil => exact .valuesNil
  | valuesCons value values bytes rest first remaining firstIH restIH =>
      exact .valuesCons value values bytes rest firstIH restIH
  | fieldsNil => exact .fieldsNil
  | fieldsCons key value fields keyBytes valueBytes rest keyBody valueBody remaining keyIH valueIH restIH =>
      exact .fieldsCons key value fields keyBytes valueBytes rest keyIH valueIH restIH

def SourceResponseEncoding (status : Nat) (value : Value) (bytes : List Nat) : Prop :=
  ∃ payload statusBytes reservedBytes sizeBytes,
    SourceEncoded (.value value) payload ∧ GatewayWords.Encoding 4 status statusBytes ∧
    GatewayWords.Encoding 4 0 reservedBytes ∧ GatewayWords.Encoding 8 payload.length sizeBytes ∧
    bytes = magic ++ statusBytes ++ reservedBytes ++ sizeBytes ++ payload

-- §FS-host-boundary.caller: The complete source header/payload has the original response meaning.
theorem source_response_original {status : Nat} {value : Value} {bytes : List Nat}
    (source : SourceResponseEncoding status value bytes) : ResponseEncoding status value bytes := by
  obtain ⟨payload, statusBytes, reservedBytes, sizeBytes, payloadSource, statusWord, reservedWord,
    sizeWord, equality⟩ := source
  refine ⟨payload, source_encoded_original payloadSource, ?_⟩
  rw [word_encoding_unique statusWord, word_encoding_unique reservedWord,
    word_encoding_unique sizeWord] at equality
  exact equality

private def subjectCount : Subject → Nat
  | .value _ => 1
  | .values values => values.length
  | .fields fields => 2 * fields.length

private theorem encoded_count {subject : Subject} {bytes : List Nat}
    (encoded : Encoded subject bytes) : subjectCount subject ≤ bytes.length := by
  induction encoded with
  | null => simp [subjectCount]
  | boolean value => simp [subjectCount]
  | scalar tag bytes => simp [subjectCount, GatewayWords.encode_length]
  | array values bytes source ih => simp [subjectCount, GatewayWords.encode_length]
  | object fields bytes source ih => simp [subjectCount, GatewayWords.encode_length]
  | valuesNil => simp [subjectCount]
  | valuesCons value rest bytes remaining first tail firstIH tailIH =>
      simp only [subjectCount, List.length_cons, List.length_append] at *
      omega
  | fieldsNil => simp [subjectCount]
  | fieldsCons key value rest keyBytes valueBytes remaining first second tail firstIH secondIH tailIH =>
      simp only [subjectCount, List.length_cons, List.length_append] at *
      omega

private theorem one_encoding (value : Nat) (small : value < 256) :
    GatewayWords.Encoding 1 value [value] := by
  rw [← encode_one_small value small]
  exact GatewayWords.encode_encoding 1 value small

-- §FS-host-boundary.caller: Actual bounded writer bytes produce the shared framing tree.
theorem encoded_source {subject : Subject} {bytes : List Nat}
    (encoded : Encoded subject bytes) (bound : bytes.length < 256 ^ 4)
    (bounded : ∀ byte ∈ bytes, byte < 256) : SourceEncoded subject bytes := by
  induction encoded with
  | null => exact .null [0] (one_encoding 0 (by decide))
  | boolean value => exact .boolean value _ (one_encoding _ (by cases value <;> decide))
  | scalar tag payload =>
      have small : tag < 256 := bounded tag (by simp)
      have size : payload.length < 256 ^ (if tag == 3 then 4 else 8) := by
        simp only [List.length_append, List.length_singleton, GatewayWords.encode_length] at bound
        split <;> omega
      exact .scalar tag payload [tag] _ (one_encoding tag small) small
        (GatewayWords.encode_encoding _ _ size)
  | array values body source ih =>
      have bodyBound : body.length < 256 ^ 4 := by
        simp only [List.length_append, List.length_singleton, GatewayWords.encode_length] at bound
        omega
      have countBound : values.length < 256 ^ 4 := by
        have count := encoded_count source
        simp only [subjectCount] at count
        omega
      exact .array values [7] _ body (one_encoding 7 (by decide))
        (GatewayWords.encode_encoding 4 values.length countBound)
        (ih bodyBound fun byte member => bounded byte (by simp [member]))
  | object fields body source ih =>
      have bodyBound : body.length < 256 ^ 4 := by
        simp only [List.length_append, List.length_singleton, GatewayWords.encode_length] at bound
        omega
      have countBound : fields.length < 256 ^ 4 := by
        have count := encoded_count source
        simp only [subjectCount] at count
        omega
      exact .object fields [8] _ body (one_encoding 8 (by decide))
        (GatewayWords.encode_encoding 4 fields.length countBound)
        (ih bodyBound fun byte member => bounded byte (by simp [member]))
  | valuesNil => exact .valuesNil
  | valuesCons value rest first remaining firstSource tailSource firstIH tailIH =>
      simp only [List.length_append] at bound
      exact .valuesCons value rest first remaining
        (firstIH (by omega) fun byte member => bounded byte (by simp [member]))
        (tailIH (by omega) fun byte member => bounded byte (by simp [member]))
  | fieldsNil => exact .fieldsNil
  | fieldsCons key value rest first second remaining firstSource secondSource tailSource firstIH secondIH tailIH =>
      simp only [List.length_append] at bound
      exact .fieldsCons key value rest first second remaining
        (firstIH (by omega) fun byte member => bounded byte (by simp [member]))
        (secondIH (by omega) fun byte member => bounded byte (by simp [member]))
        (tailIH (by omega) fun byte member => bounded byte (by simp [member]))

theorem source_encoding_actual (value : GatewayWire.Value)
    (bound : (GatewayWire.encodeValue value).size < 256 ^ 4) :
    SourceEncoded (.value (view value))
      (GatewayRequestCode.byteView (GatewayWire.encodeValue value)) := by
  apply encoded_source (encoding_actual value)
  · simpa only [GatewayRequestCode.byteView_length] using bound
  · intro byte member
    obtain ⟨actual, _, rfl⟩ := List.mem_map.mp member
    exact actual.toNat_lt

theorem source_response_actual (status : Nat) (value : GatewayWire.Value)
    (statusBound : status < 256 ^ 4)
    (bound : (GatewayWire.encodeResponse status value).size ≤ GatewayWire.responseMax) :
    SourceResponseEncoding status (view value)
      (GatewayRequestCode.byteView (GatewayWire.encodeResponse status value)) := by
  have payloadBound : (GatewayWire.encodeValue value).size < 256 ^ 4 := by
    simp only [GatewayWire.encodeResponse, ByteArray.size_append, littleEndian_size] at bound
    change GatewayWire.responseMagic.size + 4 + 4 + 8 + (GatewayWire.encodeValue value).size ≤
      536870912 at bound
    omega
  have sizeBound : (GatewayWire.encodeValue value).size < 256 ^ 8 := by omega
  refine ⟨GatewayRequestCode.byteView (GatewayWire.encodeValue value),
    GatewayWords.encode 4 status, GatewayWords.encode 4 0,
    GatewayWords.encode 8 (GatewayWire.encodeValue value).size,
    source_encoding_actual value payloadBound, GatewayWords.encode_encoding _ _ statusBound,
    GatewayWords.encode_encoding _ _ (by decide), ?_, ?_⟩
  · simpa only [GatewayRequestCode.byteView_length] using GatewayWords.encode_encoding 8
      (GatewayWire.encodeValue value).size sizeBound
  · have wordView (width value : Nat) : GatewayRequestCode.byteView (littleEndian width value) =
        GatewayWords.encode width value := GatewayWords.encode_actual width value
    simp only [GatewayWire.encodeResponse, GatewayRequestCode.byteView_append,
      GatewayResponseCode.magic_actual, wordView]

-- §FS-host-boundary.caller: The strict input view uses structural fuel over the same subjects.
def encodeStep (previous : Subject → Option (List Nat)) : Subject → Option (List Nat)
  | .value value =>
      match value with
      | .null => some [0]
      | .boolean value => some [if value then 2 else 1]
      | .scalar tag bytes =>
          some ([tag] ++ GatewayWords.encode (if tag == 3 then 4 else 8) bytes.length ++ bytes)
      | .array values =>
          (previous (.values values)).map
            (fun bytes => [7] ++ GatewayWords.encode 4 values.length ++ bytes)
      | .object fields =>
          (previous (.fields fields)).map
            (fun bytes => [8] ++ GatewayWords.encode 4 fields.length ++ bytes)
  | .values values =>
      match values with
      | [] => some []
      | value :: rest =>
          match previous (.value value) with
          | none => none
          | some first =>
              match previous (.values rest) with
              | none => none
              | some remaining => some (first ++ remaining)
  | .fields fields =>
      match fields with
      | [] => some []
      | field :: rest =>
          match previous (.value field.1) with
          | none => none
          | some first =>
              match previous (.value field.2) with
              | none => none
              | some second =>
                  match previous (.fields rest) with
                  | none => none
                  | some remaining => some (first ++ second ++ remaining)

def encodeFuel (fuel : Nat) : Subject → Option (List Nat) :=
  Nat.rec (fun _ => none) (fun _ previous => encodeStep previous) fuel

@[simp] theorem encodeFuel_zero (subject : Subject) : encodeFuel 0 subject = none := rfl
@[simp] theorem encodeFuel_succ (fuel : Nat) (subject : Subject) :
    encodeFuel (fuel + 1) subject = encodeStep (encodeFuel fuel) subject := rfl

theorem encodeFuel_mono {fuel more : Nat} {subject : Subject} {bytes : List Nat}
    (encoded : encodeFuel fuel subject = some bytes) (bound : fuel ≤ more) :
    encodeFuel more subject = some bytes := by
  induction fuel generalizing more subject bytes with
  | zero => simp [encodeFuel] at encoded
  | succ fuel ih =>
      cases more with
      | zero => omega
      | succ more =>
          have smaller : fuel ≤ more := by omega
          cases subject with
          | value value =>
              cases value with
              | null => simpa only [encodeFuel_succ, encodeStep] using encoded
              | boolean value => simpa only [encodeFuel_succ, encodeStep] using encoded
              | scalar tag payload => simpa only [encodeFuel_succ, encodeStep] using encoded
              | array values =>
                  simp only [encodeFuel_succ, encodeStep] at encoded ⊢
                  cases source : encodeFuel fuel (.values values) with
                  | none => simp [source] at encoded
                  | some body => rw [ih source smaller]; simpa [source] using encoded
              | object fields =>
                  simp only [encodeFuel_succ, encodeStep] at encoded ⊢
                  cases source : encodeFuel fuel (.fields fields) with
                  | none => simp [source] at encoded
                  | some body => rw [ih source smaller]; simpa [source] using encoded
          | values values =>
              cases values with
              | nil => simpa only [encodeFuel_succ, encodeStep] using encoded
              | cons value rest =>
                  simp only [encodeFuel_succ, encodeStep] at encoded ⊢
                  cases first : encodeFuel fuel (.value value) <;>
                    cases remaining : encodeFuel fuel (.values rest) <;>
                    simp only [first, remaining] at encoded
                  all_goals try contradiction
                  rw [ih first smaller, ih remaining smaller]
                  exact encoded
          | fields fields =>
              cases fields with
              | nil => simpa only [encodeFuel_succ, encodeStep] using encoded
              | cons field rest =>
                  rcases field with ⟨key, value⟩
                  simp only [encodeFuel_succ, encodeStep] at encoded ⊢
                  cases first : encodeFuel fuel (.value key) <;>
                    cases second : encodeFuel fuel (.value value) <;>
                    cases remaining : encodeFuel fuel (.fields rest) <;>
                    simp only [first, second, remaining] at encoded
                  all_goals try contradiction
                  rw [ih first smaller, ih second smaller, ih remaining smaller]
                  exact encoded

theorem encodeFuel_complete {subject : Subject} {bytes : List Nat}
    (encoded : Encoded subject bytes) : ∃ fuel, encodeFuel fuel subject = some bytes := by
  induction encoded with
  | null => exact ⟨1, rfl⟩
  | boolean value => exact ⟨1, rfl⟩
  | scalar tag bytes => exact ⟨1, rfl⟩
  | array values bytes source ih =>
      obtain ⟨fuel, equality⟩ := ih
      exact ⟨fuel + 1, by simp only [encodeFuel_succ, encodeStep, equality, Option.map_some]⟩
  | object fields bytes source ih =>
      obtain ⟨fuel, equality⟩ := ih
      exact ⟨fuel + 1, by simp only [encodeFuel_succ, encodeStep, equality, Option.map_some]⟩
  | valuesNil => exact ⟨1, rfl⟩
  | valuesCons value rest bytes remaining first tail firstIH tailIH =>
      obtain ⟨left, leftEq⟩ := firstIH
      obtain ⟨right, rightEq⟩ := tailIH
      exact ⟨max left right + 1, by
        simp only [encodeFuel_succ, encodeStep, encodeFuel_mono leftEq (Nat.le_max_left ..),
          encodeFuel_mono rightEq (Nat.le_max_right ..)]⟩
  | fieldsNil => exact ⟨1, rfl⟩
  | fieldsCons key value rest keyBytes valueBytes remaining first second tail firstIH secondIH tailIH =>
      obtain ⟨left, leftEq⟩ := firstIH
      obtain ⟨middle, middleEq⟩ := secondIH
      obtain ⟨right, rightEq⟩ := tailIH
      refine ⟨max (max left middle) right + 1, ?_⟩
      rw [encodeFuel_succ, encodeStep, encodeFuel_mono leftEq (by omega),
        encodeFuel_mono middleEq (by omega), encodeFuel_mono rightEq (by omega)]

-- §FS-host-boundary.caller: Enough source fuel reproduces the actual maintained writer bytes.
theorem encodeFuel_actual (value : GatewayWire.Value) :
    ∃ fuel, encodeFuel fuel (.value (view value)) =
      some (GatewayRequestCode.byteView (GatewayWire.encodeValue value)) :=
  encodeFuel_complete (encoding_actual value)

end LeanCage.Host.GatewayResponseWords
