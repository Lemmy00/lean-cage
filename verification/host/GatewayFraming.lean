import GatewayResponseWords

namespace LeanCage.Host.GatewayFraming
open GatewayResponseCode GatewayResponseWords

-- §AR-host-boundary.interfaces.gateway: Scalar separation comes from the actual typed producers.
inductive Canonical : Subject → Prop where
  | null : Canonical (.value .null)
  | boolean (flag : Bool) : Canonical (.value (.boolean flag))
  | scalar (tag : Nat) (bytes : List Nat)
      (valid : tag = 3 ∨ tag = 4 ∨ tag = 5 ∨ tag = 6 ∨ tag = 9) :
      Canonical (.value (.scalar tag bytes))
  | array (values : List Value) : Canonical (.values values) → Canonical (.value (.array values))
  | object (fields : List (Value × Value)) :
      Canonical (.fields fields) → Canonical (.value (.object fields))
  | valuesNil : Canonical (.values [])
  | valuesCons (value : Value) (values : List Value) :
      Canonical (.value value) → Canonical (.values values) → Canonical (.values (value :: values))
  | fieldsNil : Canonical (.fields [])
  | fieldsCons (key value : Value) (fields : List (Value × Value)) :
      Canonical (.value key) → Canonical (.value value) → Canonical (.fields fields) →
      Canonical (.fields ((key, value) :: fields))

inductive Mode where
  | value
  | values (count : Nat)
  | fields (count : Nat)

def mode : Subject → Mode
  | .value _ => .value
  | .values values => .values values.length
  | .fields fields => .fields fields.length

private def word (width : Nat) (bytes : List Nat) : Nat × List Nat :=
  (GatewayWords.decode (bytes.take width), bytes.drop width)

private theorem word_prefix {width value : Nat} {bytes tail : List Nat}
    (source : GatewayWords.Encoding width value bytes) : word width (bytes ++ tail) = (value, tail) := by
  unfold word
  rw [← source.1, List.take_left, List.drop_left, source.2.2]

-- §FS-host-boundary.caller: This total proof reader compares prefixes of the unchanged wire.
-- It supplies no new public decoding path and assumes no future source events.
def readStep (previous : Mode → List Nat → Option (Subject × List Nat)) :
    Mode → List Nat → Option (Subject × List Nat)
  | .value, [] => none
  | .value, tag :: bytes =>
      if tag = 0 then some (.value .null, bytes)
      else if tag = 1 then some (.value (.boolean false), bytes)
      else if tag = 2 then some (.value (.boolean true), bytes)
      else if tag = 7 then
        let (count, rest) := word 4 bytes
        match previous (.values count) rest with
        | some (.values values, tail) => some (.value (.array values), tail)
        | _ => none
      else if tag = 8 then
        let (count, rest) := word 4 bytes
        match previous (.fields count) rest with
        | some (.fields fields, tail) => some (.value (.object fields), tail)
        | _ => none
      else if tag = 3 ∨ tag = 4 ∨ tag = 5 ∨ tag = 6 ∨ tag = 9 then
        let (count, rest) := word (if tag = 3 then 4 else 8) bytes
        some (.value (.scalar tag (rest.take count)), rest.drop count)
      else none
  | .values 0, bytes => some (.values [], bytes)
  | .values (count + 1), bytes =>
      match previous .value bytes with
      | some (.value value, after) =>
          match previous (.values count) after with
          | some (.values values, tail) => some (.values (value :: values), tail)
          | _ => none
      | _ => none
  | .fields 0, bytes => some (.fields [], bytes)
  | .fields (count + 1), bytes =>
      match previous .value bytes with
      | some (.value key, afterKey) =>
          match previous .value afterKey with
          | some (.value value, afterValue) =>
              match previous (.fields count) afterValue with
              | some (.fields fields, tail) => some (.fields ((key, value) :: fields), tail)
              | _ => none
          | _ => none
      | _ => none

def readFuel : Nat → Mode → List Nat → Option (Subject × List Nat)
  | 0 => fun _ _ => none
  | fuel + 1 => readStep (readFuel fuel)

-- §FS-host-boundary.caller: Each actual source encoding consumes exactly its own prefix.
theorem source_read {subject : Subject} {bytes : List Nat}
    (source : SourceEncoded subject bytes) (canonical : Canonical subject)
    (fuel : Nat) (enough : sizeOf subject < fuel) (tail : List Nat) :
    readFuel fuel (mode subject) (bytes ++ tail) = some (subject, tail) := by
  induction source generalizing fuel tail with
  | null tagBytes tag =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [word_encoding_unique tag, encode_one_small 0 (by decide)]
      rfl
  | boolean flag tagBytes tag =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [word_encoding_unique tag, encode_one_small _ (by cases flag <;> decide)]
      cases flag <;> rfl
  | scalar tag bytes tagBytes sizeBytes tagWord small sizeWord =>
    cases canonical with
    | scalar _ _ valid =>
      cases fuel with
      | zero => omega
      | succ fuel =>
        rw [word_encoding_unique tagWord, encode_one_small tag small]
        have separate : tag ≠ 0 ∧ tag ≠ 1 ∧ tag ≠ 2 ∧ tag ≠ 7 ∧ tag ≠ 8 := by
          rcases valid with rfl | rfl | rfl | rfl | rfl <;> decide
        have actualWord : word (if tag = 3 then 4 else 8) (sizeBytes ++ (bytes ++ tail)) =
            (bytes.length, bytes ++ tail) := by
          simpa only [beq_iff_eq] using (word_prefix (tail := bytes ++ tail) sizeWord)
        simp only [readFuel, mode, readStep, List.cons_append, List.nil_append,
          List.append_assoc, ite_eq_right separate.1, ite_eq_right separate.2.1, ite_eq_right separate.2.2.1,
          ite_eq_right separate.2.2.2.1, ite_eq_right separate.2.2.2.2, ite_eq_left valid, actualWord]
        simp only [List.take_left, List.drop_left]
  | array values tagBytes sizeBytes bytes tag size body ih =>
    cases canonical with
    | array _ children =>
      cases fuel with
      | zero => omega
      | succ fuel =>
        rw [word_encoding_unique tag, encode_one_small 7 (by decide)]
        simp only [readFuel, mode, readStep, List.cons_append,
          List.nil_append, List.append_assoc, reduceIte, Nat.reduceEqDiff]
        rw [word_prefix size]
        have smaller : sizeOf (Subject.values values) < fuel := by
          simp only [Subject.value.sizeOf_spec, Value.array.sizeOf_spec] at enough
          simp only [Subject.values.sizeOf_spec]
          omega
        have bodyRead := ih children fuel smaller tail
        simp only [mode] at bodyRead
        simp only [bodyRead]
  | object fields tagBytes sizeBytes bytes tag size body ih =>
    cases canonical with
    | object _ children =>
      cases fuel with
      | zero => omega
      | succ fuel =>
        rw [word_encoding_unique tag, encode_one_small 8 (by decide)]
        simp only [readFuel, mode, readStep, List.cons_append,
          List.nil_append, List.append_assoc, reduceIte, Nat.reduceEqDiff]
        rw [word_prefix size]
        have smaller : sizeOf (Subject.fields fields) < fuel := by
          simp only [Subject.value.sizeOf_spec, Value.object.sizeOf_spec] at enough
          simp only [Subject.fields.sizeOf_spec]
          omega
        have bodyRead := ih children fuel smaller tail
        simp only [mode] at bodyRead
        simp only [bodyRead]
  | valuesNil =>
    cases fuel with
    | zero => omega
    | succ fuel => rfl
  | valuesCons value values bytes rest first remaining firstIH restIH =>
    cases canonical with
    | valuesCons _ _ head tailCanonical =>
      cases fuel with
      | zero => omega
      | succ fuel =>
        have headBound : sizeOf (Subject.value value) < fuel := by
          simp only [Subject.values.sizeOf_spec, List.cons.sizeOf_spec] at enough
          simp only [Subject.value.sizeOf_spec]; omega
        have tailBound : sizeOf (Subject.values values) < fuel := by
          simp only [Subject.values.sizeOf_spec, List.cons.sizeOf_spec] at enough ⊢
          omega
        simp only [readFuel, mode, List.length_cons, readStep, List.append_assoc]
        have firstRead := firstIH head fuel headBound (rest ++ tail)
        have restRead := restIH tailCanonical fuel tailBound tail
        simp only [mode] at firstRead restRead
        simp only [firstRead, restRead]
  | fieldsNil =>
    cases fuel with
    | zero => omega
    | succ fuel => rfl
  | fieldsCons key value fields keyBytes valueBytes rest keyBody valueBody remaining keyIH valueIH restIH =>
    cases canonical with
    | fieldsCons _ _ _ keyCanonical valueCanonical tailCanonical =>
      cases fuel with
      | zero => omega
      | succ fuel =>
        have keyBound : sizeOf (Subject.value key) < fuel := by
          simp only [Subject.fields.sizeOf_spec, List.cons.sizeOf_spec, Prod.mk.sizeOf_spec] at enough
          simp only [Subject.value.sizeOf_spec]; omega
        have valueBound : sizeOf (Subject.value value) < fuel := by
          simp only [Subject.fields.sizeOf_spec, List.cons.sizeOf_spec, Prod.mk.sizeOf_spec] at enough
          simp only [Subject.value.sizeOf_spec]; omega
        have tailBound : sizeOf (Subject.fields fields) < fuel := by
          simp only [Subject.fields.sizeOf_spec, List.cons.sizeOf_spec, Prod.mk.sizeOf_spec] at enough ⊢
          omega
        simp only [readFuel, mode, List.length_cons, readStep, List.append_assoc]
        have keyRead := keyIH keyCanonical fuel keyBound (valueBytes ++ (rest ++ tail))
        have valueRead := valueIH valueCanonical fuel valueBound (rest ++ tail)
        have restRead := restIH tailCanonical fuel tailBound tail
        simp only [mode] at keyRead valueRead restRead
        simp only [keyRead, valueRead, restRead]

-- §FS-host-boundary.caller: Self-delimiting typed values agree even across an unfinished writer.
theorem source_prefix_unique {first second : Subject} {left right leftTail rightTail : List Nat}
    (leftSource : SourceEncoded first left) (rightSource : SourceEncoded second right)
    (leftCanonical : Canonical first) (rightCanonical : Canonical second)
    (sameMode : mode first = mode second) (sameBytes : left ++ leftTail = right ++ rightTail) :
    first = second ∧ leftTail = rightTail := by
  let fuel := max (sizeOf first) (sizeOf second) + 1
  have leftRead := source_read leftSource leftCanonical fuel (by dsimp [fuel]; omega) leftTail
  have rightRead := source_read rightSource rightCanonical fuel (by dsimp [fuel]; omega) rightTail
  rw [sameMode, sameBytes, rightRead] at leftRead
  exact Prod.mk.inj (Option.some.inj leftRead.symm)

private theorem canonical_values (values : List Value)
    (children : ∀ child ∈ values, Canonical (.value child)) : Canonical (.values values) := by
  induction values with
  | nil => exact .valuesNil
  | cons first rest ih =>
    exact .valuesCons first rest (children first (by simp))
      (ih fun child member => children child (by simp [member]))

private theorem canonical_fields (fields : List (Value × Value))
    (children : ∀ field ∈ fields, Canonical (.value field.1) ∧ Canonical (.value field.2)) :
    Canonical (.fields fields) := by
  induction fields with
  | nil => exact .fieldsNil
  | cons first rest ih =>
    exact .fieldsCons first.1 first.2 rest (children first (by simp)).1
      (children first (by simp)).2 (ih fun child member => children child (by simp [member]))

-- §FS-host-boundary.caller: The maintained executable writer supplies its own tag restriction.
theorem canonical_view (value : GatewayWire.Value) : Canonical (.value (view value)) := by
  cases value with
  | null => rw [view]; exact .null
  | boolean flag => rw [view]; exact .boolean flag
  | integer value => rw [view]; exact .scalar 3 _ (by simp)
  | string value => rw [view]; exact .scalar 4 _ (by simp)
  | bytes value => rw [view]; exact .scalar 5 _ (by simp)
  | path value => rw [view]; exact .scalar 6 _ (by simp)
  | number value => rw [view]; exact .scalar 9 _ (by simp)
  | array values =>
    rw [view]
    apply Canonical.array
    apply canonical_values
    intro child member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact canonical_view original
  | object fields =>
    rw [view]
    apply Canonical.object
    apply canonical_fields
    intro field member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact ⟨.scalar 4 _ (by simp), canonical_view original.2⟩
termination_by sizeOf value
decreasing_by
  all_goals
    simp only [GatewayWire.Value.array.sizeOf_spec, GatewayWire.Value.object.sizeOf_spec]
    have smaller := List.sizeOf_lt_of_mem originalMember
    first
    | omega
    | cases original; simp only [Prod.mk.sizeOf_spec] at *; omega

private def responseRead (fuel : Nat) (bytes : List Nat) : Nat × Option (Subject × List Nat) :=
  let (status, rest) := word 4 (bytes.drop 8)
  (status, readFuel fuel .value ((rest.drop 4).drop 8))

private theorem source_response_read {status : Nat} {value : Value} {bytes : List Nat}
    (source : SourceResponseEncoding status value bytes) (canonical : Canonical (.value value))
    (fuel : Nat) (enough : sizeOf (Subject.value value) < fuel) (tail : List Nat) :
    responseRead fuel (bytes ++ tail) = (status, some (.value value, tail)) := by
  obtain ⟨payload, statusBytes, reservedBytes, sizeBytes, payloadSource, statusSource,
    reservedSource, sizeSource, equality⟩ := source
  unfold responseRead
  rw [equality]
  simp only [List.append_assoc]
  have magicSize : magic.length = 8 := rfl
  rw [← magicSize, List.drop_left, word_prefix statusSource]
  dsimp only
  rw [magicSize]
  rw [← reservedSource.1, List.drop_left, ← sizeSource.1, List.drop_left]
  exact congrArg (fun result => (status, result)) (source_read payloadSource canonical fuel enough tail)

-- §FS-host-boundary.caller: Complete accepted framing cannot be a strict prefix of this response.
theorem response_prefix_unique {leftStatus rightStatus : Nat} {leftValue rightValue : Value}
    {left right leftTail rightTail : List Nat}
    (leftSource : SourceResponseEncoding leftStatus leftValue left)
    (rightSource : SourceResponseEncoding rightStatus rightValue right)
    (leftCanonical : Canonical (.value leftValue)) (rightCanonical : Canonical (.value rightValue))
    (sameBytes : left ++ leftTail = right ++ rightTail) :
    leftStatus = rightStatus ∧ leftValue = rightValue ∧ leftTail = rightTail := by
  let fuel := max (sizeOf (Subject.value leftValue)) (sizeOf (Subject.value rightValue)) + 1
  have leftRead := source_response_read leftSource leftCanonical fuel (by dsimp [fuel]; omega) leftTail
  have rightRead := source_response_read rightSource rightCanonical fuel (by dsimp [fuel]; omega) rightTail
  rw [sameBytes, rightRead] at leftRead
  obtain ⟨statuses, decoded⟩ := Prod.mk.inj leftRead.symm
  obtain ⟨subjects, tails⟩ := Prod.mk.inj (Option.some.inj decoded)
  exact ⟨statuses, Subject.value.inj subjects, tails⟩

theorem response_complete_prefix {writerStatus parsedStatus : Nat} {writerValue parsedValue : Value}
    {writerBytes parsedBytes pending : List Nat}
    (writer : SourceResponseEncoding writerStatus writerValue writerBytes)
    (parsed : SourceResponseEncoding parsedStatus parsedValue parsedBytes)
    (writerCanonical : Canonical (.value writerValue)) (parsedCanonical : Canonical (.value parsedValue))
    (leading : writerBytes = parsedBytes ++ pending) :
    writerStatus = parsedStatus ∧ writerValue = parsedValue ∧ pending = [] ∧ writerBytes = parsedBytes := by
  have same : writerBytes ++ [] = parsedBytes ++ pending := by simpa only [List.append_nil] using leading
  obtain ⟨status, value, tail⟩ := response_prefix_unique writer parsed writerCanonical parsedCanonical same
  exact ⟨status, value, tail.symm, by simpa only [← tail, List.append_nil] using leading⟩

-- §FS-host-boundary.caller: The maintained writer supplies its source and tag premises.
theorem actual_response_prefix (status : Nat) (value : GatewayWire.Value)
    (statusBound : status < 256 ^ 4)
    (sizeBound : (GatewayWire.encodeResponse status value).size ≤ GatewayWire.responseMax)
    {parsedStatus : Nat} {parsedValue : Value} {parsedBytes pending : List Nat}
    (parsed : SourceResponseEncoding parsedStatus parsedValue parsedBytes)
    (parsedCanonical : Canonical (.value parsedValue))
    (leading : GatewayRequestCode.byteView (GatewayWire.encodeResponse status value) = parsedBytes ++ pending) :
    status = parsedStatus ∧ view value = parsedValue ∧ pending = [] ∧
      GatewayRequestCode.byteView (GatewayWire.encodeResponse status value) = parsedBytes :=
  response_complete_prefix (source_response_actual status value statusBound sizeBound)
    parsed (canonical_view value) parsedCanonical leading

-- §REQ-proof-integrity.statement: The broad relation really does contain excluded ambiguous tags.
theorem noncanonical_scalar_prefix :
    SourceEncoded (.value .null) [0] ∧
    SourceEncoded (.value (.scalar 0 [])) ([0] ++ GatewayWords.encode 8 0) ∧
    ¬ Canonical (.value (.scalar 0 [])) := by
  refine ⟨.null [0] (by simp [GatewayWords.Encoding, GatewayWords.decode]), ?_, ?_⟩
  · simpa only [List.append_nil] using
      (SourceEncoded.scalar 0 [] [0] (GatewayWords.encode 8 0)
        (by simp [GatewayWords.Encoding, GatewayWords.decode]) (by decide) (GatewayWords.encode_encoding 8 0 (by decide)))
  · intro claimed
    cases claimed with
    | scalar _ _ valid => omega

end LeanCage.Host.GatewayFraming
