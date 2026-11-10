import LeanCageHost.Json

namespace LeanCage.Host.Json

-- §FS-host-boundary.artifacts: The syntax theorem describes the bytes actually accepted by parse.
theorem parseWithDepth_success {bytes : ByteArray} {limit depth : Nat} {value : Value}
    (success : parseWithDepth bytes limit depth = .ok value) :
    ∃ (text : String) (rest : List Char),
      String.fromUTF8? bytes = some text ∧ Syntax text.toList value rest ∧ Spaces rest [] ∧
      WithinDepth depth value ∧ bytes.size ≤ limit := by
  unfold parseWithDepth at success
  cases result : parseCertified bytes limit depth with
  | error message => simp [result, Except.map] at success
  | ok parsed =>
    simp only [result, Except.map, Except.ok.injEq] at success
    cases success
    exact parsed.property

theorem parse_success {bytes : ByteArray} {limit : Nat} {value : Value}
    (success : parse bytes limit = .ok value) :
    bytes.size ≤ limit ∧ WithinDepth 64 value ∧
      ∃ (text : String) (rest : List Char), bytes.IsValidUTF8 ∧ text.toUTF8 = bytes ∧
        Syntax text.toList value rest ∧ Spaces rest [] := by
  obtain ⟨text, rest, decode, grammar, trailing, depth, bounded⟩ := parseWithDepth_success success
  obtain ⟨utf8, exactBytes⟩ := strict_utf8 decode
  exact ⟨bounded, depth, text, rest, utf8, exactBytes, grammar, trailing⟩

theorem parse_too_large {bytes : ByteArray} {limit depth : Nat} (exceeded : limit < bytes.size) :
    parseWithDepth bytes limit depth = .error "JSON byte limit exceeded" := by
  simp [parseWithDepth, parseCertified, Nat.not_le.mpr exceeded, Except.map]

-- §AR-host-boundary.interfaces: Preserve numeric lexemes and recursive key uniqueness.
inductive WellFormed : Value → Prop where
  | null : WellFormed .null
  | bool (value : Bool) : WellFormed (.bool value)
  | number {bytes : List UInt8}
      (token : ∃ chars state, NumberPrefix chars state ∧ numberAccepting state = true ∧
        bytes = encodedChars chars) : WellFormed (.number bytes)
  | string (value : String) : WellFormed (.string value)
  | array {values : Array Value} (children : ∀ value ∈ values.toList, WellFormed value) :
      WellFormed (.array values)
  | object {fields : List (String × Value)}
      (children : ∀ field ∈ fields, WellFormed field.2) (keys : (fields.map Prod.fst).Nodup) :
      WellFormed (.object fields)

theorem syntax_wellFormed {input rest : List Char} {value : Value}
    (grammar : Syntax input value rest) : WellFormed value := by
  refine Syntax.rec
    (motive_1 := fun _ value _ _ => WellFormed value)
    (motive_2 := fun _ values _ _ => ∀ value ∈ values.toList, WellFormed value)
    (motive_3 := fun _ fields _ _ =>
      (∀ field ∈ fields, WellFormed field.2) ∧ (fields.map Prod.fst).Nodup)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ grammar
  · intro input start rest value space valueSyntax ih
    exact ih
  · intro rest
    exact .null
  · intro rest
    exact .bool true
  · intro rest
    exact .bool false
  · intro input rest bytes token
    obtain ⟨chars, state, _, earlier, accepting, exactBytes⟩ := token
    exact .number ⟨chars, state, earlier, accepting, exactBytes⟩
  · intro input decoded rest token
    exact .string _
  · intro input rest space
    exact .array (by simp)
  · intro input after rest values members space children
    exact .array children
  · intro input rest space
    exact .object (by simp) (by simp)
  · intro input after rest fields members space children
    exact .object children.1 children.2
  · intro input rest value valueSyntax child item present
    change item ∈ [value] at present
    simp only [List.mem_singleton] at present
    cases present
    exact child
  · intro input after more rest values value earlier space valueSyntax old child item present
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at present
    rcases present with oldMember | rfl
    · exact old _ oldMember
    · exact child
  · intro input afterKey more rest key value keySyntax colon valueSyntax keyMeaning child
    exact ⟨by simpa using child, by simp⟩
  · intro input after nextKey afterKey more rest fields key value earlier comma keySyntax colon
      valueSyntax fresh old keyMeaning child
    constructor
    · intro item present
      simp only [List.mem_append, List.mem_singleton] at present
      rcases present with oldMember | rfl
      · exact old.1 _ oldMember
      · exact child
    · rw [List.map_append]
      exact List.nodup_append.mpr ⟨old.2, by simp, by
        intro item present other singleton equal
        have otherKey : other = key := by simpa using singleton
        have itemKey : item = key := equal.trans otherKey
        exact fresh (itemKey ▸ present)⟩

theorem parse_wellFormed {bytes : ByteArray} {limit : Nat} {value : Value}
    (success : parse bytes limit = .ok value) : WellFormed value := by
  obtain ⟨_, _, _, _, _, _, grammar, _⟩ := parse_success success
  exact syntax_wellFormed grammar

-- §FS-host-boundary.artifacts: Every occurrence of a decoded object key is unique.
theorem parse_object_unique {bytes : ByteArray} {limit : Nat} {fields : List (String × Value)}
    (success : parse bytes limit = .ok (.object fields)) : (fields.map Prod.fst).Nodup := by
  cases parse_wellFormed success with | object _ keys => exact keys

theorem get_object_exact (fields : List (String × Value)) (key : String) (value : Value)
    (unique : (fields.map Prod.fst).Nodup) :
    get? (.object fields) key = some value ↔ (key, value) ∈ fields := by
  induction fields with
  | nil => simp [get?]
  | cons field rest ih =>
    rcases field with ⟨name, head⟩
    have keys := List.nodup_cons.mp unique
    by_cases same : name = key
    · subst name
      have absent : (key, value) ∉ rest := by
        intro member
        exact keys.1 (List.mem_map.mpr ⟨(key, value), member, rfl⟩)
      simp [get?, List.find?, absent, eq_comm]
    · have reverse : key ≠ name := fun equal => same equal.symm
      have unmatched : (name == key) = false := beq_eq_false_iff_ne.mpr same
      simpa [get?, List.find?, unmatched, reverse] using ih keys.2

-- §FS-host-boundary.artifacts: The getter interprets canonical base-ten bytes without coercions.
theorem naturalToken_cons (byte : UInt8) (rest : List UInt8) (value : Nat) :
    NaturalToken (byte :: rest) value ↔
      (byte = 48 ∧ rest = [] ∧ value = 0) ∨
      ((49 ≤ byte.toNat ∧ byte.toNat ≤ 57) ∧ NaturalDigits (byte.toNat - 48) rest value) := by
  constructor
  · rintro (⟨zero, meaning⟩ | ⟨first, tail, shape, lower, upper, meaning⟩)
    · have shape := List.cons.inj zero
      exact .inl ⟨shape.1, shape.2, meaning⟩
    · cases shape
      exact .inr ⟨⟨lower, upper⟩, meaning⟩
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨⟨lower, upper⟩, meaning⟩)
    · exact .inl ⟨rfl, rfl⟩
    · exact .inr ⟨byte, rest, rfl, lower, upper, meaning⟩

theorem naturalToken_exact (bytes : List UInt8) (value : Nat) :
    naturalToken? bytes = some value ↔ NaturalToken bytes value := by
  cases bytes with
  | nil => simp [naturalToken?, NaturalToken]
  | cons byte rest =>
    by_cases zero : byte = 48
    · subst byte
      cases rest <;> simp [naturalToken?, naturalToken_cons, eq_comm]
    · by_cases positive : 49 ≤ byte.toNat ∧ byte.toNat ≤ 57
      · simp [naturalToken?, naturalToken_cons, zero, positive, naturalDigits_exact]
      · simp [naturalToken?, naturalToken_cons, zero, positive]

theorem natural_exact (value : Value) (number : Nat) :
    natural? value = some number ↔ ∃ bytes, value = .number bytes ∧ NaturalToken bytes number := by
  cases value <;> simp [natural?, naturalToken_exact]

theorem naturalTokenBelow_exact (bytes : List UInt8) (maximum value : Nat) :
    naturalTokenBelow? bytes maximum = some value ↔
      naturalToken? bytes = some value ∧ value ≤ maximum := by
  cases bytes with
  | nil => simp [naturalTokenBelow?, naturalToken?]
  | cons byte rest =>
    by_cases zero : byte = 48
    · subst byte
      cases rest <;> simp [naturalTokenBelow?, naturalToken?, eq_comm] <;> omega
    · by_cases positive : 49 ≤ byte.toNat ∧ byte.toNat ≤ 57
      · simp [naturalTokenBelow?, naturalToken?, zero, positive,
          naturalDigitsBelow_exact, naturalDigits_exact]
      · simp [naturalTokenBelow?, naturalToken?, zero, positive]

theorem naturalBelow_exact (value : Value) (maximum number : Nat) :
    naturalBelow? value maximum = some number ↔ natural? value = some number ∧ number ≤ maximum := by
  cases value <;> simp [naturalBelow?, natural?, naturalTokenBelow_exact]

-- §FS-host-boundary.artifacts: Hexadecimal rendering denotes the original low scalar value.
theorem hexDigit_hexChar {digit : Nat} (bounded : digit < 16) :
    hexDigit (hexChar digit) = some digit := by
  have choices : digit = 0 ∨ digit = 1 ∨ digit = 2 ∨ digit = 3 ∨ digit = 4 ∨ digit = 5 ∨
      digit = 6 ∨ digit = 7 ∨ digit = 8 ∨ digit = 9 ∨ digit = 10 ∨ digit = 11 ∨
      digit = 12 ∨ digit = 13 ∨ digit = 14 ∨ digit = 15 := by omega
  rcases choices with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst digit <;> decide

theorem escaped_char_meaning (c : Char) {input decoded rest : List Char}
    (tail : StringBody input decoded rest) :
    StringBody (escapeChar c ++ input) (c :: decoded) rest := by
  by_cases quote : c = '"'
  · subst c
    simpa [escapeChar] using StringBody.escaped (escape := '"') rfl tail
  · by_cases slash : c = '\\'
    · subst c
      simpa [escapeChar] using StringBody.escaped (escape := '\\') rfl tail
    · by_cases control : c.toNat < 32
      · have upper : c.toNat / 16 < 16 := by omega
        have lower : c.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
        have digits : hexFour '0' '0' (hexChar (c.toNat / 16)) (hexChar (c.toNat % 16)) =
            some c.toNat := by
          simp only [hexFour, show hexDigit '0' = some 0 from rfl,
            hexDigit_hexChar upper, hexDigit_hexChar lower]
          dsimp
          simp only [Nat.zero_add]
          change some (16 * (c.toNat / 16) + c.toNat % 16) = some c.toNat
          congr 1
          omega
        have valid : c.toNat.isValidChar := c.valid
        have scalar : Char.ofNatAux c.toNat valid = c := by
          apply Char.ext
          rfl
        simpa [escapeChar, quote, slash, control, scalar] using StringBody.scalar digits valid tail
      · simpa [escapeChar, quote, slash, control] using
          StringBody.raw ⟨by omega, quote, slash⟩ tail

theorem escaped_list_meaning (chars : List Char) {input decoded rest : List Char}
    (tail : StringBody input decoded rest) :
    StringBody (chars.flatMap escapeChar ++ input) (chars ++ decoded) rest := by
  induction chars with
  | nil => exact tail
  | cons c chars ih =>
    simpa [List.flatMap_cons, List.append_assoc] using escaped_char_meaning c ih

theorem quoted_string_meaning (text : String) :
    StringBody (text.toList.flatMap escapeChar ++ ['"']) text.toList [] := by
  simpa using escaped_list_meaning text.toList (StringBody.close [])

-- §AR-host-boundary.interfaces: The byte grammar fixes the serialized semantic value.
mutual
  inductive ByteSyntax : List UInt8 → Value → Prop where
    | null : ByteSyntax [110, 117, 108, 108] .null
    | true : ByteSyntax [116, 114, 117, 101] (.bool true)
    | false : ByteSyntax [102, 97, 108, 115, 101] (.bool false)
    | number {chars : List Char} {state : NumberState}
        (token : NumberPrefix chars state) (accepting : numberAccepting state = true) :
        ByteSyntax (encodedChars chars) (.number (encodedChars chars))
    | string {text : String} {body : List Char} (token : StringBody body text.toList []) :
        ByteSyntax (encodedChars ('"' :: body)) (.string text)
    | array {values : Array Value} {chunks : List (List UInt8)}
        (members : ByteArrayMembers values.toList chunks) :
        ByteSyntax ([91] ++ List.intercalate [44] chunks ++ [93]) (.array values)
    | object {fields : List (String × Value)} {chunks : List (List UInt8)}
        (members : ByteObjectMembers fields chunks) (keys : (fields.map Prod.fst).Nodup) :
        ByteSyntax ([123] ++ List.intercalate [44] chunks ++ [125]) (.object fields)

  inductive ByteArrayMembers : List Value → List (List UInt8) → Prop where
    | nil : ByteArrayMembers [] []
    | cons {value : Value} {bytes : List UInt8} {values : List Value} {chunks : List (List UInt8)}
        (head : ByteSyntax bytes value) (tail : ByteArrayMembers values chunks) :
        ByteArrayMembers (value :: values) (bytes :: chunks)

  inductive ByteObjectMembers : List (String × Value) → List (List UInt8) → Prop where
    | nil : ByteObjectMembers [] []
    | cons {key : String} {value : Value} {bytes : List UInt8}
        {keyBody : List Char} {fields : List (String × Value)} {chunks : List (List UInt8)}
        (keyToken : StringBody keyBody key.toList [])
        (valueToken : ByteSyntax bytes value) (tail : ByteObjectMembers fields chunks) :
        ByteObjectMembers ((key, value) :: fields)
          ((encodedChars ('"' :: keyBody) ++ [58] ++ bytes) :: chunks)
end

private theorem map_attach_value {α β : Type} (values : List α) (function : α → β) :
    values.attach.map (fun value => function value.val) = values.map function := by
  induction values with
  | nil => rfl
  | cons value rest _ => simp [List.attach_cons, List.map_map]

private theorem render_array_members (values : List Value)
    (children : ∀ value ∈ values, ByteSyntax (renderRaw value) value) :
    ByteArrayMembers values (values.map renderRaw) := by
  induction values with
  | nil => exact .nil
  | cons value rest ih =>
    exact .cons (children value (by simp)) (ih (by intro item present; exact children item (by simp [present])))

private theorem render_object_members (fields : List (String × Value))
    (children : ∀ field ∈ fields, ByteSyntax (renderRaw field.2) field.2) :
    ByteObjectMembers fields (fields.map (fun field =>
      encodedChars (quotedChars field.1) ++ [58] ++ renderRaw field.2)) := by
  induction fields with
  | nil => exact .nil
  | cons field rest ih =>
    exact .cons (quoted_string_meaning field.1) (children field (by simp))
      (ih (by intro item present; exact children item (by simp [present])))

-- §FS-host-boundary.publication: Rendering preserves the semantic value in a JSON byte grammar.
theorem render_meaning {value : Value} (valid : WellFormed value) :
    ByteSyntax (render value).data.toList value := by
  change ByteSyntax (renderRaw value) value
  induction valid with
  | null => simpa only [renderRaw] using ByteSyntax.null
  | bool value =>
    cases value with
    | false => simpa only [renderRaw] using ByteSyntax.false
    | true => simpa only [renderRaw] using ByteSyntax.true
  | number token =>
    obtain ⟨chars, state, token, accepting, rfl⟩ := token
    rw [renderRaw]
    exact .number token accepting
  | string text =>
    rw [renderRaw]
    exact .string (quoted_string_meaning text)
  | array children ih =>
    rw [renderRaw]
    simp only [map_attach_value]
    exact .array (render_array_members _ ih)
  | object children keys ih =>
    rw [renderRaw]
    rw [map_attach_value _ (fun (field : String × Value) =>
      encodedChars (quotedChars field.1) ++ [58] ++ renderRaw field.2)]
    exact .object (render_object_members _ ih) keys

-- §FS-host-boundary.artifacts: A useful object and an escaped-key denial inhabit the actual parser.
theorem useful_document :
    ∃ value, parse "{\"value\":true}".toUTF8 64 = .ok value := by
  have computed : (match parse "{\"value\":true}".toUTF8 64 with
      | .ok _ => true | .error _ => false) = true := by decide +kernel
  cases result : parse "{\"value\":true}".toUTF8 64 with
  | ok value => exact ⟨value, rfl⟩
  | error message =>
    rw [result] at computed
    contradiction

theorem escaped_duplicate_rejected :
    parse "{\"a\":0,\"\\u0061\":1}".toUTF8 64 = .error "duplicate decoded JSON object key" := by
  have computed : (match parse "{\"a\":0,\"\\u0061\":1}".toUTF8 64 with
      | .error message => message == "duplicate decoded JSON object key" | .ok _ => false) = true := by decide +kernel
  cases result : parse "{\"a\":0,\"\\u0061\":1}".toUTF8 64 with
  | ok value =>
    rw [result] at computed
    contradiction
  | error message =>
    simp only [result] at computed
    have exactMessage := eq_of_beq computed
    cases exactMessage
    rfl

end LeanCage.Host.Json
