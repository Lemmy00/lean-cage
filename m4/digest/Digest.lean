-- SPDX-License-Identifier: Apache-2.0
-- §AR-m4-controller.digest: Exact byte predicate and live digest-text representation.
import Arguments

namespace LeanCageM4.Digest
open LeanCageM3 LeanCageM4.Plan

def hexByte (b : Nat) : Bool := (48 ≤ b && b ≤ 57) || (97 ≤ b && b ≤ 102)

def hexBytes : List Nat → Bool
  | [] => true
  | b :: rest => hexByte b && hexBytes rest

def byteCount : List Nat → Nat
  | [] => 0
  | _ :: rest => 1 + byteCount rest

def nativeDigestBytes (bytes : List Nat) : Bool := (byteCount bytes == 64) && hexBytes bytes

def hexChar (c : Char) : Bool := ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')

def digestText (text : String) : Bool := (text.length == 64) && text.toList.all hexChar

theorem byteCount_length (bytes : List Nat) : byteCount bytes = bytes.length := by
  induction bytes with
  | nil => rfl
  | cons b rest ih => simp only [byteCount, List.length_cons, ih]; omega

theorem hexBytes_all (bytes : List Nat) : hexBytes bytes = bytes.all hexByte := by
  induction bytes with
  | nil => rfl
  | cons b rest ih => simp only [hexBytes, List.all_cons, ih]

theorem nativeDigestBytes_exact (bytes : List Nat) :
    nativeDigestBytes bytes = true ↔ bytes.length = 64 ∧
      ∀ b ∈ bytes, (48 ≤ b ∧ b ≤ 57) ∨ (97 ≤ b ∧ b ≤ 102) := by
  simp [nativeDigestBytes, byteCount_length, hexBytes_all, List.all_eq_true, hexByte]

theorem hexChar_toNat (c : Char) : hexChar c = hexByte c.toNat := by
  rfl

theorem valid_characters_ascii (text : String) (valid : text.toList.all hexChar = true) :
    ∀ c ∈ text.toList, c.toNat < 128 := by
  rw [List.all_eq_true] at valid
  intro c mem
  have good := valid c mem
  rw [hexChar_toNat] at good
  simp only [hexByte, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at good
  omega

theorem digest_utf8 (text : String) (valid : text.toList.all hexChar = true) :
    text.toUTF8.data.toList.map UInt8.toNat = text.toList.map Char.toNat := by
  simpa using ascii_utf8 text.toList (valid_characters_ascii text valid)

theorem valid_digest_bytes (text : String) (valid : digestText text = true) :
    nativeDigestBytes (text.toUTF8.data.toList.map UInt8.toNat) = true := by
  simp only [digestText, Bool.and_eq_true, beq_iff_eq] at valid
  rw [digest_utf8 text valid.2]
  simp only [nativeDigestBytes, byteCount_length, List.length_map, hexBytes_all,
    List.all_map, Function.comp_def, ← hexChar_toNat]
  simpa only [String.length_toList, valid.1, beq_self_eq_true, Bool.true_and] using valid.2

theorem valid_digest_no_nul (text : String) (valid : digestText text = true) :
    (0 : UInt8) ∉ text.toUTF8.data.toList := by
  intro member
  have good := (nativeDigestBytes_exact _).mp (valid_digest_bytes text valid)
  have zero := good.2 0 (List.mem_map.mpr ⟨0, member, rfl⟩)
  omega

theorem valid_digest_size (text : String) (valid : digestText text = true) :
    text.utf8ByteSize = 64 := by
  have size := ((nativeDigestBytes_exact _).mp (valid_digest_bytes text valid)).1
  simp only [List.length_map, Array.length_toList] at size
  exact size

-- §AR-m4-controller.digest: Name the existing private declaration without changing its visibility.
open Lean in
macro "liveDigestField" : term => pure (mkIdent
  (Name.str (Name.str (Name.num `_private.LeanCageM3.Policy 0) "LeanCageM3") "digestField"))

theorem live_digest_equation (j : Lean.Json) (name : String) :
    liveDigestField j name = (do
      let value ← j.getObjVal? name
      if value.isNull then return none
      let text ← value.getStr?
      let rest := (text.drop 7).toString
      if !text.startsWith "sha256:" || rest.length != 64 ||
          !rest.toList.all (fun c => ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')) then
        throw "invalid artifact digest"
      return some text) := rfl

theorem parsed_digest_valid (j : Lean.Json) (name text : String)
    (parsed : liveDigestField j name = .ok (some text)) :
    text.startsWith "sha256:" = true ∧ digestText (text.drop 7).toString = true := by
  rw [live_digest_equation] at parsed
  cases field : j.getObjVal? name with
  | error message => simp [field, Bind.bind, Except.bind] at parsed
  | ok value =>
    simp only [field, Bind.bind, Except.bind] at parsed
    split at parsed
    · cases parsed
    · cases string : value.getStr? with
      | error message => simp [string] at parsed
      | ok result =>
        simp only [string] at parsed
        split at parsed
        · cases parsed
        · rename_i valid
          change Except.ok (some result) = Except.ok (some text) at parsed
          simp only [Except.ok.injEq, Option.some.injEq] at parsed
          subst result
          simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Bool.not_eq_false', bne_eq_false_iff_eq] at valid
          refine ⟨valid.1.1, ?_⟩
          simp only [digestText, Bool.and_eq_true, beq_iff_eq]
          exact ⟨valid.1.2, valid.2⟩

theorem parsed_digest_bytes (j : Lean.Json) (name text : String)
    (parsed : liveDigestField j name = .ok (some text)) :
    nativeDigestBytes ((text.drop 7).toString.toUTF8.data.toList.map UInt8.toNat) = true :=
  valid_digest_bytes _ (parsed_digest_valid j name text parsed).2

theorem parsed_digest_memory_shape (j : Lean.Json) (name text : String)
    (parsed : liveDigestField j name = .ok (some text)) :
    (text.drop 7).toString.utf8ByteSize = 64 ∧
      (0 : UInt8) ∉ (text.drop 7).toString.toUTF8.data.toList :=
  ⟨valid_digest_size _ (parsed_digest_valid j name text parsed).2,
   valid_digest_no_nul _ (parsed_digest_valid j name text parsed).2⟩

theorem native_workspace_digest_bytes (executable : String) (p : Policy) (pid : Nat) (pre : Bool)
    (j : Lean.Json) (name text : String) (field : p.workspaceInput = some text)
    (parsed : liveDigestField j name = .ok (some text)) :
    ((nativeArgs executable p pid pre)[14]?).map
      (fun s => nativeDigestBytes (s.toUTF8.data.toList.map UInt8.toNat)) = some true := by
  rw [(native_digests executable p pid pre).1, field]
  exact congrArg some (parsed_digest_bytes j name text parsed)

theorem native_stdin_digest_bytes (executable : String) (p : Policy) (pid : Nat) (pre : Bool)
    (j : Lean.Json) (name text : String) (field : p.stdinInput = some text)
    (parsed : liveDigestField j name = .ok (some text)) :
    ((nativeArgs executable p pid pre)[15]?).map
      (fun s => nativeDigestBytes (s.toUTF8.data.toList.map UInt8.toNat)) = some true := by
  rw [(native_digests executable p pid pre).2, field]
  exact congrArg some (parsed_digest_bytes j name text parsed)

set_option maxRecDepth 4000 in
theorem native_digest_examples :
    nativeDigestBytes (List.replicate 64 48) = true ∧
    nativeDigestBytes (List.replicate 64 102) = true ∧
    nativeDigestBytes (List.replicate 63 97) = false ∧
    nativeDigestBytes (List.replicate 65 97) = false ∧
    nativeDigestBytes (List.replicate 63 97 ++ [65]) = false ∧
    nativeDigestBytes (List.replicate 63 97 ++ [255]) = false := by decide

set_option maxRecDepth 4000 in
theorem parsed_digest_examples :
    liveDigestField (Lean.Json.mkObj [("digest", .null)]) "digest" = .ok none ∧
    liveDigestField (Lean.Json.mkObj [("digest", .str
      ("sha256:" ++ String.ofList (List.replicate 64 'a')))]) "digest" =
      .ok (some ("sha256:" ++ String.ofList (List.replicate 64 'a'))) ∧
    liveDigestField (Lean.Json.mkObj [("digest", .str
      ("sha256:" ++ String.ofList (List.replicate 64 'A')))]) "digest" =
      .error "invalid artifact digest" ∧
    liveDigestField (Lean.Json.mkObj [("digest", .str
      ("sha512:" ++ String.ofList (List.replicate 64 'a')))]) "digest" =
      .error "invalid artifact digest" := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals cbv

end LeanCageM4.Digest
