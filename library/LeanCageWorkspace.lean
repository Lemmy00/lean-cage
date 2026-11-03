import LeanCageM3
import Std.Data.TreeMap.Raw.Lemmas
import Std.Data.TreeMap.Raw.WF
import Init.Data.String.Lemmas.Pattern.Find.Char

namespace LeanCage.Workspace

-- §FS-linux-product.operation: Stable public library names; there is one implementation.
abbrev Policy := LeanCageM3.Policy
abbrev Result := LeanCageM3.Result
abbrev decodePolicy := LeanCageM3.decodePolicy
abbrev decodeResult := LeanCageM3.decodeResult
abbrev validatePolicy := LeanCageM3.validatePolicy
abbrev filterBytes := LeanCageM3.Filter.bytes
abbrev prepare := LeanCageM3.planArgs
-- §FS-linux-product.proofs: Typed callers must pass the same bounds checks as byte callers.
def execute (policy : Policy) (preflight : Bool) :
    IO (Except String (Result × Lean.Json)) :=
  match validatePolicy policy with
  | .error error => pure (.error error)
  | .ok accepted => LeanCageM3.invoke accepted preflight

abbrev check (policy : Policy) := execute policy true
abbrev run (policy : Policy) := execute policy false
abbrev report := LeanCageM3.detailedReport

-- §FS-linux-product.proofs: Kernel-checked equalities bind library consumers to audited code.
theorem policy_definition : decodePolicy = LeanCageM3.decodePolicy := rfl
theorem result_definition : decodeResult = LeanCageM3.decodeResult := rfl
theorem filter_definition : filterBytes = LeanCageM3.Filter.bytes := rfl
theorem check_definition (policy : Policy) : check policy = execute policy true := rfl
theorem run_definition (policy : Policy) : run policy = execute policy false := rfl

theorem accepted_policy_executes (policy : Policy) (preflight : Bool)
    (accepted : validatePolicy policy = .ok policy) :
    execute policy preflight = LeanCageM3.invoke policy preflight := by
  simp [execute, accepted]

theorem rejected_policy_is_pure (policy : Policy) (preflight : Bool)
    (invalid : LeanCageM3.limitsValid policy.limits = false ∨
      LeanCageM3.argvValid policy.argv = false) :
    execute policy preflight = pure (.error "policy exceeds supported bounds") := by
  rcases invalid with limits | arguments
  · simp [execute, validatePolicy, LeanCageM3.validatePolicy, limits]
  · simp [execute, validatePolicy, LeanCageM3.validatePolicy, arguments]

theorem supported_policy_inhabited :
    ∃ policy : Policy, policy.argv = #["/bin/sh", "-c", "true"] ∧
      validatePolicy policy = .ok policy := by
  refine ⟨⟨#["/bin/sh", "-c", "true"], none, none, false,
    ⟨16777216, 4, 1000, 100000, 10000, 10, 1048576, 64, 0, 0, 0⟩⟩, rfl, ?_⟩
  apply (LeanCageM3.validatePolicy_iff _ _).mpr
  refine ⟨rfl, by decide, ?_⟩
  simp only [LeanCageM3.argvValid, ← Array.all_toList, ← Array.foldl_toList,
    String.contains_char_eq]
  decide

-- §FS-linux-product.proofs: Use map laws rather than expanding balanced-tree computations.
private theorem object_lookup (fields : List (String × Lean.Json)) (key : String) :
    (Lean.Json.mkObj fields).getObjVal? key =
      match fields.findSomeRev? (fun pair => if compare pair.1 key = .eq then some pair.2 else none) with
      | some value => .ok value
      | none => .error s!"property not found: {key}" := by
  change (match (Std.TreeMap.Raw.ofList fields compare)[key]? with
    | some value => (Except.ok value : Except String Lean.Json)
    | none => Except.error s!"property not found: {key}") = _
  rw [Std.TreeMap.Raw.ofList_eq_insertMany_empty,
    Std.TreeMap.Raw.getElem?_insertMany_list Std.TreeMap.Raw.WF.emptyc]
  simp

private theorem extend_value (tree : Std.TreeMap.Raw String Lean.Json compare)
    (wellformed : tree.WF) (more : List (String × Lean.Json)) (key : String) (value : Lean.Json)
    (original : (Lean.Json.obj tree).getObjVal? key = .ok value)
    (untouched : (more.map Prod.fst).contains key = false) :
    (Lean.Json.mkObj (tree.toList ++ more)).getObjVal? key = .ok value := by
  have lookup : tree[key]? = some value := by
    cases found : tree[key]? with
    | none => simp [Lean.Json.getObjVal?, found] at original
    | some got =>
      change (match tree[key]? with
        | some v => (Except.ok v : Except String Lean.Json)
        | none => Except.error s!"property not found: {key}") = .ok value at original
      rw [found] at original
      cases original
      rfl
  have roundtrip : (Std.TreeMap.Raw.ofList tree.toList compare)[key]? = some value :=
    Std.TreeMap.Raw.getElem?_ofList_of_mem (by simp)
      (Std.TreeMap.Raw.distinct_keys_toList wellformed)
      ((Std.TreeMap.Raw.mem_toList_iff_getElem?_eq_some wellformed).mpr lookup)
  change (match (Std.TreeMap.Raw.ofList (tree.toList ++ more) compare)[key]? with
    | some found => (Except.ok found : Except String Lean.Json)
    | none => Except.error s!"property not found: {key}") = _
  rw [Std.TreeMap.Raw.ofList_eq_insertMany_empty, Std.TreeMap.Raw.insertMany_append,
    ← Std.TreeMap.Raw.ofList_eq_insertMany_empty,
    Std.TreeMap.Raw.getElem?_insertMany_list_of_contains_eq_false
      Std.TreeMap.Raw.WF.ofList untouched, roundtrip]

-- §FS-linux-product.proofs: Publication changes storage status without erasing observed entry.
theorem publication_entry (r : Result) (p : Policy) (identity : Lean.Json)
    (status : String) (error : Option String) :
    (LeanCageM3.reportStorage (report r p identity) status error).getObjVal? "entry" =
      .ok (Lean.toJson r.entry.label) := by
  unfold report LeanCageM3.reportStorage
  apply extend_value _ Std.TreeMap.Raw.WF.ofList _ _ _ _ (by rfl)
  apply extend_value _ Std.TreeMap.Raw.WF.ofList _ _ _ _ (by rfl)
  change (LeanCageM3.Result.json r).getObjVal? "entry" = _
  rw [LeanCageM3.Result.json, object_lookup]
  simp [List.findSomeRev?]

theorem publication_cleanup (r : Result) (p : Policy) (identity : Lean.Json)
    (status : String) (error : Option String) :
    (LeanCageM3.reportStorage (report r p identity) status error).getObjVal? "cleanup" =
      .ok (Lean.toJson (if r.clean then "complete" else "unknown")) := by
  unfold report LeanCageM3.reportStorage
  apply extend_value _ Std.TreeMap.Raw.WF.ofList _ _ _ _ (by rfl)
  apply extend_value _ Std.TreeMap.Raw.WF.ofList _ _ _ _ (by rfl)
  change (LeanCageM3.Result.json r).getObjVal? "cleanup" = _
  rw [LeanCageM3.Result.json, object_lookup]
  simp [List.findSomeRev?]

end LeanCage.Workspace
