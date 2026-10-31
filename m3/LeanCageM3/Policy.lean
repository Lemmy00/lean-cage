import Lean

namespace LeanCageM3
open Lean
open Std.Internal.Parsec Std.Internal.Parsec.String

-- §FS-workspace.policy: Bounded parser rejects duplicate keys before map construction and numeric
-- coercions.
namespace StrictJson

private def punctuation (expected : Char) : Parser Unit := do
  if (← any) != expected then fail "unexpected JSON punctuation"
  ws

private def string : Parser String := do
  if (← any) != '"' then fail "expected JSON string"
  let s ← Json.Parser.str
  if s.utf8ByteSize > 4096 || s.contains '\x00' then fail "oversized or NUL string"
  ws
  return s

private def number : Parser Json := do
  let first ← any
  let mut n := first.toNat - '0'.toNat
  let mut more := true
  while more do
    if ← isEof then more := false
    else
      let c ← peek!
      if c ≥ '0' && c ≤ '9' then
        if first == '0' then fail "leading zero"
        skip
        n := n * 10 + (c.toNat - '0'.toNat)
        if n > 18446744073709551615 then fail "integer overflow"
      else more := false
  ws
  return toJson n

mutual
  partial def value (depth : Nat) : Parser Json := do
    if depth > 16 then fail "JSON nesting exceeds profile"
    let c ← peek!
    if c == '{' then
      punctuation '{'
      object depth []
    else if c == '[' then
      punctuation '['
      array depth #[]
    else if c == '"' then return Json.str (← string)
    else if c == 'n' then skipString "null"; ws; return Json.null
    else if c ≥ '0' && c ≤ '9' then number
    else fail "unsupported JSON value"

  partial def object (depth : Nat) (fields : List (String × Json)) : Parser Json := do
    if (← peek!) == '}' then
      punctuation '}'
      return Json.mkObj fields.reverse
    if fields.length ≥ 32 then fail "too many object fields"
    let key ← string
    if fields.any (fun field => field.1 == key) then fail "duplicate JSON key"
    punctuation ':'
    let child ← value (depth + 1)
    let next := (key, child) :: fields
    if (← peek!) == '}' then
      punctuation '}'
      return Json.mkObj next.reverse
    punctuation ','
    if (← peek!) == '}' then fail "trailing comma"
    object depth next

  partial def array (depth : Nat) (items : Array Json) : Parser Json := do
    if (← peek!) == ']' then
      punctuation ']'
      return Json.arr items
    if items.size ≥ 128 then fail "too many array items"
    let child ← value (depth + 1)
    let next := items.push child
    if (← peek!) == ']' then
      punctuation ']'
      return Json.arr next
    punctuation ','
    if (← peek!) == ']' then fail "trailing comma"
    array depth next
end

def parse (bytes : ByteArray) : Except String Json := do
  if bytes.size > 65536 then throw "policy exceeds 65536 bytes"
  let s ← match String.fromUTF8? bytes with
    | some text => pure text
    | none => throw "invalid UTF-8"
  Parser.run (do ws; let j ← value 0; eof; pure j) s

end StrictJson

structure Limits where
  memory : Nat
  tasks : Nat
  quota : Nat
  period : Nat
  cpu : Nat
  wall : Nat
  workspace : Nat
  inodes : Nat
  stdin : Nat
  stdout : Nat
  stderr : Nat
  deriving DecidableEq, Repr

structure Policy where
  argv : Array String
  workspaceInput : Option String
  stdinInput : Option String
  exportFiles : Bool
  limits : Limits
  deriving DecidableEq, Repr

def profile : String := "linux-x86_64-offline-workspace-m3-v1"
def runtimeDigest : String := "sha256:70bda1e795ded2a684ef9815955e05829b14ee5bb5c3eb2a940648e88f10fce9"

def limitsValid (l : Limits) : Bool :=
  (16777216 ≤ l.memory && l.memory ≤ 1073741824 && l.memory % 4096 == 0) &&
  (4 ≤ l.tasks && l.tasks ≤ 256) && (1000 ≤ l.quota && l.quota ≤ 100000) &&
  (l.period == 100000) && (10000 ≤ l.cpu && l.cpu ≤ 3600000000) &&
  (10 ≤ l.wall && l.wall ≤ 3600000) &&
  (1048576 ≤ l.workspace && l.workspace ≤ 268435456 && l.workspace % 4096 == 0) &&
  (64 ≤ l.inodes && l.inodes ≤ 65536) && l.stdin ≤ 67108864 &&
  l.stdout ≤ 16777216 && l.stderr ≤ 16777216

def argvValid (argv : Array String) : Bool :=
  (0 < argv.size && argv.size ≤ 64) &&
  (argv[0]? == some "/bin/sh" || argv[0]? == some "/usr/local/bin/python3") &&
  argv.all (fun s => !s.isEmpty && s.utf8ByteSize ≤ 4096 && !s.contains '\x00') &&
  argv.foldl (fun n s => n + s.utf8ByteSize + 1) 0 ≤ 16384

private def exactFields (j : Json) (expected : List String) : Except String Unit := do
  let object ← j.getObj?
  let keys := object.toList.map Prod.fst
  if keys.length != expected.length || !keys.all expected.contains then
    throw "unknown or missing policy field"

private def field (j : Json) (name : String) : Except String Json := j.getObjVal? name

private def natural (j : Json) (name : String) : Except String Nat := do
  (← field j name).getNat?

private def digestField (j : Json) (name : String) : Except String (Option String) := do
  let value ← field j name
  if value.isNull then return none
  let text ← value.getStr?
  let rest := (text.drop 7).toString
  if !text.startsWith "sha256:" || rest.length != 64 ||
      !rest.toList.all (fun c => ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')) then
    throw "invalid artifact digest"
  return some text

-- §FS-workspace.policy: Parsing yields a concrete versioned value; platform/artifact admission is
-- separate.
private def parsePolicy (bytes : ByteArray) : Except String Policy := do
  let j ← StrictJson.parse bytes
  exactFields j ["schema_version", "profile", "runtime_manifest_digest", "workspace_input",
    "stdin_input", "argv", "export", "limits"]
  if (← natural j "schema_version") != 1 || (← (← field j "profile").getStr?) != profile ||
      (← (← field j "runtime_manifest_digest").getStr?) != runtimeDigest then
    throw "unsupported policy/profile/runtime"
  let argv ← (← (← field j "argv").getArr?).mapM Json.getStr?
  let workspaceInput ← digestField j "workspace_input"
  let stdinInput ← digestField j "stdin_input"
  let exportMode ← (← field j "export").getStr?
  if exportMode != "discard" && exportMode != "regular-files" then throw "invalid export choice"
  let limits ← field j "limits"
  exactFields limits ["memory_max_bytes", "tasks_max", "cpu_quota_us", "cpu_period_us",
    "cpu_budget_us", "wall_time_ms", "workspace_max_bytes", "workspace_max_inodes",
    "stdin_max_bytes", "stdout_max_bytes", "stderr_max_bytes"]
  let l : Limits := ⟨← natural limits "memory_max_bytes", ← natural limits "tasks_max",
    ← natural limits "cpu_quota_us", ← natural limits "cpu_period_us",
    ← natural limits "cpu_budget_us", ← natural limits "wall_time_ms",
    ← natural limits "workspace_max_bytes", ← natural limits "workspace_max_inodes",
    ← natural limits "stdin_max_bytes", ← natural limits "stdout_max_bytes",
    ← natural limits "stderr_max_bytes"⟩
  return ⟨argv, workspaceInput, stdinInput, exportMode == "regular-files", l⟩

-- §AR-workspace.proofs: An actual decoded policy carries both executable bounds checks.
def validatePolicy (policy : Policy) : Except String Policy :=
  if limitsValid policy.limits && argvValid policy.argv then .ok policy
  else .error "policy exceeds supported bounds"

def decodePolicy (bytes : ByteArray) : Except String Policy := do
  validatePolicy (← parsePolicy bytes)

theorem validatePolicy_iff (input output : Policy) :
    validatePolicy input = .ok output ↔
      output = input ∧ limitsValid input.limits = true ∧ argvValid input.argv = true := by
  unfold validatePolicy
  split
  · rename_i valid
    simp only [Bool.and_eq_true] at valid
    constructor
    · intro accepted
      cases accepted
      exact ⟨rfl, valid.1, valid.2⟩
    · rintro ⟨rfl, _, _⟩
      rfl
  · rename_i invalid
    constructor
    · intro impossible
      cases impossible
    · rintro ⟨rfl, limits, arguments⟩
      simp [limits, arguments] at invalid

theorem decodePolicy_bounds (bytes : ByteArray) (policy : Policy)
    (accepted : decodePolicy bytes = .ok policy) :
    limitsValid policy.limits = true ∧ argvValid policy.argv = true := by
  unfold decodePolicy at accepted
  cases parsed : parsePolicy bytes with
  | error message => simp [parsed, Bind.bind, Except.bind] at accepted
  | ok value =>
    rw [parsed] at accepted
    change validatePolicy value = .ok policy at accepted
    have result := (validatePolicy_iff value policy).mp accepted
    rcases result with ⟨rfl, limits, arguments⟩
    exact ⟨limits, arguments⟩

-- §AR-workspace.proofs: Exact byte-decoder decomposition; structural JSON recognition is explicit.
theorem decodePolicy_iff (bytes : ByteArray) (policy : Policy) :
    decodePolicy bytes = .ok policy ↔ parsePolicy bytes = .ok policy ∧
      limitsValid policy.limits = true ∧ argvValid policy.argv = true := by
  unfold decodePolicy
  cases parsed : parsePolicy bytes with
  | error message => simp [Bind.bind, Except.bind]
  | ok input =>
    change validatePolicy input = .ok policy ↔ Except.ok input = Except.ok policy ∧ _
    rw [validatePolicy_iff]
    constructor
    · rintro ⟨rfl, limits, arguments⟩; exact ⟨rfl, limits, arguments⟩
    · rintro ⟨same, limits, arguments⟩; cases same; exact ⟨rfl, limits, arguments⟩

end LeanCageM3
