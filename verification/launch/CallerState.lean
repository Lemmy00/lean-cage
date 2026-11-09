import LeanCageEntry.Program

namespace LeanCage.Entry

-- §AR-entry.caller: These opcodes cannot substitute registers or syscall results.
def NonSubstitutingRequest (request : Nat) : Prop :=
  request = 7 ∨ request = 16896 ∨ request = 16898

-- §FS-entry.provenance: A reused numeric PID denotes a different incarnation.
structure ProcessIdentity where
  pid : Nat
  incarnation : Nat
  positive : 1 ≤ pid
  bounded : pid ≤ 2147483647
  deriving DecidableEq

-- §AR-entry.caller.origin: Initial TRACEME options or the exact source-installed option word.
-- Both exclude PTRACE_O_SUSPEND_SECCOMP; arbitrary option words remain in TracerControl.
def TracerOptionsAllowed (options : Nat) : Prop := options = 0 ∨ options = 1048592

-- §AR-entry.caller.origin: Import the source's request and actual SETOPTIONS payload together.
def SourceSupervisor (request options : Nat) : Prop :=
  NonSubstitutingRequest request ∧ (request = 16896 → options = 1048592)

-- §AR-entry.caller.origin: The source interface retains actual log membership.
def SourceRequestMember (request : Nat) : List Nat → Prop
  | [] => False
  | first :: rest => request = first ∨ SourceRequestMember request rest

def SourceSupervisorUse (history : List Nat) (request options : Nat) : Prop :=
  SourceRequestMember request history ∧ SourceSupervisor request options

theorem source_request_member {request : Nat} {history : List Nat}
    (source : SourceRequestMember request history) : request ∈ history := by
  induction history with
  | nil => contradiction
  | cons first rest ih =>
    rcases source with same | later
    · exact List.mem_cons.mpr (Or.inl same)
    · exact List.mem_cons.mpr (Or.inr (ih later))

inductive TracerControl where
  | detached
  | exclusive (owner child : ProcessIdentity) (issued : List Nat) (options : UInt64)
  | foreign

-- §FS-entry.provenance: Protected control also preserves active filter enforcement.
def TracerControl.nonSubstituting : TracerControl → Prop
  | .detached => True
  | .exclusive _ _ issued options =>
      (∀ request ∈ issued, NonSubstitutingRequest request) ∧ TracerOptionsAllowed options.toNat
  | .foreign => False

end LeanCage.Entry
