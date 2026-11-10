import GatewayChannelAliasJournal

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

-- §FS-host-boundary.ownership: The actual native row keeps the exact C
-- command. Source-proved GETFL/SETFL cannot alter aliases; F_DUPFD_CLOEXEC
-- gives a close-on-exec alias rather than silently assuming all flags safe.
theorem native_source_fcntl_authority {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {native : NativePrimitive kernel} {tick : ActorTick runtime} {before after : NativeProcesses}
    (call : NativeCallAt native tick before after) (code : NativeCode.CallRow)
    (actual : NativeCode.Interprets code call) (object : ObjectId) (fd argument : Nat)
    (source : code.operation = .fcntl fd 3 argument ∨ code.operation = .fcntl fd 4 argument ∨
      code.operation = .fcntl fd 1030 argument) : Nonempty (NativeFlagAuthority call object) := by
  have encoded := NativeCode.operation_exact actual.operation
  cases operation : call.operation <;> simp only [operation, NativeCode.encodeOperation] at encoded
  all_goals rcases source with source | source | source
  all_goals rw [source] at encoded
  all_goals try contradiction
  all_goals simp only [NativeCode.Operation.fcntl.injEq] at encoded
  all_goals rcases encoded with ⟨descriptor, command, parameter⟩
  all_goals first
    | (have same : _ = (3 : UInt64) := UInt64.toNat.inj command
       subst_vars
       exact ⟨.unchanged (by rw [operation]; exact status_fcntl_no_alias_write _ _ _ (.inl rfl))⟩)
    | (have same : _ = (4 : UInt64) := UInt64.toNat.inj command
       subst_vars
       exact ⟨.unchanged (by rw [operation]; exact status_fcntl_no_alias_write _ _ _ (.inr rfl))⟩)
    | (have same : _ = (1030 : UInt64) := UInt64.toNat.inj command
       subst_vars
       exact ⟨.cloexec _ _ operation⟩)

end LeanCage.Host.PrivateStreams
