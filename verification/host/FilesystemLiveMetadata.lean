import FilesystemObjectLifetime

namespace LeanCage.Host.Kernel
open Filesystem

-- §AR-host-boundary.primitives: These per-operation laws apply only to actually still-live inodes.
-- File data, size, links, timestamps, retirement and foreign authorized changes remain broad.
structure LiveMetadataContract {kernel : Contract} {sourceProgram : Program UInt32}
    (runtime : ActorRuntime kernel sourceProgram)
    (primitive : ChildPrimitive kernel) : Prop where
  filesystem : ∀ {before after : Population} {action : ActorAction} object information,
    ActorStep runtime action before after → actionFamily action = .filesystem → AuthoritySafeAction action →
    ObjectAlive after.shared object → before.shared.information object = some information →
    ∃ later, after.shared.information object = some later ∧ SameAuthority information later
  sdk : ∀ {before after : Population} {action : ActorAction} object information,
    ActorStep runtime action before after → actionFamily action = .runtime →
    ObjectAlive after.shared object → before.shared.information object = some information →
    ∃ later, after.shared.information object = some later ∧ SameAuthority information later
  retirement : ∀ {before after : Population} {action : ActorAction} object information,
    ActorStep runtime action before after → actionFamily action = .retirement →
    ObjectAlive after.shared object → before.shared.information object = some information →
    ∃ later, after.shared.information object = some later ∧ SameAuthority information later
  child : ∀ {before after : Processes} {tick : ActorTick runtime}
    (call : ChildCallAt primitive tick before after) object information,
    ChildAuthoritySafe call.operation → ObjectAlive tick.after.shared object → tick.before.shared.information object = some information →
    ∃ later, tick.after.shared.information object = some later ∧ SameAuthority information later
  ordinary : ∀ {before after : Population} {caller : Credentials} object information,
    ActorStep runtime (.foreign caller) before after → ObjectAlive after.shared object →
    before.shared.information object = some information →
    (∃ later, after.shared.information object = some later ∧ SameAuthority information later) ∨
      CanChangeAuthority caller information


private theorem live_launch_shared {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram}
    {before after : Population} {actor : ActorId} {references : UInt64 → Option Handle}
    {closeExec : UInt64 → Bool} {workingDirectory : ObjectId}
    (actual : ActorStep runtime (.launch actor references closeExec workingDirectory) before after) :
    after.shared = before.shared := by
  cases actual
  rfl

-- §FS-host-boundary.ownership: A peer's held directory needs no duplicate FD in the acting table.
theorem external_step_live_authority_for {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram}
    {contract : ProcessContract runtime} {primitive : ChildPrimitive kernel} {hostUid : Nat}
    (laws : LiveMetadataContract runtime primitive) {before after : Processes} {tick : ActorTick runtime}
    (source : ExternalStep contract primitive hostUid before tick after)
    (safe : ExternalAuthoritySafe source) {object : ObjectId} {information : Stat}
    (known : tick.before.shared.information object = some information)
    (trustedOwner : information.uid = hostUid ∨ information.uid = 0)
    (alive : ObjectAlive tick.after.shared object) :
    ∃ later, tick.after.shared.information object = some later ∧ SameAuthority information later := by
  cases source with
  | application recorded notForeign =>
    rcases tick with ⟨action, before, after, actual⟩
    cases action with
    | launch actor references closeExec cwd =>
      exact ⟨information, by rw [live_launch_shared actual]; exact known, ⟨rfl, rfl, rfl⟩⟩
    | returned actor effect reply =>
      cases effect with
      | filesystem request => exact laws.filesystem _ _ actual rfl safe alive known
      | spawn arguments => exact laws.sdk _ _ actual rfl alive known
      | read stream amount => exact laws.sdk _ _ actual rfl alive known
      | wait child => exact laws.sdk _ _ actual rfl alive known
      | terminate child => exact laws.sdk _ _ actual rfl alive known
      | tryWait child => exact laws.sdk _ _ actual rfl alive known
      | descriptor stream => exact laws.sdk _ _ actual rfl alive known
    | lost actor effect =>
      cases effect with
      | filesystem request => exact laws.filesystem _ _ actual rfl safe alive known
      | spawn arguments => exact laws.sdk _ _ actual rfl alive known
      | read stream amount => exact laws.sdk _ _ actual rfl alive known
      | wait child => exact laws.sdk _ _ actual rfl alive known
      | terminate child => exact laws.sdk _ _ actual rfl alive known
      | tryWait child => exact laws.sdk _ _ actual rfl alive known
      | descriptor stream => exact laws.sdk _ _ actual rfl alive known
    | foreign caller => exact False.elim (notForeign caller rfl)
    | retire actor observation | nativeRetire actor observation _ _ =>
      exact laws.retirement _ _ actual rfl alive known
  | ordinary caller recorded action allowed =>
    have actual : ActorStep runtime (.foreign caller) tick.before tick.after := action ▸ tick.operation
    rcases laws.ordinary object information actual alive known with unchanged | canChange
    · exact unchanged
    · rcases canChange with sameOwner | bypass
      · rcases trustedOwner with owner | rootOwner
        · exact False.elim (allowed.1 (sameOwner.trans owner))
        · exact False.elim (allowed.2.1 (sameOwner.trans rootOwner))
      · rw [allowed.2.2.2] at bypass
        cases bypass
  | child recorded call => exact laws.child call _ _ safe alive known
  | native recorded native impossible call => cases impossible

-- §AR-host-boundary.interfaces: Keep the original logical application consumer unchanged.
theorem external_step_live_authority {kernel : Contract} {runtime : ActorRuntime kernel}
    {contract : ProcessContract runtime} {primitive : ChildPrimitive kernel} {hostUid : Nat}
    (laws : LiveMetadataContract runtime primitive) {before after : Processes} {tick : ActorTick runtime}
    (source : ExternalStep contract primitive hostUid before tick after)
    (safe : ExternalAuthoritySafe source) {object : ObjectId} {information : Stat}
    (known : tick.before.shared.information object = some information)
    (trustedOwner : information.uid = hostUid ∨ information.uid = 0)
    (alive : ObjectAlive tick.after.shared object) :
    ∃ later, tick.after.shared.information object = some later ∧ SameAuthority information later :=
  external_step_live_authority_for laws source safe known trustedOwner alive


end LeanCage.Host.Kernel
