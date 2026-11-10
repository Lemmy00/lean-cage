import FilesystemChildEffects
import FilesystemRootAuthority
import FilesystemAuthoritySources

namespace LeanCage.Host.Kernel
open Filesystem

-- §AR-host-boundary.primitives: Another live actor's raw lease also retains the actual inode.
def GloballyHeld (population : Population) (object : ObjectId) : Prop :=
  (∃ actor engine fd handle, population.actors actor = some engine ∧ engine.references fd = some handle ∧
    handle.object = object) ∨
  (∃ parent name, population.shared.entries parent name = some object) ∨
  ∃ name child, population.shared.entries object name = some child

inductive ActionFamily where
  | launch
  | filesystem
  | runtime
  | foreign
  | retirement
  deriving DecidableEq

def actionFamily : ActorAction → ActionFamily
  | .launch _ _ _ _ => .launch
  | .returned _ (.filesystem _) _ => .filesystem
  | .lost _ (.filesystem _) => .filesystem
  | .returned _ _ _ | .lost _ _ => .runtime
  | .foreign _ => .foreign
  | .retire _ _ | .nativeRetire _ _ _ _ => .retirement

def AuthoritySafeAction : ActorAction → Prop
  | .returned _ (.filesystem request) _ | .lost _ (.filesystem request) => AuthoritySafeRequest request
  | _ => True

def ChildAuthoritySafe : ChildOperation → Prop
  | .adapted request => AuthoritySafeRequest request
  | .unixSocket _ | .bindUnix _ _ => True

def ExternalAuthoritySafe {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram}
    {contract : ProcessContract runtime} {primitive : ChildPrimitive kernel} {hostUid : Nat}
    {before after : Processes} {tick : ActorTick runtime} :
    ExternalStep contract primitive hostUid before tick after → Prop
  | .application _ _ => AuthoritySafeAction tick.action
  | .ordinary _ _ _ _ => True
  | .child _ call => ChildAuthoritySafe call.operation
  | .native _ _ impossible _ => nomatch impossible

-- §AR-host-boundary.primitives: One-operation authority laws use globally live references.
-- Timestamps, size, links and contents remain mutable; backend child operations stay separate.
structure GlobalAuthorityContract {kernel : Contract} {sourceProgram : Program UInt32}
    (runtime : ActorRuntime kernel sourceProgram)
    (primitive : ChildPrimitive kernel) : Prop where
  filesystem : ∀ {before after : Population} {action : ActorAction} object information,
    ActorStep runtime action before after → actionFamily action = .filesystem → AuthoritySafeAction action →
    GloballyHeld after object → before.shared.information object = some information →
    ∃ later, after.shared.information object = some later ∧ SameAuthority information later
  sdk : ∀ {before after : Population} {action : ActorAction} object information,
    ActorStep runtime action before after → actionFamily action = .runtime →
    GloballyHeld after object → before.shared.information object = some information →
    ∃ later, after.shared.information object = some later ∧ SameAuthority information later
  retirement : ∀ {before after : Population} {action : ActorAction} object information,
    ActorStep runtime action before after → actionFamily action = .retirement →
    GloballyHeld after object → before.shared.information object = some information →
    ∃ later, after.shared.information object = some later ∧ SameAuthority information later
  child : ∀ {before after : Processes} {tick : ActorTick runtime}
    (call : ChildCallAt primitive tick before after) object information,
    ChildAuthoritySafe call.operation → GloballyHeld tick.after object → tick.before.shared.information object = some information →
    ∃ later, tick.after.shared.information object = some later ∧ SameAuthority information later
  ordinary : ∀ {before after : Population} {caller : Credentials} object information,
    ActorStep runtime (.foreign caller) before after → GloballyHeld after object →
    before.shared.information object = some information →
    (∃ later, after.shared.information object = some later ∧ SameAuthority information later) ∨
      CanChangeAuthority caller information

private theorem launch_shared {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram}
    {before after : Population} {actor : ActorId} {references : UInt64 → Option Handle}
    {closeExec : UInt64 → Bool} {workingDirectory : ObjectId}
    (actual : ActorStep runtime (.launch actor references closeExec workingDirectory) before after) :
    after.shared = before.shared := by
  cases actual
  rfl

-- §FS-host-boundary.ownership: A peer's held directory needs no duplicate FD in the acting table.
theorem external_step_authority {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram}
    {contract : ProcessContract runtime} {primitive : ChildPrimitive kernel} {hostUid : Nat}
    (laws : GlobalAuthorityContract runtime primitive) {before after : Processes} {tick : ActorTick runtime}
    (source : ExternalStep contract primitive hostUid before tick after)
    (safe : ExternalAuthoritySafe source) {object : ObjectId} {information : Stat}
    (known : tick.before.shared.information object = some information)
    (trustedOwner : information.uid = hostUid ∨ information.uid = 0)
    (held : GloballyHeld tick.after object) :
    ∃ later, tick.after.shared.information object = some later ∧ SameAuthority information later := by
  cases source with
  | application recorded notForeign =>
    rcases tick with ⟨action, before, after, actual⟩
    cases action with
    | launch actor references closeExec cwd =>
      exact ⟨information, by rw [launch_shared actual]; exact known, ⟨rfl, rfl, rfl⟩⟩
    | returned actor effect reply =>
      cases effect with
      | filesystem request => exact laws.filesystem _ _ actual rfl safe held known
      | spawn arguments => exact laws.sdk _ _ actual rfl held known
      | read stream amount => exact laws.sdk _ _ actual rfl held known
      | wait child => exact laws.sdk _ _ actual rfl held known
      | terminate child => exact laws.sdk _ _ actual rfl held known
      | tryWait child => exact laws.sdk _ _ actual rfl held known
      | descriptor stream => exact laws.sdk _ _ actual rfl held known
    | lost actor effect =>
      cases effect with
      | filesystem request => exact laws.filesystem _ _ actual rfl safe held known
      | spawn arguments => exact laws.sdk _ _ actual rfl held known
      | read stream amount => exact laws.sdk _ _ actual rfl held known
      | wait child => exact laws.sdk _ _ actual rfl held known
      | terminate child => exact laws.sdk _ _ actual rfl held known
      | tryWait child => exact laws.sdk _ _ actual rfl held known
      | descriptor stream => exact laws.sdk _ _ actual rfl held known
    | foreign caller => exact False.elim (notForeign caller rfl)
    | retire actor observation | nativeRetire actor observation _ _ =>
      exact laws.retirement _ _ actual rfl held known
  | ordinary caller recorded action allowed =>
    have actual : ActorStep runtime (.foreign caller) tick.before tick.after := action ▸ tick.operation
    rcases laws.ordinary object information actual held known with unchanged | canChange
    · exact unchanged
    · rcases canChange with sameOwner | bypass
      · rcases trustedOwner with owner | rootOwner
        · exact False.elim (allowed.1 (sameOwner.trans owner))
        · exact False.elim (allowed.2.1 (sameOwner.trans rootOwner))
      · rw [allowed.2.2.2] at bypass
        cases bypass
  | child recorded call => exact laws.child call _ _ safe held known
  | native recorded native impossible call => cases impossible

def ExternalAuthorityJournal {kernel : Contract} {runtime : ActorRuntime kernel}
    {contract : ProcessContract runtime} {primitive : ChildPrimitive kernel} {hostUid : Nat}
    {before after : Processes} {ticks : List (ActorTick runtime)} :
    ExternalJournal contract primitive hostUid before ticks after → Prop
  | .nil _ => True
  | .cons current rest => ExternalAuthoritySafe current ∧ ExternalAuthorityJournal rest

-- §FS-host-boundary.ownership: Global metadata retention follows each actual peer/child syscall.
theorem external_journal_authority {kernel : Contract} {runtime : ActorRuntime kernel}
    {contract : ProcessContract runtime} {primitive : ChildPrimitive kernel} {hostUid : Nat}
    (laws : GlobalAuthorityContract runtime primitive)
    {initial final : Processes} {before after : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime before ticks after)
    (recording : ExternalJournal contract primitive hostUid initial ticks final)
    (safe : ExternalAuthorityJournal recording) {object : ObjectId} {information : Stat} (known : before.shared.information object = some information)
    (trustedOwner : information.uid = hostUid ∨ information.uid = 0)
    (held : ∀ tick ∈ ticks, GloballyHeld tick.after object) :
    ∃ later, after.shared.information object = some later ∧ SameAuthority information later := by
  induction journal generalizing initial information with
  | nil => exact ⟨information, known, ⟨rfl, rfl, rfl⟩⟩
  | @cons tick ticks after tail ih =>
    cases recording with
    | cons source remaining =>
      obtain ⟨middle, actualMiddle, first⟩ := external_step_authority laws source safe.1 known trustedOwner (held tick (by simp))
      have middleOwner : middle.uid = hostUid ∨ middle.uid = 0 := by
        rw [first.1]
        exact trustedOwner
      obtain ⟨last, actualLast, rest⟩ := ih remaining safe.2 actualMiddle middleOwner
        (by intro other member; exact held other (by simp [member]))
      exact ⟨last, actualLast, same_authority_trans first rest⟩

-- §FS-host-boundary.ownership: Application setter restrictions come from the same source tick.
theorem selected_action_authority_safe {kernel : Contract} {runtime : ActorRuntime kernel}
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} (selected : ticks[position]? = some tick) :
    AuthoritySafeAction tick.action := by
  rcases tick with ⟨action, before, after, actual⟩
  cases actual with
  | launch => trivial
  | @returned β population actor engine effect next reply world present alive head operation =>
    cases effect with
    | filesystem request =>
      exact selected_authority_safe (observed := some reply) journal selected
        (by simp [ActorAction.eventFor, Program.filesystemPrefixEvent]) present
    | spawn | read | wait | terminate | tryWait | descriptor => trivial
  | @lost β population actor engine effect next world present alive head operation =>
    cases effect with
    | filesystem request =>
      exact selected_authority_safe (observed := none) journal selected
        (by simp [ActorAction.eventFor, Program.filesystemPrefixEvent]) present
    | spawn | read | wait | terminate | tryWait | descriptor => trivial
  | foreign | retire | nativeRetire => trivial

-- §AR-host-boundary.primitives: Backend safety is only this actual operation's attribute name.
-- Controller source and the fixed-argument VMM primitive profile supply this producer.
def BackendAuthorityProducer {kernel : Contract} {runtime : ActorRuntime kernel}
    (contract : ProcessContract runtime) (primitive : ChildPrimitive kernel) (ticks : List (ActorTick runtime)) : Prop :=
  ∀ position tick, ∀ source : OwnedChildCall contract primitive ticks position tick,
    ChildAuthoritySafe source.call.operation

private theorem process_append {kernel : Contract} {runtime : ActorRuntime kernel}
    {contract : ProcessContract runtime} {before middle after : Processes} {first last : List (ActorTick runtime)}
    (initial : ProcessJournal contract before first middle) (final : ProcessJournal contract middle last after) :
    ProcessJournal contract before (first ++ last) after := by
  induction initial with
  | nil => exact final
  | cons actual rest ih => exact .cons actual (ih final)

-- §FS-host-boundary.acceptance: The entire per-operation attribute profile has real producers.
theorem actual_external_authority_journal {kernel : Contract} {runtime : ActorRuntime kernel}
    {contract : ProcessContract runtime} {primitive : ChildPrimitive kernel} {hostUid : Nat}
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    (backend : BackendAuthorityProducer contract primitive all) {after : Processes}
    (recording : ExternalJournal contract primitive hostUid Processes.empty all after) :
    ExternalAuthorityJournal recording := by
  have follow : ∀ {before after : Processes} {ticks : List (ActorTick runtime)}
      (remaining : ExternalJournal contract primitive hostUid before ticks after)
      (leading : List (ActorTick runtime)),
      all = leading ++ ticks → ProcessJournal contract Processes.empty leading before →
      ExternalAuthorityJournal remaining := by
    intro before after ticks remaining
    induction remaining with
    | nil => intro leading shape prior; trivial
    | @cons before middle after tick ticks current tail ih =>
      intro leading shape prior
      have selected : all[leading.length]? = some tick := by
        rw [shape, List.getElem?_append_right (Nat.le_refl _)]
        simp
      have safe : ExternalAuthoritySafe current := by
        cases current with
        | application actual notForeign => exact selected_action_authority_safe journal selected
        | ordinary => trivial
        | child actual call =>
          obtain ⟨source⟩ := actual_backend_source journal leading ticks tick shape prior call.token call.active
          exact backend leading.length tick ⟨before, middle, call, source⟩
        | native actual native impossible call => cases impossible
      refine ⟨safe, ?_⟩
      apply ih (leading ++ [tick])
      · simpa only [List.append_assoc, List.singleton_append] using shape
      · exact process_append prior (.cons current.process (.nil _))
  exact follow recording [] (by simp) (.nil _)

end LeanCage.Host.Kernel
