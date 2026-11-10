import FilesystemNativeMetadata
import FilesystemPrimitiveRoles

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

def NativeAuthoritySafe {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat}
    {before after : Processes} {callers next : NativeProcesses} {tick : ActorTick runtime} :
    NativeExternalStep process child native hostUid before callers tick after next → Prop
  | .application _ _ _ _ => AuthoritySafeAction tick.action
  | .launch _ _ => True
  | .ordinary _ _ _ _ => True
  | .child _ call => ChildAuthoritySafe call.operation
  | .native _ _ _ _ | .retiring _ _ => True

def NativeAuthorityJournal {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat}
    {before after : Processes} {callers next : NativeProcesses} {ticks : List (ActorTick runtime)} :
    NativeExternalJournal process child native hostUid before callers ticks after next → Prop
  | .nil _ _ => True
  | .cons current rest => NativeAuthoritySafe current ∧ NativeAuthorityJournal rest

theorem native_step_parent_authority {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat}
    (laws : GlobalAuthorityContract runtime child) (nativeLaws : NativeMetadataContract native)
    {all : List (ActorTick runtime)} (profile : NativeAuthorityProfile native all hostUid)
    {position : Nat} {tick : ActorTick runtime} (selected : all[position]? = some tick)
    {before after : Processes} {callers next : NativeProcesses}
    (source : NativeExternalStep process child native hostUid before callers tick after next)
    (safe : NativeAuthoritySafe source) {object : ObjectId} {information : Stat}
    (lease : ActiveParentLease runtime all tick.before hostUid object)
    (known : tick.before.shared.information object = some information)
    (owner : information.uid = hostUid ∨ information.uid = 0) (held : GloballyHeld tick.after object) :
    ∃ later, tick.after.shared.information object = some later ∧ SameAuthority information later := by
  cases source with
  | application recorded notForeign notLaunch =>
    exact external_step_authority (hostUid := hostUid) laws (.application recorded notForeign) safe known owner held
  | launch recorded handoff =>
    have notForeign : ∀ caller, tick.action ≠ .foreign caller := by
      intro caller impossible
      rw [handoff.action] at impossible
      cases impossible
    have safe : AuthoritySafeAction tick.action := by simp only [handoff.action, AuthoritySafeAction]
    exact external_step_authority (hostUid := hostUid) laws (.application recorded notForeign) safe known owner held
  | ordinary caller recorded action allowed =>
    exact external_step_authority (hostUid := hostUid) laws (.ordinary caller recorded action allowed) True.intro known owner held
  | child recorded call => exact external_step_authority (hostUid := hostUid) laws (.child recorded call) safe known owner held
  | native recorded call retirementFrame => exact native_active_parent_authority nativeLaws profile selected call lease held known
  | retiring recorded exit =>
    have actual : ActorStep runtime (.nativeRetire exit.token exit.observation exit.beforeResources exit.afterResources)
        tick.before tick.after := exit.action ▸ tick.operation
    exact laws.retirement _ _ actual rfl held known

-- §FS-host-boundary.ownership: Actual raw source calls supply the setter-name restriction.
theorem selected_primitive_action_authority {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
      exact primitive_authority_safe (observed := some reply)
        (selected_source_prefix_for (event := .returned (.filesystem request) reply) journal selected
          (by simp [ActorAction.eventFor]) present)
    | spawn | read | wait | terminate | tryWait | descriptor => trivial
  | @lost β population actor engine effect next world present alive head operation =>
    cases effect with
    | filesystem request =>
      exact primitive_authority_safe (observed := none)
        (selected_source_prefix_for (event := .lost (.filesystem request)) journal selected
          (by simp [ActorAction.eventFor]) present)
    | spawn | read | wait | terminate | tryWait | descriptor => trivial
  | foreign | retire | nativeRetire => trivial

-- §AR-host-boundary.primitives: This producer names only an actual owned child's setter name.
-- Its caller is the maintained controller source or the explicit fixed-argument VMM contract.
def PrimitiveChildAuthorityProducer {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (child : ChildPrimitive kernel) (ticks : List (ActorTick runtime)) : Prop :=
  ∀ (position : Nat) (tick : ActorTick runtime), ticks[position]? = some tick → ∀ before after
    (call : ChildCallAt child tick before after), ChildAuthoritySafe call.operation

theorem actual_native_authority_journal {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat}
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    (backend : PrimitiveChildAuthorityProducer child all)
    {before after : Processes} {callers next : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid before callers all after next) :
    NativeAuthorityJournal recording := by
  have follow : ∀ {prior last : Processes} {nativeBefore nativeAfter : NativeProcesses}
      {ticks : List (ActorTick runtime)}
      (remaining : NativeExternalJournal process child native hostUid prior nativeBefore ticks last nativeAfter)
      (leading : List (ActorTick runtime)), all = leading ++ ticks → NativeAuthorityJournal remaining := by
    intro prior last nativeBefore nativeAfter ticks remaining
    induction remaining with
    | nil => intro leading shape; trivial
    | @cons before middle after callers next final tick ticks current tail ih =>
      intro leading shape
      have selected : all[leading.length]? = some tick := by
        rw [shape, List.getElem?_append_right (Nat.le_refl _)]
        simp
      refine ⟨?_, ih (leading ++ [tick]) (by simpa only [List.append_assoc, List.singleton_append] using shape)⟩
      cases current with
      | application recorded notForeign notLaunch => exact selected_primitive_action_authority journal selected
      | launch | ordinary | native | retiring => trivial
      | child recorded call => exact backend leading.length tick selected before middle call
  exact follow recording [] (by simp)

theorem native_safe_split {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat}
    {before after : Processes} {callers next : NativeProcesses} (first last : List (ActorTick runtime))
    (recording : NativeExternalJournal process child native hostUid before callers (first ++ last) after next)
    (safe : NativeAuthorityJournal recording) :
    ∃ middle middleNative,
      ∃ initial : NativeExternalJournal process child native hostUid before callers first middle middleNative,
      ∃ final : NativeExternalJournal process child native hostUid middle middleNative last after next,
        NativeAuthorityJournal initial ∧ NativeAuthorityJournal final := by
  induction first generalizing before callers with
  | nil => exact ⟨before, callers, .nil _ _, recording, True.intro, safe⟩
  | cons tick ticks ih =>
    cases recording with
    | cons current rest =>
      obtain ⟨middle, middleNative, initial, final, firstSafe, lastSafe⟩ := ih rest safe.2
      exact ⟨middle, middleNative, .cons current initial, final, ⟨safe.1, firstSafe⟩, lastSafe⟩

-- §FS-host-boundary.ownership: Current parent authority follows each same-journal syscall,
-- including native callbacks, rather than an assumed stable parent or callback interval.
theorem native_parent_authority_interval {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat}
    (laws : GlobalAuthorityContract runtime child) (nativeLaws : NativeMetadataContract native)
    {all : List (ActorTick runtime)} (profile : NativeAuthorityProfile native all hostUid)
    {before after : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime before ticks after)
    (included : ∀ tick ∈ ticks, tick ∈ all)
    {prior last : Processes} {callers next : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid prior callers ticks last next)
    (safe : NativeAuthorityJournal recording) {object : ObjectId} {information : Stat}
    (known : before.shared.information object = some information)
    (owner : information.uid = hostUid ∨ information.uid = 0)
    (held : ∀ tick ∈ ticks, GloballyHeld tick.after object)
    (leases : ∀ tick ∈ ticks, Nonempty (ActiveParentLease runtime all tick.before hostUid object)) :
    ∃ later, after.shared.information object = some later ∧ SameAuthority information later := by
  induction journal generalizing prior callers information with
  | nil => exact ⟨information, known, ⟨rfl, rfl, rfl⟩⟩
  | @cons tick ticks after tail ih =>
    cases recording with
    | cons current rest =>
      obtain ⟨position, bound, actual⟩ := List.mem_iff_getElem.mp (included tick (by simp))
      have selected : all[position]? = some tick := List.getElem?_eq_some_iff.mpr ⟨bound, actual⟩
      obtain ⟨lease⟩ := leases tick (by simp)
      obtain ⟨middle, actualMiddle, first⟩ := native_step_parent_authority laws nativeLaws profile selected
        current safe.1 lease known owner (held tick (by simp))
      have middleOwner : middle.uid = hostUid ∨ middle.uid = 0 := by rw [first.1]; exact owner
      obtain ⟨later, actualLater, following⟩ := ih
        (by intro other member; exact included other (by simp [member])) rest safe.2 actualMiddle middleOwner
        (by intro other member; exact held other (by simp [member]))
        (by intro other member; exact leases other (by simp [member]))
      exact ⟨later, actualLater, same_authority_trans first following⟩

end LeanCage.Host.Kernel
