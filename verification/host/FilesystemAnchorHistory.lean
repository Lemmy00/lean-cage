import FilesystemAnchorOperations
import FilesystemReferenceLifetime

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

private theorem launched_shared {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {before after : Population} {actor : ActorId} {references : UInt64 → Option Handle}
    {closeExec : UInt64 → Bool} {workingDirectory : ObjectId}
    (actual : ActorStep runtime (.launch actor references closeExec workingDirectory) before after) :
    after.shared = before.shared := by
  cases actual
  rfl

def AnchorActionOperands {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {initial : World} (anchor : TemporaryAnchor initial) (tick : ActorTick runtime) : Prop :=
  ∀ actor engine request observed,
    tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)) →
    tick.before.actors actor = some engine → AnchorOperandSafe anchor (tick.before.project engine) request

def AnchorSourceOperands {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat} {initial : World}
    (anchor : TemporaryAnchor initial) {before after : Processes} {callers next : NativeProcesses}
    {tick : ActorTick runtime} :
    NativeExternalStep process child native hostUid before callers tick after next → Prop
  | .application _ _ _ _ => AnchorActionOperands anchor tick
  | .child _ call => ChildAnchorOperandSafe anchor call.beforeReferences tick.before.shared call.operation
  | .launch _ _ | .ordinary _ _ _ _ | .native _ _ _ _ | .retiring _ _ => True

private theorem application_anchor_binding {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {child : ChildPrimitive kernel} {semantics : NameSemanticsView} {initial : World}
    {anchor : TemporaryAnchor initial} (laws : AnchorOperationContract runtime child semantics anchor)
    {tick : ActorTick runtime} (notForeign : ∀ caller, tick.action ≠ .foreign caller)
    (notLaunch : ∀ actor references closeExec workingDirectory,
      tick.action ≠ .launch actor references closeExec workingDirectory)
    (arguments : AnchorActionOperands anchor tick) (state : SystemAnchorState anchor semantics tick.before.shared) :
    anchor.At tick.after.shared := by
  rcases tick with ⟨action, before, after, actual⟩
  cases actual with
  | launch => exact False.elim (notLaunch _ _ _ _ rfl)
  | @returned β population actor engine effect next reply world present alive head operation =>
    cases effect with
    | filesystem request =>
      exact laws.filesystem _ _ _ _ operation state.bound state.names
        (arguments actor engine request (some reply) (by simp [ActorAction.eventFor, Program.filesystemPrefixEvent]) present)
    | spawn | read | wait | terminate | tryWait | descriptor => exact laws.sdk _ _ _ _ _ operation state.bound
  | @lost β population actor engine effect next world present alive head operation =>
    cases effect with
    | filesystem request =>
      exact laws.filesystem _ _ _ _ operation state.bound state.names
        (arguments actor engine request none (by simp [ActorAction.eventFor, Program.filesystemPrefixEvent]) present)
    | spawn | read | wait | terminate | tryWait | descriptor => exact laws.sdk _ _ _ _ _ operation state.bound
  | foreign => exact False.elim (notForeign _ rfl)
  | retire present operation => exact laws.retirement (.retire present operation) rfl state.bound
  | nativeRetire operation => exact laws.retirement (.nativeRetire operation) rfl state.bound

private theorem anchor_source_bound {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat} {semantics : NameSemanticsView} {initial : World}
    {anchor : TemporaryAnchor initial} (laws : AnchorOperationContract runtime child semantics anchor)
    {all : List (ActorTick runtime)} (profile : NativeAnchorProfile native anchor semantics all)
    {position : Nat} {tick : ActorTick runtime} (selected : all[position]? = some tick)
    {before after : Processes} {callers next : NativeProcesses}
    (source : NativeExternalStep process child native hostUid before callers tick after next)
    (arguments : AnchorSourceOperands anchor source) (state : SystemAnchorState anchor semantics tick.before.shared) :
    anchor.At tick.after.shared := by
  cases source with
  | application recorded notForeign notLaunch => exact application_anchor_binding laws notForeign notLaunch arguments state
  | launch recorded handoff =>
    have same := launched_shared (handoff.action ▸ tick.operation)
    rw [same]
    exact state.bound
  | ordinary caller recorded action allowed => exact ordinary_anchor_preserved laws (action ▸ tick.operation) allowed state
  | child recorded call => exact laws.child call state.bound state.names arguments
  | native recorded call => exact profile.binding position tick selected callers next call state.bound
  | retiring recorded exit =>
    exact laws.retirement (exit.action ▸ tick.operation) rfl state.bound

private theorem anchor_source_authority {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat} {semantics : NameSemanticsView} {initial : World}
    {anchor : TemporaryAnchor initial} (laws : GlobalAuthorityContract runtime child)
    (nativeLaws : NativeMetadataContract native)
    {all : List (ActorTick runtime)} (profile : NativeAnchorProfile native anchor semantics all)
    {position : Nat} {tick : ActorTick runtime} (selected : all[position]? = some tick)
    {before after : Processes} {callers next : NativeProcesses}
    (source : NativeExternalStep process child native hostUid before callers tick after next)
    (safe : NativeAuthoritySafe source) (state : SystemAnchorState anchor semantics tick.before.shared)
    (held : GloballyHeld tick.after anchor.root) :
    ∃ later, tick.after.shared.information anchor.root = some later ∧ SameAuthority state.information later := by
  cases source with
  | application recorded notForeign notLaunch =>
    exact external_step_authority (hostUid := hostUid) laws (.application recorded notForeign) safe state.known
      (.inr state.owner) held
  | launch recorded handoff =>
    have notForeign : ∀ caller, tick.action ≠ .foreign caller := by
      intro caller impossible
      rw [handoff.action] at impossible
      cases impossible
    have safe : AuthoritySafeAction tick.action := by simp only [handoff.action, AuthoritySafeAction]
    exact external_step_authority (hostUid := hostUid) laws (.application recorded notForeign) safe state.known
      (.inr state.owner) held
  | ordinary caller recorded action allowed =>
    exact external_step_authority (hostUid := hostUid) laws (.ordinary caller recorded action allowed) True.intro
      state.known (.inr state.owner) held
  | child recorded call =>
    exact external_step_authority (hostUid := hostUid) laws (.child recorded call) safe state.known (.inr state.owner) held
  | retiring recorded exit => exact laws.retirement _ _ (exit.action ▸ tick.operation) rfl held state.known
  | native recorded call =>
    obtain ⟨later, known, same | target⟩ := nativeLaws.existing call anchor.root state.information held state.known
    · exact ⟨later, known, same⟩
    · exact ⟨later, known, profile.authority position tick selected callers next call state.information later
        state state.known known target⟩

private theorem anchor_source_lookup {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat} {semantics : NameSemanticsView} {initial : World}
    {anchor : TemporaryAnchor initial} (laws : LookupMutationContract (runtime := runtime) child native)
    {all : List (ActorTick runtime)} (profile : NativeAnchorProfile native anchor semantics all)
    {position : Nat} {tick : ActorTick runtime} (selected : all[position]? = some tick)
    {before after : Processes} {callers next : NativeProcesses}
    (source : NativeExternalStep process child native hostUid before callers tick after next)
    (safe : NativeAuthoritySafe source) (state : SystemAnchorState anchor semantics tick.before.shared)
    (held : GloballyHeld tick.after anchor.root) : LookupBitsEqual tick.before.shared tick.after.shared anchor.root := by
  cases source with
  | application recorded notForeign notLaunch =>
    rcases tick with ⟨action, before, after, actual⟩
    cases action with
    | launch actor references closeExec cwd => exact False.elim (notLaunch _ _ _ _ rfl)
    | returned actor effect reply =>
      cases effect with
      | filesystem request => exact laws.filesystem _ actual rfl safe state.rootLive held
      | spawn | read | wait | terminate | tryWait | descriptor => exact laws.sdk _ actual rfl state.rootLive held
    | lost actor effect =>
      cases effect with
      | filesystem request => exact laws.filesystem _ actual rfl safe state.rootLive held
      | spawn | read | wait | terminate | tryWait | descriptor => exact laws.sdk _ actual rfl state.rootLive held
    | foreign caller => exact False.elim (notForeign caller rfl)
    | retire actor observation | nativeRetire actor observation _ _ =>
      exact laws.retirement _ actual rfl state.rootLive held
  | launch recorded handoff =>
    have same := launched_shared (handoff.action ▸ tick.operation)
    change tick.after.shared.inodeFlags anchor.root &&& _ = tick.before.shared.inodeFlags anchor.root &&& _
    rw [same]
  | ordinary caller recorded action allowed =>
    rcases laws.ordinary anchor.root state.information (action ▸ tick.operation) state.rootLive held state.known with
      same | permission
    · exact same
    · rcases permission with owner | bypass
      · exact False.elim (allowed.2.1 (owner.trans state.owner))
      · rw [allowed.2.2.2] at bypass
        cases bypass
  | child recorded call => exact laws.child call anchor.root safe state.rootLive held
  | retiring recorded exit => exact laws.retirement _ (exit.action ▸ tick.operation) rfl state.rootLive held
  | native recorded call =>
    rcases laws.native call anchor.root state.rootLive held with same | target
    · exact same
    · exact profile.lookup position tick selected callers next call state target

-- §FS-host-boundary.ownership: This fold step retains only the initialized system anchor.
-- The application side supplies actual destructive-call operands, never a child-path binding.
theorem system_anchor_step {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat} {semantics : NameSemanticsView} {initial : World}
    {anchor : TemporaryAnchor initial} (lifetimes : LifetimeContract runtime)
    (operations : AnchorOperationContract runtime child semantics anchor)
    (metadata : GlobalAuthorityContract runtime child) (nativeMetadata : NativeMetadataContract native)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {all : List (ActorTick runtime)} (profile : NativeAnchorProfile native anchor semantics all)
    {position : Nat} {tick : ActorTick runtime} (selected : all[position]? = some tick)
    {before after : Processes} {callers next : NativeProcesses}
    (source : NativeExternalStep process child native hostUid before callers tick after next)
    (arguments : AnchorSourceOperands anchor source) (safe : NativeAuthoritySafe source)
    (state : SystemAnchorState anchor semantics tick.before.shared) :
    Nonempty (SystemAnchorState anchor semantics tick.after.shared) := by
  have binding := anchor_source_bound operations profile selected source arguments state
  have held : GloballyHeld tick.after anchor.root := .inr (.inr ⟨"tmp".toUTF8, anchor.entry, binding⟩)
  obtain ⟨later, known, authority⟩ := anchor_source_authority metadata nativeMetadata profile selected source safe state held
  have names := anchor_source_lookup lookup profile selected source safe state held
  exact ⟨⟨binding, actor_step_allocated lifetimes tick.operation _ state.rootLive, later, known,
    authority.1.trans state.owner, (same_authority_mask authority 18 (by decide)).trans state.permissions,
    byte_exact_after_lookup_bits state.names names⟩⟩

-- §FS-host-boundary.ownership: These are checked snapshots at actual global positions. The
-- application constructs this history using the single-operation step above.
inductive SystemAnchorJournal {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram)
    {initial : World} (anchor : TemporaryAnchor initial) (semantics : NameSemanticsView) :
    Population → List (ActorTick runtime) → Population → Prop where
  | nil (population : Population) (state : Nonempty (SystemAnchorState anchor semantics population.shared)) :
      SystemAnchorJournal runtime anchor semantics population [] population
  | cons {tick : ActorTick runtime} {ticks : List (ActorTick runtime)} {after : Population}
      (state : Nonempty (SystemAnchorState anchor semantics tick.before.shared))
      (tail : SystemAnchorJournal runtime anchor semantics tick.after ticks after) :
      SystemAnchorJournal runtime anchor semantics tick.before (tick :: ticks) after

theorem system_anchor_selected {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {initial : World} {anchor : TemporaryAnchor initial} {semantics : NameSemanticsView}
    {before after : Population} {ticks : List (ActorTick runtime)}
    (history : SystemAnchorJournal runtime anchor semantics before ticks after)
    {position : Nat} {tick : ActorTick runtime} (selected : ticks[position]? = some tick) :
    Nonempty (SystemAnchorState anchor semantics tick.before.shared) := by
  induction history generalizing position with
  | nil => cases selected
  | cons state tail ih =>
    cases position with
    | zero => cases selected; exact state
    | succ position => exact ih selected

-- §FS-host-boundary.ownership: Raw open provenance selects its own snapshot from the same
-- global history. No independent safe open-world is chosen.
theorem system_anchor_source_snapshot {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {initial : World} {anchor : TemporaryAnchor initial} {semantics : NameSemanticsView}
    {before after : Population} {ticks : List (ActorTick runtime)}
    (history : SystemAnchorJournal runtime anchor semantics before ticks after)
    {actor ordinal : Nat} {β : Type} {effect : Effect β} {reply : β} {first last : World}
    (sampled : SourceReturnAt runtime ticks actor ordinal β effect reply first last) : anchor.At first := by
  obtain ⟨position, tick, engine, finalEngine, selected, action, present, finalPresent, count, same, finalSame⟩ := sampled
  obtain ⟨state⟩ := system_anchor_selected history selected
  simpa only [same, TemporaryAnchor.At, Population.project] using state.bound

-- §FS-host-boundary.ownership: Its remaining source input is only actual destructive-call
-- operands at each position; all anchor preservation and metadata are derived per operation.
theorem system_anchor_journal {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat} {semantics : NameSemanticsView} {initial : World}
    {anchor : TemporaryAnchor initial} (lifetimes : LifetimeContract runtime)
    (operations : AnchorOperationContract runtime child semantics anchor)
    (metadata : GlobalAuthorityContract runtime child) (nativeMetadata : NativeMetadataContract native)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {all : List (ActorTick runtime)} (profile : NativeAnchorProfile native anchor semantics all)
    (arguments : ∀ (position : Nat) (tick : ActorTick runtime), all[position]? = some tick →
      ∀ before after callers next (source : NativeExternalStep process child native hostUid before callers tick after next),
        AnchorSourceOperands anchor source)
    {before after : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime before ticks after) (included : ∀ tick ∈ ticks, tick ∈ all)
    {prior last : Processes} {callers next : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid prior callers ticks last next)
    (safe : NativeAuthorityJournal recording) (state : SystemAnchorState anchor semantics before.shared) :
    SystemAnchorJournal runtime anchor semantics before ticks after := by
  induction journal generalizing prior callers with
  | nil => exact .nil _ ⟨state⟩
  | @cons tick ticks after tail ih =>
    cases recording with
    | cons current rest =>
      obtain ⟨position, bound, same⟩ := List.mem_iff_getElem.mp (included tick (by simp))
      have selected : all[position]? = some tick := List.getElem?_eq_some_iff.mpr ⟨bound, same⟩
      obtain ⟨middle⟩ := system_anchor_step lifetimes operations metadata nativeMetadata lookup profile
        selected current (arguments position tick selected _ _ _ _ current) safe.1 state
      exact .cons ⟨state⟩ (ih (by intro event member; exact included event (by simp [member])) rest safe.2 middle)

end LeanCage.Host.Kernel
