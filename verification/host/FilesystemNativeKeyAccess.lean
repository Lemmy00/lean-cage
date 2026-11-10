import FilesystemNativeMarkerLifetime
import FilesystemNativeRetirement
import GatewayChannelHistory

namespace LeanCage.Host.Kernel
open PrivateStreams

variable {sourceProgram : Program UInt32}

def NativeKeysExcluded (processes : NativeProcesses) (keys : ObjectId → Prop) : Prop :=
  ∀ object, keys object → ¬ NativeHeld processes object

-- §DA-host-engine.hostcode: This is the actual resolved operand of ONE external
-- host-code operation. Profile 1 excludes bootstrap-private acquisition; public
-- data/name effects remain in this same row with their full tables and result.
def NativeKeyOperand {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} (namespaceLaws : NativeNamespaceContract native) (keys : ObjectId → Prop)
    {before after : Processes} {first last : NativeProcesses} {tick : ActorTick runtime} :
    NativeExternalStep process child native hostUid before first tick after last → Prop
  | .native _ call _ _ => ∀ object, keys object → ¬ NativeCallAccess namespaceLaws call object
  | _ => True

def NativeKeyOperands {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} (namespaceLaws : NativeNamespaceContract native) (keys : ObjectId → Prop)
    {before after : Processes} {first last : NativeProcesses} {ticks : List (ActorTick runtime)} :
    NativeExternalJournal process child native hostUid before first ticks after last → Prop
  | .nil _ _ => True
  | .cons current rest => NativeKeyOperand namespaceLaws keys current ∧ NativeKeyOperands namespaceLaws keys rest

theorem native_call_keys_excluded {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {native : NativePrimitive kernel} (namespaceLaws : NativeNamespaceContract native)
    {before after : NativeProcesses} {tick : ActorTick runtime} (call : NativeCallAt native tick before after)
    {keys : ObjectId → Prop} (operands : ∀ object, keys object → ¬ NativeCallAccess namespaceLaws call object)
    (initialized : ∀ object, keys object → tick.before.shared.allocated object = true)
    (prior : NativeKeysExcluded before keys) : NativeKeysExcluded after keys := by
  intro object key held
  rcases namespaceLaws.acquired call object held with old | fresh | used
  · exact prior object key old
  · have allocated := initialized object key
    rw [fresh] at allocated
    cases allocated
  · exact operands object key used

private theorem transfer_held_before {processes : NativeProcesses} {actor : ActorId} {execution : NativeExecution}
    {object : ObjectId} (held : NativeHeld (processes.transfer actor execution) object) : NativeHeld processes object := by
  rcases held with ⟨token, references, present, reference⟩ | retired
  · by_cases same : token = actor
    · simp only [NativeProcesses.transfer, same, ite_eq_left] at present
      cases present
    · exact .inl ⟨token, references, by
        simpa only [NativeProcesses.transfer, ite_eq_right same] using present, reference⟩
  · exact .inr retired

-- §FS-host-boundary.publication: Absence follows from acquisition origins and
-- initialized lifetime births. No callback-wide private-state frame is an input.
theorem native_step_keys_excluded {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} (namespaceLaws : NativeNamespaceContract native) (retirement : RetirementContract runtime)
    {before after : Processes} {first last : NativeProcesses} {tick : ActorTick runtime}
    (source : NativeExternalStep process child native hostUid before first tick after last)
    {keys : ObjectId → Prop} (operands : NativeKeyOperand namespaceLaws keys source)
    (initialized : ∀ object, keys object → tick.before.shared.allocated object = true)
    (prior : NativeKeysExcluded first keys) : NativeKeysExcluded last keys := by
  cases source with
  | application | ordinary | child => exact prior
  | launch recorded handoff => exact fun object key held => prior object key (transfer_held_before held)
  | native recorded call => exact native_call_keys_excluded namespaceLaws call operands initialized prior
  | retiring recorded exit =>
    exact fun object key held => prior object key (native_retirement_held_before retirement exit held)

private def native_inputs {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {before after : Processes} {first last : NativeProcesses} {tick : ActorTick runtime}
    (_source : NativeExternalStep process child native hostUid before first tick after last) : NativeProcesses := first

-- §FS-host-boundary.ownership: These per-position facts are produced by the real
-- joint history and retain the exact embedded native call, not another equal tick.
def NativeKeySafety {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} (keys : ObjectId → Prop)
    {before after : Processes} {first last : NativeProcesses} {ticks : List (ActorTick runtime)} :
    NativeExternalJournal process child native hostUid before first ticks after last → Prop
  | .nil _ callers => NativeKeysExcluded callers keys
  | .cons current rest => NativeKeysExcluded (native_inputs current) keys ∧ NativeKeySafety keys rest

theorem native_journal_keys_excluded {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} (namespaceLaws : NativeNamespaceContract native) (retirement : RetirementContract runtime)
    (lifetimes : LifetimeContract runtime)
    {start finish : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime start ticks finish)
    {before after : Processes} {first last : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid before first ticks after last)
    {keys : ObjectId → Prop} (operands : NativeKeyOperands namespaceLaws keys recording)
    (initialized : ∀ object, keys object → start.shared.allocated object = true)
    (prior : NativeKeysExcluded first keys) : NativeKeySafety keys recording := by
  induction journal generalizing before first with
  | nil => cases recording; exact prior
  | @cons tick ticks final tail ih =>
    cases recording with
    | cons current rest =>
      refine ⟨prior, ih rest operands.2 ?_ ?_⟩
      · intro object key
        exact actor_step_allocated lifetimes tick.operation object (initialized object key)
      · exact native_step_keys_excluded namespaceLaws retirement current operands.1 initialized prior

theorem native_selected_keys_excluded {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {before after : Processes} {first last : NativeProcesses} {ticks : List (ActorTick runtime)}
    (recording : NativeExternalJournal process child native hostUid before first ticks after last)
    {keys : ObjectId → Prop} (safe : NativeKeySafety keys recording)
    {position : Nat} (point : SelectedNativeCut process child native hostUid before after first last ticks position)
    (selected : selectNativeCut recording position = some point) : NativeKeysExcluded point.cut.priorNative keys := by
  induction recording generalizing position with
  | nil => simp only [selectNativeCut] at selected; cases selected
  | @cons before middle after first next last tick ticks current rest ih =>
    cases position with
    | zero =>
      have same : point = ⟨tick, ⟨[], ticks, rfl, rfl, before, middle, first, next, .nil _ _, current, rest⟩⟩ :=
        (Option.some.inj selected).symm
      cases same
      exact safe.1
    | succ position =>
      let extend := fun (chosen : SelectedNativeCut process child native hostUid middle after next last ticks position) =>
        ({ tick := chosen.tick
           cut := { chosen.cut with
             leading := tick :: chosen.cut.leading
             count := by simp only [List.length_cons, chosen.cut.count]
             shape := by simp only [chosen.cut.shape, List.cons_append]
             first := .cons current chosen.cut.first } } :
          SelectedNativeCut process child native hostUid before after first last (tick :: ticks) (position + 1))
      change (selectNativeCut rest position).map extend = some point at selected
      cases earlier : selectNativeCut rest position with
      | none => simp only [earlier, Option.map_none] at selected; cases selected
      | some chosen =>
        have prior := ih safe.2 chosen earlier
        simp only [earlier, Option.map_some] at selected
        have identity := (Option.some.inj selected).symm
        cases identity
        exact prior

-- §FS-host-boundary.publication: A native read/dup/spawn consumer selects the
-- actual before-table of this journal occurrence. Numeric FD equality is not used
-- to identify a key lifetime, and retired surviving references remain covered.
theorem native_selected_key_reference_excluded {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {before after : Processes} {first last : NativeProcesses} {ticks : List (ActorTick runtime)}
    (recording : NativeExternalJournal process child native hostUid before first ticks after last)
    {keys : ObjectId → Prop} (safe : NativeKeySafety keys recording)
    {position : Nat} (point : SelectedNativeCut process child native hostUid before after first last ticks position)
    (selected : selectNativeCut recording position = some point)
    {token : NativeToken} {references : NativeReferences} {fd : UInt64} {handle : Handle} {key : ObjectId}
    (input : point.cut.priorNative.references token = some references)
    (live : references.handles fd = some handle) (protectedKey : keys key) : handle.object ≠ key := by
  intro same
  have excluded := native_selected_keys_excluded recording safe point selected
  exact excluded key protectedKey (.inl ⟨token, references, input, .inl ⟨fd, handle, live, same⟩⟩)

end LeanCage.Host.Kernel
