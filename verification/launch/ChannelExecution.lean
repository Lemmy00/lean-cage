import ChannelProofs
import CallerPhysical

namespace LeanCage.Entry.CallerPhysical

-- §FS-entry.release: Cut the exact native occurrence, retaining every intervening parent operation.
theorem execution_native_cut {fs : Filesystem} {platform : PrimitiveContract fs}
    {runtime : OriginContract platform} {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {supervisor : SupervisorContract mayTrace owner child}
    {native : NativeContract runtime mayTrace owner child} {history : List Nat}
    {position : Nat} {before after : Context} {initial final : State}
    {journal : List Action} {trace : List (Request × Reply)} {controls : List TracerControl}
    (run : Execution supervisor native history position before initial journal trace controls after final)
    (leading : List (Request × Reply)) (request : Request) (reply : Reply)
    (trailing : List (Request × Reply)) (cut : trace = leading ++ (request, reply) :: trailing) :
    ∃ first rest firstControls restControls ordinal context origin state next changed,
      journal = first ++ .native :: rest ∧
      controls = firstControls ++ control owner child context :: restControls ∧
      ordinal = position + first.length ∧
      Execution supervisor native history position before initial first leading firstControls context state ∧
      native.returned ordinal context origin state request reply next changed ∧
      Execution supervisor native history (ordinal + 1) next changed rest trailing restControls after final := by
  induction run generalizing leading with
  | done => simp at cut
  | supervisor source operation rest ih =>
    obtain ⟨first, rest, firstControls, restControls, ordinal, context, origin, state, next,
      changed, journalCut, controlsCut, ordinalEq, leadingRun, selected, trailingRun⟩ := ih leading cut
    refine ⟨_ :: first, rest, firstControls, restControls, ordinal, context, origin, state,
      next, changed, ?_, controlsCut, ?_, .supervisor source operation leadingRun,
      selected, trailingRun⟩
    · simpa only [List.cons_append] using congrArg (List.cons _) journalCut
    · simp only [List.length_cons]; omega
  | @native position current middle last initial changed final journal trace controls
      selectedOrigin selectedRequest selectedReply operation rest ih =>
    cases leading with
    | nil =>
      have pair : (selectedRequest, selectedReply) = (request, reply) :=
        (List.cons.inj cut).1
      have remaining := (List.cons.inj cut).2
      have requestEq : selectedRequest = request := congrArg Prod.fst pair
      have replyEq : selectedReply = reply := congrArg Prod.snd pair
      subst request reply
      refine ⟨[], _, [], _, _, _, selectedOrigin, _, _, _, rfl, rfl, ?_, .done _ _ _,
        operation, ?_⟩
      · simp
      · simpa only [remaining] using rest
    | cons event leading =>
      have tailCut := (List.cons.inj cut).2
      obtain ⟨first, rest, firstControls, restControls, ordinal, context, origin, state, next,
        changed, journalCut, controlsCut, ordinalEq, leadingRun, selected, trailingRun⟩ := ih leading tailCut
      have eventEq := (List.cons.inj cut).1
      refine ⟨.native :: first, rest, control owner child current :: firstControls, restControls, ordinal, context,
        origin, state, next, changed, ?_, ?_, ?_, ?_, selected, trailingRun⟩
      · simpa only [List.cons_append] using congrArg (List.cons Action.native) journalCut
      · simpa only [List.cons_append] using congrArg (List.cons _) controlsCut
      · simp only [List.length_cons]; omega
      · rw [← eventEq]
        exact .native selectedOrigin selectedRequest selectedReply operation leadingRun

private theorem before_release_filter_order (p : Inputs) : FilterAtEnd (beforeRelease p) := by
  have absent : ∀ command ∈ beforeRelease p, command.request.op ≠ .filter := by
    intro command member
    rcases before_release_operations p command member with op | op | op | op <;> simp [op]
  simpa only [List.append_nil] using
    (filter_at_end_append (beforeRelease p) [] absent True.intro)

-- §FS-entry.release: The read, descriptor table and physical ordinal are the same occurrence.
theorem actual_release_read {fs : Filesystem} {platform : PrimitiveContract fs}
    {runtime : OriginContract platform} {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {supervisor : SupervisorContract mayTrace owner child}
    {native : NativeContract runtime mayTrace owner child} {history : List Nat}
    {position : Nat} {before after : Context} {initial final : State}
    {journal : List Action} {trace : List (Request × Reply)} {controls : List TracerControl}
    (p : Inputs) (normal : p.fault = "normal") {target : Request}
    (controlAtExec : AtExec (admission p) trace target)
    (source : CallerRequestsAllowed history) (good : Good owner history before)
    (clean : initial.filters = [])
    (run : Execution supervisor native history position before initial journal trace controls after final) :
    ∃ leading trailing reply first rest firstControls restControls ordinal context state next changed,
      trace = leading ++ ((releaseCommand p).request, reply) :: trailing ∧
      journal = first ++ .native :: rest ∧
      controls = firstControls ++ control owner child context :: restControls ∧
      ordinal = position + first.length ∧
      Execution supervisor native history position before initial first leading firstControls context state ∧
      native.returned ordinal context .kernel state (releaseCommand p).request reply next changed ∧
      Execution supervisor native history (ordinal + 1) next changed rest trailing restControls after final ∧
      state.handles = initial.handles ∧ reply.1 = 1 ∧ reply.2 = (⟨#[165]⟩ : ByteArray) ∧
      CallerControlUse owner child history (control owner child context) := by
  obtain ⟨_, accepted, _, _⟩ := admission_at_exec p controlAtExec
  rw [setup_release_cut p normal] at accepted
  obtain ⟨leading, trailing, traceCut, leadingAccepted, remaining⟩ := accepted_append accepted
  cases remaining with
  | cons command reply accepted tail =>
    obtain ⟨first, rest, firstControls, restControls, ordinal, context, origin, state, next,
      changed, journalCut, controlsCut, ordinalEq, leadingRun, operation, trailingRun⟩ :=
      execution_native_cut run leading (releaseCommand p).request reply _ traceCut
    have returned := execution_returns good leadingRun
    have guards : ∀ command ∈ beforeRelease p, GuardSound command := by
      intro command member
      apply setup_guards_sound p normal command
      rw [setup_release_cut p normal]
      exact List.mem_append_left _ member
    have kernelPrefix := accepted_kernel_from_clean platform runtime (beforeRelease p)
      leadingAccepted guards (before_release_filter_order p) clean
      (caller_returns_non_substituting source returned.1) (caller_returns_erased returned.1)
    have handleFrame := accepted_before_release_handles platform leadingAccepted guards
      (before_release_operations p) kernelPrefix
    have atReadClean := (accepted_before_release_filters platform leadingAccepted guards
      (before_release_operations p) kernelPrefix).trans clean
    have genuine := runtime.unmediated _ _ _ _ _ _
      (native.effect _ _ _ _ _ _ _ _ operation)
      (caller_control_non_substituting source returned.2) atReadClean
    subst origin
    have checked : reply.1 = 1 ∧ (reply.2 == (⟨#[165]⟩ : ByteArray)) = true := by
      simpa [releaseCommand, cmd, Expected.accepts] using accepted
    have bytes : reply.2 = (⟨#[165]⟩ : ByteArray) := by
      apply ByteArray.ext
      have data : (reply.2.data == #[165]) = true := checked.2
      simpa only [beq_iff_eq] using data
    exact ⟨leading, _, reply, first, rest, firstControls, restControls, ordinal, context,
      state, next, changed, traceCut, journalCut, controlsCut, ordinalEq, leadingRun,
      operation, trailingRun, handleFrame, checked.1, bytes, returned.2⟩

end LeanCage.Entry.CallerPhysical
