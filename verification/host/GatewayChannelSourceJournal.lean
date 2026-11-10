import GatewayChannelResidualSources
import GatewayChannelResponsePrefix

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
  {before after : Processes} {callers next : NativeProcesses} {ticks : List (ActorTick runtime)} {pair : Pair} {Token : Type}

-- §AR-host-boundary.primitives: This records raw samples and the mandatory
-- native read/engine ACK partition only. It assumes no exclusive reader,
-- nondiscard property, expected response or successful source continuation.
inductive SourceChannelJournal
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    (primitive : Primitive process child native hostUid before after callers next ticks pair Token) :
    Nat → List (ActorTick runtime) → PhysicalState → List Record → PhysicalState → Type 1 where
  | nil (position : Nat) (state : PhysicalState) : SourceChannelJournal journal primitive position [] state [] state
  | cons {position : Nat} {tick : ActorTick runtime} {remaining : List (ActorTick runtime)}
      {initial pending read acknowledged final : PhysicalState} {progress readings replies rest : List Record}
      (selected : ticks[position]? = some tick)
      (batch : ResidualJournal primitive position initial progress pending)
      (positions : ∀ record ∈ progress, record.position = position)
      (unobserved : ∀ record ∈ progress, pendingRecord record)
      (reader : NativeReadRow journal primitive position pending readings read)
      (row : EngineRow primitive position tick read replies acknowledged)
      (tail : SourceChannelJournal journal primitive (position + 1) remaining acknowledged rest final) :
      SourceChannelJournal journal primitive position (tick :: remaining) initial
        (progress ++ readings ++ replies ++ rest) final

private theorem ResidualJournal.property
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {boundary : Nat} {initial final : PhysicalState} {records : List Record}
    (actual : ResidualJournal primitive boundary initial records final) (property : Record → Prop)
    (produced : ∀ {initial final record}, ∀ step : ObservedStep primitive initial record final,
      ResidualStep step → property record) :
    ∀ record ∈ records, property record := by
  induction actual with
  | nil => simp
  | cons order step residual tail ih =>
    intro record member
    rcases List.mem_cons.mp member with same | later
    · subst record
      exact produced step residual
    · exact ih record later

private theorem native_read_preserves
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {position : Nat} {initial final : PhysicalState} {records : List Record}
    (row : NativeReadRow journal primitive position initial records final) :
    ∀ action ∈ records.flatMap Record.actions, preservesReceivedBytes .caller action := by
  cases row with
  | outside => simp
  | received => simp [preservesReceivedBytes]

private theorem engine_row_actions_empty
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {position : Nat} {tick : ActorTick runtime} {initial final : PhysicalState} {records : List Record}
    (row : EngineRow primitive position tick initial records final) : records.flatMap Record.actions = [] := by
  cases row <;> rfl

section Sources
variable {ipc : ObjectId → Prop}
  (sockets : SocketPairContract native ipc) (descriptions : NativeDescriptionContract native)
  (raw : RawReferenceLifetimeContract kernel) (sdk : RuntimeDescriptorContract runtime)
  (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
  (references : ReferenceContract runtime) (namespaceLaws : NativeNamespaceContract native)
  {initialWorld : World} {population : Population}
  (source : ActorJournal runtime (Population.empty initialWorld) ticks population)
  (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
  (channels : EngineChannelRows journal)
  (birth : PairBirthEntry process child native hostUid before after callers next ticks pair)
  (actualBirth : ActualPairBirth journal birth)
  (referenceRuntime : SocketReferenceRuntime process child native hostUid)
  {first last : SocketReferenceSnapshot} (recording : SocketReferenceRecording referenceRuntime journal first last)
  {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
  {additional : Nat → SocketLifetime → Prop}
  (effects : SocketResidualRuntime journal primitive referenceRuntime recording birth.callerSocket additional)
  (nativeSources : NativeSocketRowSources journal birth.callerSocket)
  (otherSources : ∀ position, ¬ additional position birth.callerSocket)

include sockets descriptions raw sdk descriptors lifetimes references namespaceLaws source channels actualBirth effects nativeSources otherSources

-- §FS-host-boundary.caller: The previous otherReads hypothesis is produced
-- from actual per-operation source receipts and the derived raw-engine fold.
noncomputable def SourceChannelJournal.channel
    {position : Nat} {remaining : List (ActorTick runtime)}
    {initial final : PhysicalState} {records : List Record}
    (actual : SourceChannelJournal journal primitive position remaining initial records final) :
    ChannelJournal journal primitive position remaining initial records final := by
  induction actual with
  | nil => exact .nil _ _
  | @cons position tick remaining initial pending read acknowledged final progress readings replies rest selected batch positions unobserved reader row tail ih =>
    have noRead : ∀ record ∈ progress, ∀ bytes, Action.read .caller bytes ∉ record.actions := by
      obtain ⟨cut, atCut⟩ := selectNativeCut_exists journal selected
      let point : SelectedNativeCut process child native hostUid before after callers next ticks position := ⟨tick, cut⟩
      obtain ⟨current, following, preceding, suffix, sampled, operation, suffixAt⟩ :=
        SocketReferenceRecording.selected_cut referenceRuntime recording point atCut
      have properties := batch.property (fun record => record.position = position → ∀ bytes, Action.read .caller bytes ∉ record.actions) (by
        intro input output record step residual atPosition
        exact actual_residual_step_no_caller_read sockets descriptions raw sdk descriptors lifetimes references namespaceLaws
          source journal channels birth actualBirth referenceRuntime recording effects nativeSources point atCut
          current following sampled (otherSources position) step residual atPosition)
      intro record member
      exact properties record member (positions record member)
    exact .cons selected ⟨batch.erase, positions, unobserved⟩ noRead reader row ih

-- A real receive supplies the last-OFD lifetime anchor. All other discard
-- causes are handled by their exact source opcode/operand receipts.
theorem SourceChannelJournal.preserves_received
    (nativeDescriptors : NativeReferenceContract native)
    (received : NativeReadEntry process child native hostUid before after callers next ticks pair)
    (actualReceive : ActualNativeRead journal received) (terminal : received.position + 1 = ticks.length)
    (receiver : received.receiver = .caller) (description : received.handle.description = birth.firstHandle.description)
    {position : Nat} {remaining : List (ActorTick runtime)}
    {initial final : PhysicalState} {records : List Record}
    (actual : SourceChannelJournal journal primitive position remaining initial records final) :
    ∀ action ∈ records.flatMap Record.actions, preservesReceivedBytes .caller action := by
  induction actual with
  | nil => simp
  | @cons position tick remaining initial pending read acknowledged final progress readings replies rest selected batch positions unobserved reader row tail ih =>
    obtain ⟨cut, atCut⟩ := selectNativeCut_exists journal selected
    let point : SelectedNativeCut process child native hostUid before after callers next ticks position := ⟨tick, cut⟩
    obtain ⟨current, following, preceding, suffix, sampled, operation, suffixAt⟩ :=
      SocketReferenceRecording.selected_cut referenceRuntime recording point atCut
    have progressSource : ∀ record ∈ progress, ∀ action ∈ record.actions, preservesReceivedBytes .caller action := by
      have properties := batch.property (fun record => record.position = position → ∀ action ∈ record.actions, preservesReceivedBytes .caller action) (by
        intro input output record step residual atPosition
        exact actual_residual_step_preserves_received sockets descriptions raw sdk descriptors lifetimes references namespaceLaws
          source journal channels birth actualBirth referenceRuntime recording effects nativeSources
          nativeDescriptors received actualReceive terminal receiver description point atCut current following sampled
          (otherSources position) step atPosition)
      intro record member
      exact properties record member (positions record member)
    intro action member
    simp only [List.flatMap_append, List.mem_append, engine_row_actions_empty row, List.mem_nil_iff, or_false] at member
    rcases member with (inside | inside) | inside
    · obtain ⟨record, belongs, chosen⟩ := List.mem_flatMap.mp inside
      exact progressSource record belongs action chosen
    · exact native_read_preserves journal reader action inside
    · exact ih action inside

end Sources
end LeanCage.Host.PrivateStreams
