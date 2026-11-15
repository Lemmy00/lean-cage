import GatewayChannelEngineSource
import FilesystemNativeLaunchHistory

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)}

-- §FS-host-boundary.ownership: The execution row is selected from this
-- supplied journal value. It retains the embedded call and complete tables;
-- an alternative witness for an equal foreign tick cannot replace them.
structure CanonicalNativeExecution
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    (token : NativeToken) (execution : NativeExecution) where
  position : Nat
  point : SelectedNativeCut process child native hostUid before after callers next ticks position
  selected : selectNativeCut journal position = some point
  call : NativeCallAt native point.tick point.cut.priorNative point.cut.nextNative
  embedded : embeddedNative point.cut.current = some call
  identity : call.token = token
  product : call.product = .executed execution.image
  stored : point.cut.nextNative.executions token = some execution

-- §AR-host-boundary.primitives: This is the exact table stored by the same
-- selected exec, including SDK/stderr slots. It does not derive exec from
-- spawn success, process exit, reaping or an eventual SDK acknowledgement.
theorem CanonicalNativeExecution.actual_table
    {journal : NativeExternalJournal process child native hostUid before callers ticks after next}
    {token : NativeToken} {execution : NativeExecution} (cut : CanonicalNativeExecution journal token execution) :
    cut.call.operation = .exec execution.arguments ∧ cut.call.afterReferences = execution.references := by
  obtain ⟨arguments, actual, operation, stored, _image, argumentBytes, table⟩ := native_exec_table cut.call cut.product
  have same : actual = execution := Option.some.inj (stored.symm.trans (by simpa only [cut.identity] using cut.stored))
  have argumentsSame : execution.arguments = arguments :=
    (congrArg NativeExecution.arguments same).symm.trans argumentBytes
  exact ⟨operation.trans (congrArg NativeOperation.exec argumentsSame.symm),
    table.trans (congrArg NativeExecution.references same)⟩

theorem actual_canonical_execution_source
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    {token : NativeToken} {execution : NativeExecution} (stored : next.executions token = some execution) :
    callers.executions token = some execution ∨ Nonempty (CanonicalNativeExecution journal token execution) := by
  induction journal with
  | nil => exact .inl stored
  | @cons before middle after callers following final tick rest actual tail ih =>
    rcases ih stored with current | later
    · cases actual with
      | application | launch | ordinary | child => exact .inl current
      | retiring recorded exit => rw [exit.next] at current; exact .inl current
      | native recorded call retirementFrame otherReferences =>
        rcases native.execution_origin _ _ _ _ _ _ _ _ _ _ _ call.native current with old | ⟨identity, product⟩
        · exact .inl old
        · exact .inr ⟨{
            position := 0
            point := ⟨tick, ⟨[], rest, rfl, rfl, before, middle, callers, following, .nil _ _,
              .native recorded call retirementFrame otherReferences, tail⟩⟩
            selected := rfl
            call
            embedded := rfl
            identity := identity.symm
            product
            stored := current }⟩
    · obtain ⟨cut⟩ := later
      let extend := fun (chosen : SelectedNativeCut process child native hostUid middle after following final rest cut.position) =>
        ({ tick := chosen.tick
           cut := { chosen.cut with
             leading := tick :: chosen.cut.leading
             count := by simp only [List.length_cons, chosen.cut.count]
             shape := by simp only [chosen.cut.shape, List.cons_append]
             first := .cons actual chosen.cut.first } } :
          SelectedNativeCut process child native hostUid before after callers final (tick :: rest) (cut.position + 1))
      let point := extend cut.point
      refine .inr ⟨{
        position := cut.position + 1
        point
        selected := ?_
        call := cut.call
        embedded := cut.embedded
        identity := cut.identity
        product := cut.product
        stored := cut.stored }⟩
      change (selectNativeCut tail cut.position).map extend = some point
      rw [cut.selected]
      rfl

theorem actual_handoff_canonical_execution
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    {tick : ActorTick runtime} (handoff : NativeHandoffAt tick next)
    (absent : callers.executions handoff.actor = none) :
    Nonempty (CanonicalNativeExecution journal handoff.actor handoff.execution) := by
  rcases actual_canonical_execution_source journal handoff.recorded with old | current
  · rw [absent] at old
    cases old
  · exact current

-- §FS-host-boundary.caller: A checked C row observation feeds the actual
-- selected exec table. The old source role is never used as a substitute
-- for the complete handoff snapshot or for the actual canonical row.
theorem CanonicalNativeExecution.channel_evidence
    {journal : NativeExternalJournal process child native hostUid before callers ticks after next}
    {token : NativeToken} {execution : NativeExecution} (cut : CanonicalNativeExecution journal token execution)
    {code : NativeCode.CallRow} (interpreted : NativeCode.Interprets code cut.call)
    {data control : Nat} (source : NativeChannels.Evidence code.afterReferences data control) :
    NativeChannels.Evidence (NativeCode.encodeReferences execution.references) data control := by
  simpa only [interpreted.output, cut.actual_table.2] using source

theorem engine_channels_from_canonical_source {ipc : ObjectId → Prop} (sockets : SocketPairContract native ipc)
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    {position : Nat} (point : SelectedNativeCut process child native hostUid before after callers next ticks position)
    (_selected : selectNativeCut journal position = some point)
    (handoff : NativeHandoffAt point.tick point.cut.priorNative)
    (_stored : embeddedHandoff point.cut.current = some handoff)
    (cut : CanonicalNativeExecution point.cut.first handoff.actor handoff.execution)
    (dataUse controlUse : ChannelCode.PairUse) (dataSource : dataUse.Consistent) (controlSource : controlUse.Consistent)
    (dataPoint : SelectedNativeCut process child native hostUid before after callers next ticks dataUse.position)
    (dataSelected : selectNativeCut journal dataUse.position = some dataPoint)
    (dataCall : NativeCallAt native dataPoint.tick dataPoint.cut.priorNative dataPoint.cut.nextNative)
    (dataStored : embeddedNative dataPoint.cut.current = some dataCall)
    (dataInterpreted : NativeCode.Interprets dataUse.row dataCall)
    (controlPoint : SelectedNativeCut process child native hostUid before after callers next ticks controlUse.position)
    (controlSelected : selectNativeCut journal controlUse.position = some controlPoint)
    (controlCall : NativeCallAt native controlPoint.tick controlPoint.cut.priorNative controlPoint.cut.nextNative)
    (controlStored : embeddedNative controlPoint.cut.current = some controlCall)
    (controlInterpreted : NativeCode.Interprets controlUse.row controlCall)
    (execCode : NativeCode.CallRow) (execInterpreted : NativeCode.Interprets execCode cut.call)
    (source : NativeChannels.Evidence execCode.afterReferences dataUse.rightObject controlUse.rightObject) :
    Nonempty (EngineSourceChannels journal handoff) :=
  engine_channels_from_source_pairs sockets journal handoff dataUse controlUse dataSource controlSource
    dataPoint dataSelected dataCall dataStored dataInterpreted
    controlPoint controlSelected controlCall controlStored controlInterpreted (cut.channel_evidence execInterpreted source)

end LeanCage.Host.PrivateStreams
