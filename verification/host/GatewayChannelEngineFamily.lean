import GatewayChannelEngineAbsence

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)} {pair : Pair}

private theorem actual_launch_handoff {first last : Processes} {current following : NativeProcesses}
    {tick : ActorTick runtime} (row : NativeExternalStep process child native hostUid first current tick last following)
    (actor : ActorId) (handles : UInt64 → Option Handle) (flags : UInt64 → Bool) (cwd : ObjectId)
    (action : tick.action = .launch actor handles flags cwd) :
    ∃ handoff, embeddedHandoff row = some handoff := by
  cases row with
  | application recorded notForeign notLaunch notRetiring => exact False.elim (notLaunch actor handles flags cwd action)
  | launch recorded handoff => exact ⟨handoff, rfl⟩
  | ordinary caller recorded foreign allowed => rw [foreign] at action; cases action
  | child recorded call => rw [call.action] at action; cases action
  | native recorded call retirementFrame others => rw [call.action] at action; cases action
  | retiring recorded exit => rw [exit.action] at action; cases action

-- §AR-host-boundary.interfaces.gateway: Select the actual handoff stored in
-- this row. Its channel equations are source-built; global pair freshness
-- turns those equations into the raw-table absence used by the family fold.
theorem actual_launch_excludes_original_socket
    (lifetimes : LifetimeContract runtime) (namespaceLaws : NativeNamespaceContract native)
    {initial : World} {final : Population} (source : ActorJournal runtime (Population.empty initial) ticks final)
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    (channels : EngineChannelRows journal)
    (birth : PairBirthEntry process child native hostUid before after callers next ticks pair)
    (actual : ActualPairBirth journal birth)
    (tick : ActorTick runtime) (member : tick ∈ ticks)
    (actor : ActorId) (handles : UInt64 → Option Handle) (flags : UInt64 → Bool) (cwd : ObjectId)
    (action : tick.action = .launch actor handles flags cwd) : SocketTableAbsent birth.callerSocket handles := by
  obtain ⟨position, selected⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨cut, current⟩ := selectNativeCut_exists journal selected
  let point : SelectedNativeCut process child native hostUid before after callers next ticks position := ⟨tick, cut⟩
  obtain ⟨handoff, stored⟩ := actual_launch_handoff point.cut.current actor handles flags cwd action
  obtain ⟨fields⟩ := channels position point current handoff stored
  have noCaller := source_channels_exclude_caller lifetimes namespaceLaws source journal birth actual fields
  obtain ⟨sameActor, sameHandles, sameFlags, sameCwd⟩ := ActorAction.launch.inj (action.symm.trans handoff.action)
  intro descriptor handle held identity
  have captured : handoff.execution.references.rawProjection.handles descriptor = some handle := sameHandles ▸ held
  exact noCaller descriptor handle captured identity.1

-- §FS-host-boundary.ownership: This covers the complete post-birth engine
-- family on the supplied global history. Earlier engines start excluded by
-- freshness; every later handoff is checked from its real source pair rows.
theorem actual_engine_family_excludes_caller_ofd {ipc : ObjectId → Prop}
    (sockets : SocketPairContract native ipc) (descriptions : NativeDescriptionContract native)
    (raw : RawReferenceLifetimeContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (namespaceLaws : NativeNamespaceContract native)
    {initial : World} {final : Population} (source : ActorJournal runtime (Population.empty initial) ticks final)
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    (channels : EngineChannelRows journal)
    (birth : PairBirthEntry process child native hostUid before after callers next ticks pair)
    (actual : ActualPairBirth journal birth) :
    EngineSocketAbsent final birth.callerSocket ∧ ∀ tick ∈ birth.cut.trailing,
      EngineSocketAbsent tick.before birth.callerSocket ∧ EngineSocketAbsent tick.after birth.callerSocket := by
  have arranged := source
  rw [birth.cut.shape] at arranged
  obtain ⟨middle, preceding, rest⟩ := actor_journal_split birth.cut.leading (birth.tick :: birth.cut.trailing) arranged
  cases rest with
  | cons tail =>
    apply engine_socket_absent_journal raw sdk references tail birth.callerSocket
      (pair_birth_description_allocated descriptions birth .caller)
      (engines_exclude_new_pair sockets descriptors lifetimes references source birth)
    intro tick member actor handles flags cwd action
    apply actual_launch_excludes_original_socket lifetimes namespaceLaws source journal channels birth actual tick _ actor handles flags cwd action
    rw [birth.cut.shape]
    simp [member]

end LeanCage.Host.PrivateStreams
