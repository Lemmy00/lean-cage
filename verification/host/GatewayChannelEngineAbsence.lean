import GatewayChannelEngineLaunches
import GatewayChannelDescriptionLifetimes
import GatewayChannelPair
import FilesystemReferenceLifetime

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)} {pair : Pair}

def PairBirthEntry.callerSocket
    (entry : PairBirthEntry process child native hostUid before after callers next ticks pair) : SocketLifetime :=
  ⟨pair.caller, entry.firstHandle.description⟩

def EngineSocketAbsent (population : Population) (socket : SocketLifetime) : Prop :=
  ∀ actor engine, population.actors actor = some engine → SocketTableAbsent socket engine.references

private theorem foreign_actor_tables {initial final : Population} {caller : Credentials}
    (actual : ActorStep runtime (.foreign caller) initial final) : final.actors = initial.actors := by
  cases actual
  rfl

theorem pair_birth_description_fresh {ipc : ObjectId → Prop} (sockets : SocketPairContract native ipc)
    (birth : PairBirthEntry process child native hostUid before after callers next ticks pair) :
    birth.tick.before.shared.descriptionAllocated birth.firstHandle.description = false := by
  obtain ⟨allocation⟩ := sockets.created birth.call birth.first birth.second birth.operation birth.product
  have same := Option.some.inj (allocation.leftOutput.symm.trans birth.firstInput)
  exact same ▸ allocation.leftDescriptionFresh

-- §FS-host-boundary.ownership: Before this real pair birth, an existing
-- engine cannot hold its future socket OFD. The actual foreign creation row
-- leaves each engine's raw table untouched; no process-role premise is used.
theorem engines_exclude_new_pair {ipc : ObjectId → Prop} (sockets : SocketPairContract native ipc)
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime)
    {initial : World} {final : Population}
    (source : ActorJournal runtime (Population.empty initial) ticks final)
    (birth : PairBirthEntry process child native hostUid before after callers next ticks pair) :
    EngineSocketAbsent birth.tick.after birth.callerSocket := by
  have consistent := (actor_journal_consistent descriptors lifetimes references source
    (empty_population_consistent initial)).2 birth.tick (List.mem_of_getElem? (pair_birth_selected birth)) |>.1
  have fresh := pair_birth_description_fresh sockets birth
  have tables : birth.tick.after.actors = birth.tick.before.actors :=
    foreign_actor_tables (birth.call.action ▸ birth.tick.operation)
  intro actor engine present descriptor handle held identity
  have original := tables ▸ present
  have allocated := (consistent actor engine original descriptor handle held).2.1
  change handle.object = pair.caller ∧ handle.description = birth.firstHandle.description at identity
  rw [identity.2, fresh] at allocated
  cases allocated

-- Each actual step retains old raw references or introduces a fresh OFD.
-- Launch is the sole new-table boundary and consumes its exact exec evidence.
theorem engine_socket_absent_step
    (raw : RawReferenceLifetimeContract kernel) (sdk : RuntimeDescriptorContract runtime)
    {action : ActorAction} {initial final : Population} (actual : ActorStep runtime action initial final)
    (socket : SocketLifetime) (old : initial.shared.descriptionAllocated socket.description = true)
    (prior : EngineSocketAbsent initial socket)
    (launch : ∀ actor handles flags cwd, action = .launch actor handles flags cwd → SocketTableAbsent socket handles) :
    EngineSocketAbsent final socket := by
  intro query engine afterPresent descriptor handle held identity
  cases actual with
  | @launch population actor handles flags cwd fresh absent inherited =>
    by_cases same : query = actor
    · subst query
      simp only [Population.launch, Population.install, ite_eq_left] at afterPresent
      cases afterPresent
      exact launch actor handles flags cwd rfl descriptor handle held identity
    · exact prior query engine (by
        simpa only [Population.launch, Population.install, ite_eq_right same] using afterPresent) descriptor handle held identity
  | @returned β population actor current effect next reply world present alive head operation =>
    by_cases same : query = actor
    · subst query
      simp only [Population.advance, Population.install, ite_eq_left] at afterPresent
      cases afterPresent
      have original := operation_reference_before raw sdk operation (by simpa only [Population.project, identity.2] using old) held
      exact prior actor current present descriptor handle original identity
    · exact prior query engine (by
        simpa only [Population.advance, Population.install, ite_eq_right same] using afterPresent) descriptor handle held identity
  | @lost β population actor current effect next world present alive head operation =>
    by_cases same : query = actor
    · subst query
      simp only [Population.advance, Population.install, ite_eq_left] at afterPresent
      cases afterPresent
      have original := operation_reference_before raw sdk operation (by simpa only [Population.project, identity.2] using old) held
      exact prior actor current present descriptor handle original identity
    · exact prior query engine (by
        simpa only [Population.advance, Population.install, ite_eq_right same] using afterPresent) descriptor handle held identity
  | foreign operation => exact prior query engine afterPresent descriptor handle held identity
  | @retire population actor current observation world present operation =>
    by_cases same : query = actor
    · subst query
      simp only [Population.advance, Population.install, ite_eq_left] at afterPresent
      cases afterPresent
      exact prior actor current present descriptor handle
        (sdk.engine_subset _ _ _ _ _ _ _ operation held) identity
    · exact prior query engine (by
        simpa only [Population.advance, Population.install, ite_eq_right same] using afterPresent) descriptor handle held identity
  | nativeRetire operation => exact prior query engine afterPresent descriptor handle held identity

-- §AR-host-boundary.interfaces.gateway: This is the cumulative raw-table
-- fold over the SAME history. It includes older engines, new launches, lost
-- replies and partial retirement, without excluding any of those transitions.
theorem engine_socket_absent_journal
    (raw : RawReferenceLifetimeContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (references : ReferenceContract runtime)
    {initial final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime initial all final) (socket : SocketLifetime)
    (old : initial.shared.descriptionAllocated socket.description = true)
    (prior : EngineSocketAbsent initial socket)
    (launches : ∀ tick ∈ all, ∀ actor handles flags cwd,
      tick.action = .launch actor handles flags cwd → SocketTableAbsent socket handles) :
    EngineSocketAbsent final socket ∧ ∀ tick ∈ all,
      EngineSocketAbsent tick.before socket ∧ EngineSocketAbsent tick.after socket := by
  induction journal with
  | nil => exact ⟨prior, by intro tick impossible; cases impossible⟩
  | @cons tick rest final tail ih =>
    have next := engine_socket_absent_step raw sdk tick.operation socket old prior (launches tick (by simp))
    have allocated := actor_step_description_allocated references tick.operation socket.description old
    obtain ⟨finalAbsent, restAbsent⟩ := ih allocated next (fun other member => launches other (by simp [member]))
    refine ⟨finalAbsent, ?_⟩
    intro selected member
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨prior, next⟩
    · exact restAbsent selected later

end LeanCage.Host.PrivateStreams
