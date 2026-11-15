import GatewayChannelOFDReferences
import GatewayChannelAliasJournal
import GatewayChannelReferenceHistory

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

-- §AR-host-boundary.primitives: A new open description may name an old
-- inode, including an O_PATH view. Only object+OFD identity supplies the
-- alias relation below; the primitive has no IPC or safe-source premise.
inductive DescriptorOFDOrigin {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {native : NativePrimitive kernel} {tick : ActorTick runtime} {before after : NativeProcesses}
    (call : NativeCallAt native tick before after) (fd : UInt64) (handle : Handle) : Type where
  | retained (original : Handle) (input : call.beforeReferences.handles fd = some original)
      (object : handle.object = original.object) (description : handle.description = original.description)
      (flags : call.afterReferences.closeOnExec fd = call.beforeReferences.closeOnExec fd) :
      DescriptorOFDOrigin call fd handle
  | duplicated (source : UInt64) (original : Handle) (closeExec : Bool)
      (input : call.beforeReferences.handles source = some original)
      (object : handle.object = original.object) (description : handle.description = original.description)
      (operation : DescriptorDuplication call.operation source fd closeExec)
      (flags : call.afterReferences.closeOnExec fd = closeExec) : DescriptorOFDOrigin call fd handle
  | flag (argument : UInt64) (input : call.beforeReferences.handles fd = some handle)
      (operation : call.operation = .fcntl fd 2 argument)
      (flags : call.afterReferences.closeOnExec fd = (argument &&& 1 != 0)) :
      DescriptorOFDOrigin call fd handle
  | freshDescription (allocated : tick.before.shared.descriptionAllocated handle.description = false) :
      DescriptorOFDOrigin call fd handle

structure NativeOFDOriginContract {kernel : Contract} (native : NativePrimitive kernel) : Prop where
  output : ∀ {runtime : PrimitiveActorRuntime kernel} {tick : ActorTick runtime} {before after : NativeProcesses}
    (call : NativeCallAt native tick before after) fd handle,
    call.afterReferences.handles fd = some handle → Nonempty (DescriptorOFDOrigin call fd handle)

def SocketAliasesCloseExec (socket : SocketLifetime) (references : NativeReferences) : Prop :=
  ∀ fd handle, references.handles fd = some handle → socket.matches handle → references.closeOnExec fd = true

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {native : NativePrimitive kernel} {tick : ActorTick runtime} {before after : NativeProcesses}

private theorem old_socket_description {socket : SocketLifetime} {handle : Handle}
    (allocated : tick.before.shared.descriptionAllocated socket.description = true)
    (identity : socket.matches handle) : tick.before.shared.descriptionAllocated handle.description = true := by
  simpa only [identity.2] using allocated

-- §FS-host-boundary.ownership: Concrete source flag operands preserve only
-- the original socket OFD aliases. A distinct OFD for the same inode remains
-- admitted with its actual flag, rather than being erased by the model.
theorem native_source_preserves_socket_cloexec
    (platform : NativeOFDOriginContract native) (call : NativeCallAt native tick before after)
    (socket : SocketLifetime) (allocated : tick.before.shared.descriptionAllocated socket.description = true)
    (authority : NativeFlagAuthority call socket.object) (initial : SocketAliasesCloseExec socket call.beforeReferences) :
    SocketAliasesCloseExec socket call.afterReferences := by
  intro fd handle found identity
  obtain ⟨origin⟩ := platform.output call fd handle found
  cases origin with
  | retained original input object description flags =>
    exact flags.trans (initial fd original input ⟨object.symm.trans identity.1, description.symm.trans identity.2⟩)
  | freshDescription fresh =>
    have old := old_socket_description allocated identity
    rw [fresh] at old
    cases old
  | duplicated source original closeExec input object description operation flags =>
    cases authority with
    | unchanged allowed => exact False.elim (allowed.1 source fd closeExec operation)
    | cloexec source minimum actual => exact flags.trans (DescriptorDuplication.cloexec operation actual)
    | operands allowed =>
      exact False.elim (allowed source original operation.operand input (object.symm.trans identity.1))
  | flag argument input operation flags =>
    cases authority with
    | unchanged allowed => exact False.elim (allowed.2 fd argument operation)
    | cloexec source minimum actual => rw [actual] at operation; cases operation
    | operands allowed =>
      exact False.elim (allowed fd handle (operation ▸ .fcntl fd 2 argument) input identity.1)

-- The fresh-description branch requires no fresh-object premise. This is
-- the precise old-inode case omitted by the predecessor's universal ABI.
def existing_inode_fresh_ofd_origin (call : NativeCallAt native tick before after) (fd : UInt64) (handle : Handle)
    (fresh : tick.before.shared.descriptionAllocated handle.description = false) : DescriptorOFDOrigin call fd handle :=
  .freshDescription fresh

theorem different_ofd_does_not_constrain_flags (socket : SocketLifetime) (references : NativeReferences)
    (descriptor : UInt64) (handle : Handle) (different : handle.description ≠ socket.description) :
    ∀ fd candidate, (fun slot => if slot = descriptor then some handle else references.handles slot) fd = some candidate →
      socket.matches candidate → fd ≠ descriptor := by
  intro fd candidate input identity equal
  subst fd
  have same : handle = candidate := Option.some.inj (by simpa only [ite_true] using input)
  exact different ((congrArg Handle.description same).trans identity.2)

-- This witnesses the predecessor's missing representation case, without
-- asserting an application can acquire a private FD. The final source/caller
-- authority must still be checked on that operation's real operands.
theorem old_object_origin_does_not_cover_new_open {ipc : ObjectId → Prop}
    (call : NativeCallAt native tick before after) (fd : UInt64) (handle : Handle) (request : Request)
    (operation : call.operation = .vfs (.adapted request))
    (absent : call.beforeReferences.handles fd = none)
    (old : tick.before.shared.allocated handle.object = true) (kind : ipc handle.object) :
    ¬ Nonempty (NativeDescriptorOrigin ipc call fd handle) := by
  rintro ⟨origin⟩
  cases origin with
  | retained original input object description flags => rw [absent] at input; cases input
  | duplicated source original closeExec input object description duplicate flags =>
    rcases duplicate with ⟨minimum, actual, _⟩ | ⟨minimum, actual, _⟩ | ⟨flags, actual, _⟩ <;>
      rw [operation] at actual <;> cases actual
  | flag argument input actual flags => rw [operation] at actual; cases actual
  | fresh allocated => rw [old] at allocated; cases allocated
  | nonIpc outside => exact outside kind

def NativeSocketAliasesCloseExec (socket : SocketLifetime) (processes : NativeProcesses) : Prop :=
  ∀ token references, processes.allocated token = true → processes.references token = some references →
    SocketAliasesCloseExec socket references

-- The same copied fork table is retained; no full-FD or stderr/support slot
-- is dropped merely because only the raw engine channels are later projected.
theorem native_call_preserves_socket_aliases
    (fork : NativeCode.ForkReferences (runtime := runtime) native)
    (call : NativeCallAt native tick before after) (socket : SocketLifetime)
    (initial : NativeSocketAliasesCloseExec socket before)
    (own : SocketAliasesCloseExec socket call.afterReferences) : NativeSocketAliasesCloseExec socket after := by
  intro token references active present
  by_cases same : token = call.token
  · subst token
    have identity := Option.some.inj (call.outputTable.symm.trans present)
    exact identity ▸ own
  · by_cases existed : before.allocated token = true
    · rcases native.other_references _ _ _ _ _ _ _ _ _ _ call.native same existed with retained | absent
      · exact initial token references existed (retained.symm.trans present)
      · rw [absent] at present
        cases present
    · have unallocated : before.allocated token = false := by
        cases current : before.allocated token
        · rfl
        · exact False.elim (existed current)
      obtain ⟨arguments, birth, operation, product, recorded, parent, fields⟩ :=
        native.fresh_source _ _ _ _ _ _ _ _ _ _ call.native unallocated active
      have cloned := fork.cloned tick before after call token product
      have identity := Option.some.inj (cloned.symm.trans present)
      exact identity ▸ initial call.token call.beforeReferences call.active call.inputTable

def NativeDescriptionsLive (processes : NativeProcesses) (world : World) : Prop :=
  ∀ token references, processes.allocated token = true → processes.references token = some references →
    ∀ fd handle, references.handles fd = some handle → world.descriptionAllocated handle.description = true

theorem pair_initializes_original_ofd_cloexec {ipc : ObjectId → Prop}
    (fork : NativeCode.ForkReferences (runtime := runtime) native)
    {call : NativeCallAt native tick before after} {first second : UInt64}
    (allocation : PairAllocation ipc call first second)
    (live : NativeDescriptionsLive before tick.before.shared) :
    NativeSocketAliasesCloseExec ⟨allocation.left.object, allocation.left.description⟩ after := by
  let socket : SocketLifetime := ⟨allocation.left.object, allocation.left.description⟩
  apply native_call_preserves_socket_aliases fork call socket
  · intro token references active present fd handle found identity
    have allocated := live token references active present fd handle found
    rw [identity.2] at allocated
    change tick.before.shared.descriptionAllocated allocation.left.description = true at allocated
    rw [allocation.leftDescriptionFresh] at allocated
    cases allocated
  · intro fd handle found identity
    by_cases left : fd = first
    · subst fd
      exact allocation.leftCloseExec
    · by_cases right : fd = second
      · subst fd
        have same := Option.some.inj (allocation.rightOutput.symm.trans found)
        have equal := (congrArg Handle.description same).trans identity.2
        exact False.elim (allocation.descriptionsSeparate equal.symm)
      · have input := (allocation.otherOutputs fd left right).symm.trans found
        have allocated := live call.token call.beforeReferences call.active call.inputTable fd handle input
        rw [identity.2] at allocated
        change tick.before.shared.descriptionAllocated allocation.left.description = true at allocated
        rw [allocation.leftDescriptionFresh] at allocated
        cases allocated

variable {process : ProcessContract runtime} {child : ChildPrimitive kernel} {hostUid : Nat}

theorem native_row_socket_aliases
    (platform : NativeOFDOriginContract native) (fork : NativeCode.ForkReferences (runtime := runtime) native)
    {first last : Processes} {current following : NativeProcesses} {tick : ActorTick runtime}
    (actual : NativeExternalStep process child native hostUid first current tick last following)
    (socket : SocketLifetime) (allocated : tick.before.shared.descriptionAllocated socket.description = true)
    (source : NativeRowFlagSource actual socket.object) (initial : NativeSocketAliasesCloseExec socket current) :
    NativeSocketAliasesCloseExec socket following := by
  cases actual with
  | application | ordinary | child => exact initial
  | launch recorded handoff =>
    intro token references active present
    by_cases same : token = handoff.actor
    · simp only [NativeProcesses.transfer, same, ite_eq_left] at present
      cases present
    · exact initial token references active (by
        simpa only [NativeProcesses.transfer, ite_eq_right same] using present)
  | native recorded call retiring others =>
    apply native_call_preserves_socket_aliases fork call socket initial
    exact native_source_preserves_socket_cloexec platform call socket allocated source
      (initial call.token call.beforeReferences call.active call.inputTable)
  | retiring recorded exit =>
    intro token references active present
    rw [exit.next] at present active
    by_cases same : token = exit.token
    · simp only [NativeProcesses.retire, same, ite_eq_left] at present
      cases present
    · exact initial token references active (by
        simpa only [NativeProcesses.retire, ite_eq_right same] using present)

inductive SocketAliasExecution (socket : SocketLifetime) :
    {first last : Processes} → {current following : NativeProcesses} → {ticks : List (ActorTick runtime)} →
    NativeExternalJournal process child native hostUid first current ticks last following → Type 1 where
  | nil (before : Processes) (callers : NativeProcesses) (aliases : NativeSocketAliasesCloseExec socket callers) :
      SocketAliasExecution socket (.nil before callers)
  | cons {before middle after : Processes} {callers next final : NativeProcesses}
      {tick : ActorTick runtime} {ticks : List (ActorTick runtime)}
      {actual : NativeExternalStep process child native hostUid before callers tick middle next}
      {rest : NativeExternalJournal process child native hostUid middle next ticks after final}
      (aliases : NativeSocketAliasesCloseExec socket callers) (tail : SocketAliasExecution socket rest) :
      SocketAliasExecution socket (.cons actual rest)

theorem native_socket_alias_execution
    (platform : NativeOFDOriginContract native) (fork : NativeCode.ForkReferences (runtime := runtime) native)
    (references : ReferenceContract runtime) (socket : SocketLifetime)
    {first last : Processes} {current following : NativeProcesses} {ticks : List (ActorTick runtime)}
    {recording : NativeExternalJournal process child native hostUid first current ticks last following}
    (classifications : NativeFlagClassifications socket.object recording)
    {start finish : Population} (history : ActorJournal runtime start ticks finish)
    (allocated : start.shared.descriptionAllocated socket.description = true)
    (initial : NativeSocketAliasesCloseExec socket current) : Nonempty (SocketAliasExecution socket recording) := by
  induction classifications generalizing start finish with
  | nil before callers => exact ⟨.nil before callers initial⟩
  | @cons before middle after callers next final tick ticks actual rest currentSource tail ih =>
    cases history with
    | cons following =>
      obtain ⟨derived⟩ := ih following (actor_step_description_allocated references tick.operation socket.description allocated)
        (native_row_socket_aliases platform fork actual socket allocated currentSource initial)
      exact ⟨.cons initial derived⟩

theorem native_descriptions_live_of_snapshot
    (references : SocketReferenceRuntime process child native hostUid)
    {before after : Processes} {callers next : NativeProcesses} {tick : ActorTick runtime}
    {row : NativeExternalStep process child native hostUid before callers tick after next}
    {first last : SocketReferenceSnapshot} (observed : references.observed row first last) :
    NativeDescriptionsLive callers tick.before.shared := by
  intro token table _active present fd handle found
  have nativeTable := (references.input observed).2.1
  exact references.input_lifetime observed (.native token fd) handle (by
    simp only [SocketReferenceSnapshot.at, nativeTable, present, Option.bind_some, found])

-- §FS-host-boundary.ownership: This seed and fold use the same selected
-- reference recording and pair birth. No original socket was allocated in
-- the earlier global state, and no alias conclusion is a platform premise.
theorem native_socket_alias_execution_after_pair {ipc : ObjectId → Prop}
    (platform : NativeOFDOriginContract native) (pairs : SocketPairContract native ipc)
    (fork : NativeCode.ForkReferences (runtime := runtime) native)
    (descriptions : NativeDescriptionContract native) (lifetimes : ReferenceContract runtime)
    (references : SocketReferenceRuntime process child native hostUid)
    {before after : Processes} {callers next : NativeProcesses} {ticks : List (ActorTick runtime)}
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    {first last : SocketReferenceSnapshot} (recording : SocketReferenceRecording references journal first last)
    {pair : Pair} (entry : PairBirthEntry process child native hostUid before after callers next ticks pair)
    (actual : ActualPairBirth journal entry)
    (classifications : NativeFlagClassifications pair.caller entry.cut.last)
    {start finish : Population} (history : ActorJournal runtime start ticks finish) :
    Nonempty (SocketAliasExecution ⟨pair.caller, entry.firstHandle.description⟩ entry.cut.last) := by
  obtain ⟨input, output, _prefix, _suffix, _at, observed, _suffixAt⟩ :=
    SocketReferenceRecording.selected_cut references recording ⟨entry.tick, entry.cut⟩ actual
  obtain ⟨allocation⟩ := pairs.created entry.call entry.first entry.second entry.operation entry.product
  have same := Option.some.inj (allocation.leftOutput.symm.trans entry.firstInput)
  have object : allocation.left.object = pair.caller :=
    (congrArg Handle.object same).trans entry.callerObject
  have description : allocation.left.description = entry.firstHandle.description := congrArg Handle.description same
  have initial : NativeSocketAliasesCloseExec ⟨pair.caller, entry.firstHandle.description⟩ entry.cut.nextNative := by
    simpa only [object, description] using
      pair_initializes_original_ofd_cloexec fork allocation (native_descriptions_live_of_snapshot references observed)
  have allocated := pair_birth_description_allocated descriptions entry .caller
  rw [entry.cut.shape] at history
  obtain ⟨middle, _prior, suffix⟩ := actor_journal_split entry.cut.leading _ history
  cases suffix with
  | cons following =>
    exact native_socket_alias_execution platform fork lifetimes _ classifications following allocated initial

theorem SocketAliasExecution.selected_before
    {before after : Processes} {callers next : NativeProcesses} {ticks : List (ActorTick runtime)}
    {recording : NativeExternalJournal process child native hostUid before callers ticks after next}
    {socket : SocketLifetime} (execution : SocketAliasExecution socket recording)
    {position : Nat} (selected : SelectedNativeCut process child native hostUid before after callers next ticks position)
    (same : selectNativeCut recording position = some selected) :
    NativeSocketAliasesCloseExec socket selected.cut.priorNative := by
  induction execution generalizing position with
  | nil => simp only [selectNativeCut] at same; cases same
  | @cons before middle after callers next final tick ticks actual rest aliases tail ih =>
    cases position with
    | zero =>
      have identity : selected = ⟨tick, ⟨[], ticks, rfl, rfl, before, middle, callers, next, .nil _ _, actual, rest⟩⟩ :=
        (Option.some.inj same).symm
      cases identity
      exact aliases
    | succ position =>
      let extend := fun (chosen : SelectedNativeCut process child native hostUid middle after next final ticks position) =>
        ({ tick := chosen.tick
           cut := { chosen.cut with
             leading := tick :: chosen.cut.leading
             count := by simp only [List.length_cons, chosen.cut.count]
             shape := by simp only [chosen.cut.shape, List.cons_append]
             first := .cons actual chosen.cut.first } } :
          SelectedNativeCut process child native hostUid before after callers final (tick :: ticks) (position + 1))
      change (selectNativeCut rest position).map extend = some selected at same
      cases earlier : selectNativeCut rest position with
      | none => simp only [earlier, Option.map_none] at same; cases same
      | some chosen =>
        have prior := ih chosen earlier
        simp only [earlier, Option.map_some] at same
        have identity := (Option.some.inj same).symm
        cases identity
        exact prior

end LeanCage.Host.PrivateStreams
