import GatewayChannelAliases
import FilesystemNativeForkRows

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

-- §AR-host-boundary.primitives: Classify the raw operation that can duplicate
-- an existing OFD. This permits ordinary non-CLOEXEC duplication as well.
def DescriptorDuplication (operation : NativeOperation) (source target : UInt64) (closeExec : Bool) : Prop :=
  (∃ minimum, operation = .fcntl source 1030 minimum ∧ closeExec = true) ∨
  (∃ minimum, operation = .fcntl source 0 minimum ∧ closeExec = false) ∨
  ∃ flags, operation = .duplicate source target flags ∧ closeExec = (flags &&& 524288 != 0)

inductive DescriptorOperand : NativeOperation → UInt64 → Prop where
  | fcntl (fd command argument : UInt64) : DescriptorOperand (.fcntl fd command argument) fd
  | duplicate (source target flags : UInt64) : DescriptorOperand (.duplicate source target flags) source

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {native : NativePrimitive kernel} {tick : ActorTick runtime} {before after : NativeProcesses}

-- §AR-host-boundary.primitives: This is one kernel descriptor effect. No
-- source invocation, role, protected object or reader-safety predicate occurs.
inductive NativeDescriptorOrigin (ipc : ObjectId → Prop)
    (call : NativeCallAt native tick before after) (fd : UInt64) (handle : Handle) : Type where
  | retained (original : Handle) (input : call.beforeReferences.handles fd = some original)
      (object : handle.object = original.object) (description : handle.description = original.description)
      (flags : call.afterReferences.closeOnExec fd = call.beforeReferences.closeOnExec fd) :
      NativeDescriptorOrigin ipc call fd handle
  | duplicated (source : UInt64) (original : Handle) (closeExec : Bool)
      (input : call.beforeReferences.handles source = some original)
      (object : handle.object = original.object) (description : handle.description = original.description)
      (operation : DescriptorDuplication call.operation source fd closeExec)
      (flags : call.afterReferences.closeOnExec fd = closeExec) : NativeDescriptorOrigin ipc call fd handle
  | flag (argument : UInt64) (input : call.beforeReferences.handles fd = some handle)
      (operation : call.operation = .fcntl fd 2 argument)
      (flags : call.afterReferences.closeOnExec fd = (argument &&& 1 != 0)) :
      NativeDescriptorOrigin ipc call fd handle
  | fresh (allocated : tick.before.shared.allocated handle.object = false) :
      NativeDescriptorOrigin ipc call fd handle
  | nonIpc (kind : ¬ ipc handle.object) : NativeDescriptorOrigin ipc call fd handle

structure NativeDescriptorContract {kernel : Contract} (native : NativePrimitive kernel) (ipc : ObjectId → Prop) : Prop where
  output : ∀ {runtime : PrimitiveActorRuntime kernel} {tick : ActorTick runtime} {before after : NativeProcesses}
    (call : NativeCallAt native tick before after) fd handle,
    call.afterReferences.handles fd = some handle → Nonempty (NativeDescriptorOrigin ipc call fd handle)

-- §FS-host-boundary.ownership: The external-code boundary restricts each real
-- resolved private operand. It does not forbid unrelated descriptor changes.
def ExternalDescriptorProfile (call : NativeCallAt native tick before after) (object : ObjectId) : Prop :=
  ∀ fd handle, DescriptorOperand call.operation fd → call.beforeReferences.handles fd = some handle →
    handle.object ≠ object

theorem DescriptorDuplication.operand {operation source target closeExec}
    (actual : DescriptorDuplication operation source target closeExec) : DescriptorOperand operation source := by
  rcases actual with ⟨minimum, rfl, _⟩ | ⟨minimum, rfl, _⟩ | ⟨flags, rfl, _⟩
  · exact .fcntl ..
  · exact .fcntl ..
  · exact .duplicate ..

theorem DescriptorDuplication.cloexec {operation source target closeExec fd minimum}
    (actual : DescriptorDuplication operation source target closeExec)
    (code : operation = .fcntl fd 1030 minimum) : closeExec = true := by
  rcases actual with ⟨_, same, flag⟩ | ⟨_, same, _⟩ | ⟨_, same, _⟩
  · exact flag
  · rw [code] at same
    cases same
  · rw [code] at same
    cases same

def DescriptorNoAliasWrite (operation : NativeOperation) : Prop :=
  (∀ source target closeExec, ¬ DescriptorDuplication operation source target closeExec) ∧
  ∀ fd argument, operation ≠ .fcntl fd 2 argument

theorem status_fcntl_no_alias_write (fd command argument : UInt64)
    (status : command = 3 ∨ command = 4) : DescriptorNoAliasWrite (.fcntl fd command argument) := by
  rcases status with rfl | rfl <;>
    simp [DescriptorNoAliasWrite, DescriptorDuplication]

theorem receive_no_alias_write (fd extent flags : UInt64) :
    DescriptorNoAliasWrite (.receive fd extent flags) := by
  simp [DescriptorNoAliasWrite, DescriptorDuplication]

theorem send_no_alias_write (fd : UInt64) (bytes : ByteArray) (extent flags : UInt64) :
    DescriptorNoAliasWrite (.send fd bytes extent flags) := by
  simp [DescriptorNoAliasWrite, DescriptorDuplication]

theorem source_operation_preserves_aliases {ipc : ObjectId → Prop}
    (platform : NativeDescriptorContract native ipc) (call : NativeCallAt native tick before after)
    (object : ObjectId) (kind : ipc object) (live : tick.before.shared.allocated object = true)
    (operation : DescriptorNoAliasWrite call.operation)
    (initial : AliasesCloseExec object call.beforeReferences) : AliasesCloseExec object call.afterReferences := by
  intro fd handle found same
  obtain ⟨origin⟩ := platform.output call fd handle found
  cases origin with
  | retained original input identity description flags =>
    exact flags.trans (initial fd original input (identity.symm.trans same))
  | duplicated source original closeExec input identity description actual flags =>
    exact False.elim (operation.1 source fd closeExec actual)
  | flag argument input actual flags => exact False.elim (operation.2 fd argument actual)
  | fresh absent => rw [same, live] at absent; cases absent
  | nonIpc excluded => exact False.elim (excluded (same ▸ kind))

theorem source_cloexec_duplicate_preserves_aliases {ipc : ObjectId → Prop}
    (platform : NativeDescriptorContract native ipc) (call : NativeCallAt native tick before after)
    (object : ObjectId) (kind : ipc object) (live : tick.before.shared.allocated object = true)
    (source minimum : UInt64)
    (code : call.operation = .fcntl source 1030 minimum)
    (initial : AliasesCloseExec object call.beforeReferences) : AliasesCloseExec object call.afterReferences := by
  intro fd handle found same
  obtain ⟨origin⟩ := platform.output call fd handle found
  cases origin with
  | retained original input identity description flags =>
    exact flags.trans (initial fd original input (identity.symm.trans same))
  | duplicated source original closeExec input identity description operation flags =>
    exact flags.trans (operation.cloexec code)
  | flag argument input operation flags => rw [code] at operation; cases operation
  | fresh absent => rw [same, live] at absent; cases absent
  | nonIpc excluded => exact False.elim (excluded (same ▸ kind))

theorem external_operation_preserves_aliases {ipc : ObjectId → Prop}
    (platform : NativeDescriptorContract native ipc) (call : NativeCallAt native tick before after)
    (object : ObjectId) (kind : ipc object) (live : tick.before.shared.allocated object = true)
    (profile : ExternalDescriptorProfile call object)
    (initial : AliasesCloseExec object call.beforeReferences) : AliasesCloseExec object call.afterReferences := by
  intro fd handle found same
  obtain ⟨origin⟩ := platform.output call fd handle found
  cases origin with
  | retained original input identity description flags =>
    exact flags.trans (initial fd original input (identity.symm.trans same))
  | duplicated source original closeExec input identity description operation flags =>
    exact False.elim (profile source original operation.operand input (identity.symm.trans same))
  | flag argument input operation flags =>
    exact False.elim (profile fd handle (operation ▸ DescriptorOperand.fcntl fd 2 argument) input same)
  | fresh absent => rw [same, live] at absent; cases absent
  | nonIpc excluded => exact False.elim (excluded (same ▸ kind))

-- §AR-host-boundary.primitives: A real fresh pair supplies this classification
-- directly, including both new endpoints; it does not require a preexisting alias.
theorem pair_descriptor_origins {ipc : ObjectId → Prop}
    {call : NativeCallAt native tick before after} {first second : UInt64}
    (allocation : PairAllocation ipc call first second) (fd : UInt64) (handle : Handle)
    (found : call.afterReferences.handles fd = some handle) :
    Nonempty (NativeDescriptorOrigin ipc call fd handle) := by
  by_cases left : fd = first
  · subst fd
    have identity := Option.some.inj (allocation.leftOutput.symm.trans found)
    subst handle
    exact ⟨.fresh allocation.leftFresh⟩
  · by_cases right : fd = second
    · subst fd
      have identity := Option.some.inj (allocation.rightOutput.symm.trans found)
      subst handle
      exact ⟨.fresh allocation.rightFresh⟩
    · exact ⟨.retained handle ((allocation.otherOutputs fd left right).symm.trans found)
        rfl rfl (allocation.otherCloseExec fd left right)⟩

-- §FS-host-boundary.ownership: All active native process tables retain aliases,
-- including a fresh child's full fork table before any file actions or exec.
def NativeAliasesCloseExec (object : ObjectId) (processes : NativeProcesses) : Prop :=
  ∀ token references, processes.allocated token = true → processes.references token = some references →
    AliasesCloseExec object references

theorem native_call_preserves_all_aliases
    (fork : NativeCode.ForkReferences (runtime := runtime) native)
    (call : NativeCallAt native tick before after) (object : ObjectId)
    (initial : NativeAliasesCloseExec object before)
    (own : AliasesCloseExec object call.afterReferences) : NativeAliasesCloseExec object after := by
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

theorem pair_initializes_all_native_aliases {ipc : ObjectId → Prop}
    (fork : NativeCode.ForkReferences (runtime := runtime) native)
    {call : NativeCallAt native tick before after} {first second : UInt64}
    (allocation : PairAllocation ipc call first second)
    (live : NativeReferencesLive before tick.before.shared) :
    NativeAliasesCloseExec allocation.left.object after := by
  apply native_call_preserves_all_aliases fork call allocation.left.object
  · intro token references active present fd handle found same
    exact False.elim (fresh_native_reference_absent live allocation.leftFresh present found same)
  · exact pair_caller_aliases_close_exec allocation live

end LeanCage.Host.PrivateStreams
