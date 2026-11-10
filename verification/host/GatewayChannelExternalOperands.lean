import GatewayChannelDescriptorEffects
import GatewayChannelAliasJournal

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

-- §FS-host-boundary.ownership: Profile 1 constrains the actual resolved
-- operand of one external-code operation. An exec is kept as an image event,
-- rather than declaring a complete callback to preserve descriptors.
inductive PrivateDescriptorOperand : NativeOperation → UInt64 → Prop where
  | read {operation descriptor} (input : NativeReadOperand operation descriptor) :
      PrivateDescriptorOperand operation descriptor
  | shutdown (descriptor how : UInt64) : PrivateDescriptorOperand (.shutdown descriptor how) descriptor
  | fcntl (descriptor command argument : UInt64) : PrivateDescriptorOperand (.fcntl descriptor command argument) descriptor
  | duplicateSource (source target flags : UInt64) : PrivateDescriptorOperand (.duplicate source target flags) source
  | duplicateTarget (source target flags : UInt64) : PrivateDescriptorOperand (.duplicate source target flags) target
  | send (descriptor extent flags : UInt64) (bytes : ByteArray) :
      PrivateDescriptorOperand (.send descriptor bytes extent flags) descriptor
  | write (request : Request) (writing : request.op = .write) :
      PrivateDescriptorOperand (.vfs (.adapted request)) request.first
  | close (request : Request) (closing : request.op = .close) :
      PrivateDescriptorOperand (.vfs (.adapted request)) request.first
  | cursor (request : Request) (closing : request.op = .dirClose) :
      PrivateDescriptorOperand (.vfs (.adapted request)) request.second

theorem shutdown_private_operand {operation descriptor}
    (actual : NativeReadShutdown operation descriptor) : PrivateDescriptorOperand operation descriptor := by
  cases actual
  exact .shutdown ..

theorem alias_private_operand {operation descriptor}
    (actual : DescriptorOperand operation descriptor) : PrivateDescriptorOperand operation descriptor := by
  cases actual with
  | fcntl fd command argument => exact .fcntl ..
  | duplicate source target flags => exact .duplicateSource ..

theorem replacement_private_operand {operation product descriptor}
    (actual : NativeReferenceReplacement operation product descriptor) :
    PrivateDescriptorOperand operation descriptor ∨ ∃ image, product = .executed image := by
  cases actual with
  | close request product closing => exact .inl (.close request closing)
  | cursor request product closing => exact .inl (.cursor request closing)
  | duplicate source target flags product => exact .inl (.duplicateTarget ..)
  | image arguments image descriptor => exact .inr ⟨image, rfl⟩

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {native : NativePrimitive kernel} {tick : ActorTick runtime} {before after : NativeProcesses}

def ExternalEndpointOperands (call : NativeCallAt native tick before after) (object : ObjectId) : Prop :=
  ∀ descriptor handle, PrivateDescriptorOperand call.operation descriptor →
    call.beforeReferences.handles descriptor = some handle → handle.object ≠ object

theorem external_read_operands (call : NativeCallAt native tick before after) (object : ObjectId)
    (profile : ExternalEndpointOperands call object) : ExternalReadAuthority call object := by
  intro descriptor handle operation input
  cases operation with
  | inl read => exact profile descriptor handle (.read read) input
  | inr shutdown => exact profile descriptor handle (shutdown_private_operand shutdown) input

theorem external_alias_operands (call : NativeCallAt native tick before after) (object : ObjectId)
    (profile : ExternalEndpointOperands call object) : ExternalDescriptorProfile call object := by
  intro descriptor handle operation input
  exact profile descriptor handle (alias_private_operand operation) input

-- An actual private input handle rules out the concrete replacement targets.
-- Successful image replacement stays separate and is ruled out only by the
-- same observed source-incarnation interval below.
theorem external_reference_operand (call : NativeCallAt native tick before after)
    (descriptor : UInt64) (handle : Handle) (input : call.beforeReferences.handles descriptor = some handle)
    (profile : ExternalEndpointOperands call handle.object)
    (noExec : ∀ image, call.product ≠ .executed image) : RetainsDescriptor call descriptor := by
  intro replacement
  rcases replacement_private_operand replacement with operand | ⟨image, replaced⟩
  · exact profile descriptor handle operand input rfl
  · exact noExec image replaced

variable {process : ProcessContract runtime} {child : ChildPrimitive kernel} {hostUid : Nat}
  {prior final : Processes} {callers next : NativeProcesses} {ticks : List (ActorTick runtime)}

theorem current_call_not_executed {before after : Processes} {callers next : NativeProcesses}
    {tick : ActorTick runtime}
    (row : NativeExternalStep process child native hostUid before callers tick after next)
    (query : NativeToken) (zero : nativeExecIncrement row query = 0)
    (call : NativeCallAt native tick callers next)
    (embedded : embeddedNative row = some call) (source : call.token = query) :
    ∀ image, call.product ≠ .executed image := by
  cases row with
  | native recorded actual retirement others =>
    have identity := Option.some.inj embedded
    subst actual
    intro image product
    simp only [nativeExecIncrement, product, source, ↓reduceIte] at zero
    contradiction
  | application | ordinary | child | launch | retiring => cases embedded

-- §AR-host-boundary.primitives: The exact embedded call, rather than another
-- witness for an equal tick, supplies this image-replacement observation.
theorem selected_call_not_executed
    (journal : NativeExternalJournal process child native hostUid prior callers ticks final next)
    (query first last : Nat)
    (incarnation : nativeExecCountBefore journal first query = nativeExecCountBefore journal last query)
    {position : Nat}
    (point : SelectedNativeCut process child native hostUid prior final callers next ticks position)
    (selected : selectNativeCut journal position = some point)
    (lower : first ≤ position) (upper : position < last)
    (call : NativeCallAt native point.tick point.cut.priorNative point.cut.nextNative)
    (embedded : embeddedNative point.cut.current = some call) (source : call.token = query) :
    ∀ image, call.product ≠ .executed image := by
  have zero := selected_exec_excluded_by_incarnation journal query first last incarnation point selected lower upper
  exact current_call_not_executed point.cut.current query zero call embedded source

-- All three conclusions concern this SAME current call. They impose neither
-- queue contents nor a reader role; pending/lost SDK replies remain possible.
theorem actual_external_endpoint_operands
    (journal : NativeExternalJournal process child native hostUid prior callers ticks final next)
    (query first last : Nat)
    (incarnation : nativeExecCountBefore journal first query = nativeExecCountBefore journal last query)
    {position : Nat}
    (point : SelectedNativeCut process child native hostUid prior final callers next ticks position)
    (selected : selectNativeCut journal position = some point)
    (lower : first ≤ position) (upper : position < last)
    (call : NativeCallAt native point.tick point.cut.priorNative point.cut.nextNative)
    (embedded : embeddedNative point.cut.current = some call) (source : call.token = query)
    (descriptor : UInt64) (handle : Handle) (input : call.beforeReferences.handles descriptor = some handle)
    (profile : ExternalEndpointOperands call handle.object) :
    ¬ NativeEndpointRead call handle.object ∧ ¬ NativeEndpointShutdown call handle.object ∧
      RetainsDescriptor call descriptor ∧ Nonempty (NativeFlagAuthority call handle.object) := by
  obtain ⟨noRead, noShutdown⟩ := external_no_endpoint_read call handle.object (external_read_operands call handle.object profile)
  exact ⟨noRead, noShutdown, external_reference_operand call descriptor handle input profile
    (selected_call_not_executed journal query first last incarnation point selected lower upper call embedded source),
    ⟨.operands (external_alias_operands call handle.object profile)⟩⟩

end LeanCage.Host.PrivateStreams
