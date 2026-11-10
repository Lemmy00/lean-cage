import ControllerChildEffects
import FilesystemRecordedBackend

namespace LeanCage.Application.ControllerFilesystem
open LeanCageM3
open LeanCage.Host LeanCage.Host.Filesystem LeanCage.Host.Kernel

-- §AR-host-boundary.coverage: These are the actual source roles of a child born
-- by the expanded host engine, retaining the original source and exact raw chunks.
theorem actual_primitive_child_program {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {all : List (ActorTick runtime)} {position : Nat}
    {before : Processes} {token : ProcessToken} (source : PrimitiveBackendSource process all position before token) :
    Nonempty (ChildProgramSource source.source.source.caller.context.bundle source.arguments) :=
  actual_child_program source.source.source.caller.role

inductive PrimitiveControllerCallSource {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {primitive : ChildPrimitive kernel} (sdk : ControllerRuntimeContract)
    {before after : Processes} {tick : ActorTick runtime}
    (call : ChildCallAt primitive tick before after) (path : String) : Type 1 where
  | metadata (request : Metadata.Request) (prior : List (Metadata.Request × Option Metadata.Reply))
      (reply : Option Metadata.Reply)
      (active : Prefix (Metadata.bounded path 65536) (prior ++ [(request, reply)]))
      (operation : call.operation = .adapted (metadataRequest request))
      (sameReply : call.reply = reply) : PrimitiveControllerCallSource sdk call path
  | runtime (actual : sdk.observed call.token (call.beforeReferences.project tick.before.shared)
      call.operation call.reply (call.afterReferences.project tick.after.shared)) :
      PrimitiveControllerCallSource sdk call path

theorem primitive_controller_authority {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {primitive : ChildPrimitive kernel} (sdk : ControllerRuntimeContract)
    {before after : Processes} {tick : ActorTick runtime}
    (call : ChildCallAt primitive tick before after) (path : String)
    (source : PrimitiveControllerCallSource sdk call path) : ChildAuthoritySafe call.operation := by
  cases source with
  | metadata request prior reply active operation sameReply =>
    rw [operation]
    exact metadata_authority_safe request
  | runtime actual => exact sdk.authority _ _ _ _ _ actual

def PrimitiveProgramCall {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {primitive : ChildPrimitive kernel}
    (sdk : ControllerRuntimeContract) (vmm : VmmRuntimeContract)
    {all : List (ActorTick runtime)} {position : Nat} {before after : Processes} {tick : ActorTick runtime}
    (call : ChildCallAt primitive tick before after)
    (source : PrimitiveBackendSource process all position before call.token) : Prop :=
  match source.source.source.caller.role with
  | .validator _ context _ _ _ _ _ =>
    Nonempty (PrimitiveControllerCallSource sdk call (context.allocated.directory.path ++ "/policy.json"))
  | .vm _ _ _ _ _ _ _ _ => vmm.observed source.arguments call.token
    (call.beforeReferences.project tick.before.shared) call.operation call.reply
    (call.afterReferences.project tick.after.shared)

theorem primitive_program_authority {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {primitive : ChildPrimitive kernel}
    (sdk : ControllerRuntimeContract) (vmm : VmmRuntimeContract)
    {all : List (ActorTick runtime)} {position : Nat} {before after : Processes} {tick : ActorTick runtime}
    (call : ChildCallAt primitive tick before after)
    (source : PrimitiveBackendSource process all position before call.token)
    (actual : PrimitiveProgramCall sdk vmm call source) : ChildAuthoritySafe call.operation := by
  unfold PrimitiveProgramCall at actual
  cases role : source.source.source.caller.role with
  | validator raw context outside inside active trace argumentSource =>
    simp only [role] at actual
    obtain ⟨observed⟩ := actual
    exact primitive_controller_authority sdk call _ observed
  | vm request duration context outside inside active trace argumentSource =>
    simp only [role] at actual
    have observed : vmm.observed (VirtualMachine.arguments source.source.source.caller.context.bundle
        context.allocated.directory.path) call.token (call.beforeReferences.project tick.before.shared)
        call.operation call.reply (call.afterReferences.project tick.after.shared) := by
      simpa only [argumentSource] using actual
    exact vmm.authority _ _ _ _ _ _ _ observed

private def source_tick {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {before after : Processes} {first last : NativeProcesses} {tick : ActorTick runtime}
    (_source : NativeExternalStep process child native hostUid before first tick after last) : ActorTick runtime := tick

def RecordedProgramCall {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} (sdk : ControllerRuntimeContract) (vmm : VmmRuntimeContract)
    (all : List (ActorTick runtime)) (position : Nat)
    {before after : Processes} {first last : NativeProcesses} {tick : ActorTick runtime} :
    NativeExternalStep process child native hostUid before first tick after last → Prop
  | .child _ call => ∃ source : PrimitiveBackendSource process all position before call.token,
    PrimitiveProgramCall sdk vmm call source
  | _ => True

-- §AR-host-boundary.primitives: Only individual interpreted child operations
-- enter this journal. Controller metadata prefixes and fixed-argument VMM calls
-- retain the SAME embedded child call, rather than an assumed whole footprint.
def RecordedPrograms {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} (sdk : ControllerRuntimeContract) (vmm : VmmRuntimeContract) (all : List (ActorTick runtime))
    {before after : Processes} {first last : NativeProcesses} {ticks : List (ActorTick runtime)} :
    NativeExternalJournal process child native hostUid before first ticks after last → List (ActorTick runtime) → Prop
  | .nil _ _, _ => True
  | .cons current rest, processed => RecordedProgramCall sdk vmm all processed.length current ∧
    RecordedPrograms sdk vmm all rest (processed ++ [source_tick current])

theorem recorded_programs_authority {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} (sdk : ControllerRuntimeContract) (vmm : VmmRuntimeContract) (all : List (ActorTick runtime))
    {before after : Processes} {first last : NativeProcesses} {ticks processed : List (ActorTick runtime)}
    (recording : NativeExternalJournal process child native hostUid before first ticks after last)
    (actual : RecordedPrograms sdk vmm all recording processed) : RecordedChildAuthority recording := by
  induction recording generalizing processed with
  | nil => trivial
  | cons current rest ih =>
    refine ⟨?_, ih actual.2⟩
    cases current with
    | application | launch | ordinary | native | retiring => trivial
    | child recorded call =>
      obtain ⟨source, observed⟩ := actual.1
      exact primitive_program_authority sdk vmm call source observed

def RecordedProgramAdapter {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} (sdk : ControllerRuntimeContract) (vmm : VmmRuntimeContract)
    (all : List (ActorTick runtime)) (position : Nat)
    {before after : Processes} {first last : NativeProcesses} {tick : ActorTick runtime} :
    NativeExternalStep process child native hostUid before first tick after last → Prop
  | .child _ call => ∀ source : PrimitiveBackendSource process all position before call.token,
    PrimitiveProgramCall sdk vmm call source
  | _ => True

-- §AR-host-boundary.primitives: Individual runtime/metadata/VMM observations are
-- attached to the actual stored calls; the source/birth receipts are constructed
-- by the application from that same history, rather than supplied as a platform claim.
def RecordedProgramAdapters {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} (sdk : ControllerRuntimeContract) (vmm : VmmRuntimeContract) (all : List (ActorTick runtime))
    {before after : Processes} {first last : NativeProcesses} {ticks : List (ActorTick runtime)} :
    NativeExternalJournal process child native hostUid before first ticks after last → List (ActorTick runtime) → Prop
  | .nil _ _, _ => True
  | .cons current rest, processed => RecordedProgramAdapter sdk vmm all processed.length current ∧
    RecordedProgramAdapters sdk vmm all rest (processed ++ [source_tick current])

theorem actual_recorded_programs {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} (sdk : ControllerRuntimeContract) (vmm : VmmRuntimeContract)
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {after : Processes} {first last : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid Processes.empty first all after last)
    (adapters : RecordedProgramAdapters sdk vmm all recording []) : RecordedPrograms sdk vmm all recording [] := by
  have sources := actual_recorded_child_sources journal recording
  have follow : ∀ {before after : Processes} {first last : NativeProcesses} {ticks processed : List (ActorTick runtime)}
      (remaining : NativeExternalJournal process child native hostUid before first ticks after last),
      RecordedChildSources all remaining processed → RecordedProgramAdapters sdk vmm all remaining processed →
      RecordedPrograms sdk vmm all remaining processed := by
    intro before after first last ticks processed remaining
    induction remaining generalizing processed with
    | nil => intro source actual; trivial
    | cons current rest ih =>
      intro source actual
      refine ⟨?_, ih source.2 actual.2⟩
      cases current with
      | application | launch | ordinary | native | retiring => trivial
      | child recorded call =>
        obtain ⟨origin⟩ := source.1
        exact ⟨origin, actual.1 origin⟩
  exact follow recording sources adapters

theorem actual_recorded_program_authority {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} (sdk : ControllerRuntimeContract) (vmm : VmmRuntimeContract)
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {after : Processes} {first last : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid Processes.empty first all after last)
    (adapters : RecordedProgramAdapters sdk vmm all recording []) : NativeAuthorityJournal recording :=
  recorded_native_authority_journal journal recording
    (recorded_programs_authority sdk vmm all recording (actual_recorded_programs sdk vmm journal recording adapters))

end LeanCage.Application.ControllerFilesystem
