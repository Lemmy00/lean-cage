import GatewayChannelDescriptorEffects

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

-- Empty final-close discards are harmless. A prior successful EOF can supply
-- their emptiness; no live endpoint or complete teardown is inferred from it.
def preservesReceivedBytes (receiver : Side) : Action → Prop
  | .discard actual bytes => actual ≠ receiver ∨ bytes = []
  | _ => True

theorem step_balance_allow_empty {before after : State} {action : Action} (receiver : Side)
    (step : Step (some before) action (some after)) (retained : preservesReceivedBytes receiver action) :
    before.incoming receiver ++ written receiver action =
      received receiver action ++ after.incoming receiver := by
  cases step with
  | write state sender bytes writable =>
    cases receiver <;> cases sender <;> simp [written, received, State.enqueue, State.setIncoming, Side.peer]
  | read state actual bytes rest contents =>
    cases receiver <;> cases actual <;> simp_all [written, received, State.setIncoming]
  | discard state actual bytes rest contents =>
    rcases retained with different | empty
    · cases receiver <;> cases actual <;> simp_all [written, received, State.setIncoming]
    · subst bytes
      cases receiver <;> cases actual <;> simp_all [written, received, State.setIncoming]
  | closeWrite state sender => simp [written, received, State.closeWrite]
  | eof state actual empty closed => simp [written, received]
  | quiet state => simp [written, received]

theorem run_balance_allow_empty {before after : State} {actions : List Action} (receiver : Side)
    (run : Run before actions after)
    (retained : ∀ action ∈ actions, preservesReceivedBytes receiver action) :
    before.incoming receiver ++ actions.flatMap (written receiver) =
      actions.flatMap (received receiver) ++ after.incoming receiver := by
  induction run with
  | nil => simp
  | cons head tail ih =>
    have first := step_balance_allow_empty receiver head (retained _ (by simp))
    have rest := ih (fun action member => retained action (by simp [member]))
    simp only [List.flatMap_cons]
    rw [← List.append_assoc, first, List.append_assoc, rest, List.append_assoc]

def incomingOrEmpty (state : Option State) (receiver : Side) : Bytes :=
  match state with | none => [] | some state => state.incoming receiver

theorem option_step_balance_allow_empty {before after : Option State} {action : Action} (receiver : Side)
    (step : Step before action after) (retained : preservesReceivedBytes receiver action) :
    incomingOrEmpty before receiver ++ written receiver action =
      received receiver action ++ incomingOrEmpty after receiver := by
  cases before with
  | none => cases step <;> simp [incomingOrEmpty, written, received, State.empty]
  | some before =>
    obtain ⟨after, rfl⟩ := step_live step
    exact step_balance_allow_empty receiver step retained

-- §FS-host-boundary.caller: This derives the common byte prefix from the
-- actual empty-before-birth history, also retaining empty final discards.
theorem physical_received_prefix_allow_empty {before after : Option State} {actions : List Action}
    (actual : Steps before actions after) (receiver : Side)
    (retained : ∀ action ∈ actions, preservesReceivedBytes receiver action) :
    incomingOrEmpty before receiver ++ actions.flatMap (written receiver) =
      actions.flatMap (received receiver) ++ incomingOrEmpty after receiver := by
  induction actual with
  | nil => simp
  | @cons before middle after action actions head tail ih =>
    have first := option_step_balance_allow_empty receiver head (retained action (by simp))
    have rest := ih (fun action member => retained action (by simp [member]))
    simp only [List.flatMap_cons]
    rw [← List.append_assoc, first, List.append_assoc, rest, List.append_assoc]

structure ActorEndpointRead {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (tick : ActorTick runtime) (object : ObjectId) where
  actor : ActorId
  engine : EngineState
  present : tick.before.actors actor = some engine
  request : Request
  next : Reply → Program UInt32
  head : engine.current = .call (.filesystem request) next
  reading : request.op = .read
  handle : Handle
  input : engine.references request.first = some handle
  endpoint : handle.object = object

-- §AR-host-boundary.primitives: A discard is explained by its one actual
-- kernel cause at this stored row. The last-reference branch samples all
-- current raw/retiring/support handles; it supplies no inferred resource drain.
inductive DiscardOrigin {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses} {tick : ActorTick runtime}
    (row : NativeExternalStep process child native hostUid before callers tick after next)
    (support : NativeToken → UInt64 → Option Handle) (object : ObjectId) : Type 1 where
  | nativeRead (call : NativeCallAt native tick callers next) (embedded : embeddedNative row = some call)
      (read : NativeEndpointRead call object) : DiscardOrigin row support object
  | actorRead (read : ActorEndpointRead tick object) : DiscardOrigin row support object
  | shutdown (call : NativeCallAt native tick callers next) (embedded : embeddedNative row = some call)
      (shut : NativeEndpointShutdown call object) : DiscardOrigin row support object
  | lastReference (released : NoEndpointReference tick.after next support object) : DiscardOrigin row support object

-- These exclusions concern individual actual operands/source heads. Their
-- producer is the verified C/pre-exec/engine source family plus Profile 1;
-- no whole-callback frame or exclusive-reader label appears in the result.
theorem retained_caller_excludes_discard {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses} {tick : ActorTick runtime}
    (row : NativeExternalStep process child native hostUid before callers tick after next)
    (support : NativeToken → UInt64 → Option Handle) (object : ObjectId)
    (process : NativeToken) (table : NativeReferences) (descriptor : UInt64) (handle : Handle)
    (current : next.references process = some table) (held : table.handles descriptor = some handle)
    (endpoint : handle.object = object)
    (nativeRead : ∀ call, embeddedNative row = some call → ¬ NativeEndpointRead call object)
    (actorRead : ¬ Nonempty (ActorEndpointRead tick object))
    (shutdown : ∀ call, embeddedNative row = some call → ¬ NativeEndpointShutdown call object) :
    ¬ Nonempty (DiscardOrigin row support object) := by
  intro actual
  obtain ⟨cause⟩ := actual
  cases cause with
  | nativeRead call same read => exact nativeRead call same read
  | actorRead read => exact actorRead ⟨read⟩
  | shutdown call same shut => exact shutdown call same shut
  | lastReference released =>
    exact retained_native_reference_excludes_last_drop tick.after next support process table descriptor handle current held
      (by simpa only [endpoint] using released)

end LeanCage.Host.PrivateStreams
