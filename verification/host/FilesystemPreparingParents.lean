import FilesystemPreparingObservations
import PublicationProofs.MkdirFrontier

namespace LeanCage.Host.Kernel
open Filesystem

structure ObservedCreationParent (kernel : Contract) (origin : FilesystemOrigin) (limit : Nat)
    (world : World) (uid : Nat) (request : Request) (family : Family) (scope : ObjectId) where
  directory : Directories.Opened
  operand : directory.fd = request.first
  observation : ObservedDirectory kernel origin limit world uid directory
  privateParent : family observation.handle.object = some scope
  component : Directories.component request.left = true
  operation : request.op = .mkdirAt ∨ (request.op = .openAt ∧ request.second = newFileFlags)
  mode : request.op = .mkdirAt → request.second = 448

namespace Lowered

-- §FS-host-boundary.ownership: This actual selected directory-loop mkdir
-- derives its checked parent from earlier real iterations and the SAME
-- completed child chain, not an assumed private traversal footprint.
theorem directories_mkdir_observed {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} (descriptors : DescriptorContract kernel)
    (actor : ActorId) (origin : OperationOrigin) (limit : Nat) {family : Family}
    (opens : PrivateDirectoryOpens kernel (fun index query reply before after =>
      origin index Reply (.filesystem query) reply before after ∧ index < limit) family)
    {uid : Nat} {root : UInt64} {paths : List Artifacts.ExportPath}
    {before : List (Request × Option Reply)} {request : Request}
    (source : Publication.DirectoriesMkdirFrontier uid root paths before request)
    {raw : List Program.Event} (chunks : PrimitiveFilesystem.Chunks (before.map Program.filesystemPrefixEvent) raw)
    {ordinal : Nat} {first after : World}
    (history : ActorHistoryWith runtime actor origin ordinal first raw after)
    (bounded : ordinal + raw.length ≤ limit) {information : Stat}
    (starting : ObservedDirectory kernel (fun ordinal query reply => origin ordinal Reply (.filesystem query) reply)
      ordinal first uid {fd := root, information}) {scope : ObjectId}
    (privateRoot : family starting.handle.object = some scope) :
    Nonempty (ObservedCreationParent kernel (fun ordinal query reply => origin ordinal Reply (.filesystem query) reply)
      (ordinal + raw.length) after uid request family scope) := by
  have logical : before.map Program.filesystemPrefixEvent =
      source.loop.completed.map Program.filesystemEvent ++ source.current.opening.map Program.filesystemEvent := by
    have loop : before.map Program.filesystemPrefixEvent =
        source.loop.completed.map Program.filesystemEvent ++ source.loop.inside.map Program.filesystemPrefixEvent := by
      simpa only [List.map_append, completed_filesystem_events] using
        congrArg (List.map Program.filesystemPrefixEvent) source.loop.trace
    have current : source.loop.inside.map Program.filesystemPrefixEvent =
        source.current.opening.map Program.filesystemEvent := by
      simpa only [completed_filesystem_events] using
        congrArg (List.map Program.filesystemPrefixEvent) source.current.trace
    exact loop.trans (congrArg (source.loop.completed.map Program.filesystemEvent ++ ·) current)
  rw [logical] at chunks
  obtain ⟨loopRaw, chainRaw, loopChunks, chainChunks, rawTrace⟩ := PrimitiveFilesystem.chunks_split _ _ chunks
  obtain ⟨middle, loopHistory, chainHistory⟩ := actor_with_split loopRaw chainRaw (rawTrace ▸ history)
  obtain ⟨loopEvents, loopReturned, loopTrace⟩ := PrimitiveFilesystem.chunks_filesystem_returns source.loop.prepared loopChunks
  have borrowed : BorrowPost kernel root starting.handle (fun _ => True)
      (forIn source.loop.earlier (none, ())
        (Publication.actionBody (fun path => Publication.under uid root path.components true (fun _ => pure (.ok ()))))).lower := by
    apply borrow_forIn
    intro path state
    unfold Publication.actionBody
    apply borrow_bind (publication_under_borrow descriptors root starting.handle _ _ _ _ _ (fun _ => .pure True.intro))
    intro result _
    cases result <;> exact .pure True.intro
  have kept := (history_borrow _ _ borrowed ⟨loopReturned, actor_recorded_filesystem (loopTrace ▸ loopHistory)⟩ starting.live).1
  let updated := starting.advance kept (show ordinal ≤ ordinal + loopRaw.length by omega)
  obtain ⟨directory, operand, observation, privateParent⟩ := preparing_chain_observed descriptors actor origin limit opens
    source.current.chain chainChunks chainHistory (by rw [rawTrace, List.length_append] at bounded; omega) updated privateRoot
  refine ⟨{
    directory
    operand := operand.trans (congrArg Request.first source.current.operation).symm
    observation := observation.advance observation.live (by rw [rawTrace, List.length_append]; omega)
    privateParent
    component := ?_
    operation := .inl (congrArg Request.op source.current.operation)
    mode := fun _ => congrArg Request.second source.current.operation }⟩
  rw [source.current.operation]
  exact SourceReadForms.valid_component_form source.current.name source.current.component

-- §FS-host-boundary.ownership: The export branch derives its real opened
-- root and every nested checked parent from the same syscall transcript.
-- The selected mkdir remains pending, including its failed/lost outcomes.
theorem exports_mkdir_observed {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} (descriptors : DescriptorContract kernel)
    (actor : ActorId) (origin : OperationOrigin) (limit : Nat) {family : Family}
    (opens : PrivateDirectoryOpens kernel (fun index query reply before after =>
      origin index Reply (.filesystem query) reply before after ∧ index < limit) family)
    {uid : Nat} {stage : UInt64} {input : Publication.Input}
    {before : List (Request × Option Reply)} {request : Request}
    (source : Publication.ExportsMkdirFrontier uid stage input before request)
    {raw : List Program.Event} (chunks : PrimitiveFilesystem.Chunks (before.map Program.filesystemPrefixEvent) raw)
    {ordinal : Nat} {first after : World}
    (history : ActorHistoryWith runtime actor origin ordinal first raw after)
    (bounded : ordinal + raw.length ≤ limit) {information : Stat}
    (starting : ObservedDirectory kernel (fun ordinal query reply => origin ordinal Reply (.filesystem query) reply)
      ordinal first uid {fd := stage, information}) {scope : ObjectId}
    (privateRoot : family starting.handle.object = some scope) :
    Nonempty (ObservedCreationParent kernel (fun ordinal query reply => origin ordinal Reply (.filesystem query) reply)
      (ordinal + raw.length) after uid request family scope) := by
  cases source with
  | root trace operation =>
    subst before
    cases chunks
    have live : after.handles stage = some starting.handle := by
      rw [actor_retaining_event_handles descriptors history (by intro event impossible; cases impossible)]
      exact starting.live
    refine ⟨{
      directory := {fd := stage, information}
      operand := (congrArg Request.first operation).symm
      observation := starting.advance live (by simp)
      privateParent := privateRoot
      component := ?_
      operation := .inl (congrArg Request.op operation)
      mode := fun _ => congrArg Request.second operation }⟩
    rw [operation]
    change Directories.component (ByteArray.mk #[101, 120, 112, 111, 114, 116]) = true
    simp [Directories.component, ByteArray.isEmpty, ByteArray.size, Array.contains_eq_mem]
  | nested made root opening opened inside current trace =>
    let make : Request := {op := .mkdirAt, first := stage, second := 448, left := "export".toUTF8}
    have logical : before.map Program.filesystemPrefixEvent =
        [(make, made)].map Program.filesystemEvent ++
          (opening.map Program.filesystemEvent ++ inside.map Program.filesystemPrefixEvent) := by
      simpa only [List.map_append, List.map_cons, List.map_nil, completed_filesystem_events,
        Program.filesystemPrefixEvent, Program.filesystemEvent, make, List.append_assoc] using
        congrArg (List.map Program.filesystemPrefixEvent) trace
    rw [logical] at chunks
    obtain ⟨madeRaw, followingRaw, madeChunks, remainingChunks, firstTrace⟩ := PrimitiveFilesystem.chunks_split _ _ chunks
    obtain ⟨beforeOpen, madeHistory, remainingHistory⟩ := actor_with_split madeRaw followingRaw (firstTrace ▸ history)
    have madeSource : Returns (Filesystem.Program.effect make) [(make, made)] made := .call _ _ _ _ _ (.pure _)
    obtain ⟨madeEvents, madeReturned, madeTrace⟩ := PrimitiveFilesystem.chunks_filesystem_returns madeSource madeChunks
    have borrowed : BorrowPost kernel stage starting.handle (fun _ => True) (Filesystem.Program.effect make).lower := by
      apply passive_call descriptors stage starting.handle (by simp [make, RetainsDescriptors])
      intro reply
      exact .pure True.intro
    have held := (history_borrow _ _ borrowed ⟨madeReturned, actor_recorded_filesystem (madeTrace ▸ madeHistory)⟩ starting.live).1
    obtain ⟨openingRaw, insideRaw, openingChunks, insideChunks, nextTrace⟩ := PrimitiveFilesystem.chunks_split _ _ remainingChunks
    obtain ⟨afterOpen, openingHistory, insideHistory⟩ := actor_with_split openingRaw insideRaw (nextTrace ▸ remainingHistory)
    obtain ⟨events, openingReturned, openingTrace⟩ := PrimitiveFilesystem.chunks_filesystem_returns opened openingChunks
    have openingBound : ordinal + madeRaw.length + events.length ≤ limit := by
      have count := congrArg List.length openingTrace
      simp only [List.length_map] at count
      rw [firstTrace, nextTrace, List.length_append, List.length_append] at bounded
      omega
    have boundedHistory := recorded_history_source_bound (actor_recorded_filesystem (openingTrace ▸ openingHistory)) limit openingBound
    obtain ⟨observed, privateChild⟩ := directory_open_private descriptors opens (ordinal + madeRaw.length) uid stage
      "export".toUTF8 starting.handle scope ⟨openingReturned, boundedHistory⟩ held privateRoot
      (by
        change Directories.component (ByteArray.mk #[101, 120, 112, 111, 114, 116]) = true
        simp [Directories.component, ByteArray.isEmpty, ByteArray.size, Array.contains_eq_mem])
      (by decide) (by decide)
    let checked := observed.mapOrigin (fun _ _ _ _ _ evidence => evidence.1)
    let updated : ObservedDirectory kernel (fun ordinal query reply => origin ordinal Reply (.filesystem query) reply)
        (ordinal + madeRaw.length + openingRaw.length) afterOpen uid root := checked.advance checked.live (by
      have count := congrArg List.length openingTrace
      simp only [List.length_map] at count
      omega)
    obtain ⟨parent⟩ := directories_mkdir_observed descriptors actor origin limit opens current insideChunks insideHistory
      (by rw [firstTrace, nextTrace, List.length_append, List.length_append] at bounded; omega) updated privateChild
    exact ⟨{parent with observation := parent.observation.advance parent.observation.live (by
      rw [firstTrace, nextTrace, List.length_append, List.length_append]
      omega)}⟩

end Lowered
end LeanCage.Host.Kernel
