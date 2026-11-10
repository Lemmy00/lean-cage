import FilesystemCleanupReplyOwnership

namespace LeanCage.Host.Kernel
open Filesystem

def cleanupBeforeRoot (parent : Directories.Parent) (stage : Directories.Fresh)
    (input : Publication.Input) : Filesystem.Program Unit :=
  (Directories.openAt parent.uid stage.directory.fd "export".toUTF8).bind (fun opened =>
    (match opened with
      | .error _ => Filesystem.Program.pure ()
      | .ok root => Publication.cleanupExport parent.uid root input).bind (fun _ =>
      (Publication.cleanupStageFiles stage Publication.cleanupNames).bind (fun _ =>
        (Filesystem.Program.effect {
          op := .unlinkAt, first := stage.directory.fd, second := 512, left := "export".toUTF8 }).bind (fun _ =>
          (Filesystem.Program.effect {op := .close, first := stage.directory.fd}).bind (fun _ => .pure ())))))

def Lowered.FinalCleanupFrontier.replies {parent : Directories.Parent} {stage : Directories.Fresh}
    {input : Publication.Input} {before : List (Request × Option Reply)} {request : Request}
    (source : Lowered.FinalCleanupFrontier parent stage input before request) : List (Request × Reply) :=
  source.opening ++ source.earlier ++ source.files ++ [
    ({op := .unlinkAt, first := stage.directory.fd, second := 512, left := "export".toUTF8}, source.exportReply),
    ({op := .close, first := stage.directory.fd}, source.closeReply)]

-- §FS-host-boundary.ownership: This source prefix is obtained from the
-- selected final call's real frontier, rather than a second cleanup run.
theorem Lowered.FinalCleanupFrontier.returned {parent : Directories.Parent} {stage : Directories.Fresh}
    {input : Publication.Input} {before : List (Request × Option Reply)} {request : Request}
    (source : Lowered.FinalCleanupFrontier parent stage input before request) :
    Returns (cleanupBeforeRoot parent stage input) source.replies () := by
  cases source with
  | mk opened opening openingSource earlier prior files completed exportReply closeReply trace operation =>
    unfold cleanupBeforeRoot
    have lastSource : Returns
        ((Publication.cleanupStageFiles stage Publication.cleanupNames).bind (fun _ =>
          (Filesystem.Program.effect {
            op := .unlinkAt, first := stage.directory.fd, second := 512, left := "export".toUTF8 }).bind (fun _ =>
            (Filesystem.Program.effect {op := .close, first := stage.directory.fd}).bind (fun _ => .pure ()))))
        (files ++ [
          ({op := .unlinkAt, first := stage.directory.fd, second := 512, left := "export".toUTF8}, exportReply),
          ({op := .close, first := stage.directory.fd}, closeReply)]) () :=
      Snapshot.returns_bind_join completed (.call _ _ exportReply _ _
        (.call _ _ closeReply _ _ (.pure ())))
    have selected : Returns
        (match opened with
          | .error _ => Filesystem.Program.pure ()
          | .ok root => Publication.cleanupExport parent.uid root input)
        earlier () := by
      cases opened with
      | error error =>
        have empty : earlier = [] := prior
        rw [empty]
        exact .pure _
      | ok root => exact prior
    simpa only [replies, List.append_assoc] using Snapshot.returns_bind_join openingSource
      (Snapshot.returns_bind_join selected lastSource)

theorem static_cleanup_components : ∀ name ∈ Publication.cleanupNames,
    Directories.component name.toUTF8 = true := by
  intro name member
  simp only [Publication.cleanupNames, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Directories.component (ByteArray.mk #[112, 111, 108, 105, 99, 121, 46, 106, 115, 111, 110]) = true
    simp [Directories.component, ByteArray.isEmpty, ByteArray.size, Array.contains_eq_mem]
  · change Directories.component (ByteArray.mk #[98, 111, 111, 116, 46, 108, 111, 103]) = true
    simp [Directories.component, ByteArray.isEmpty, ByteArray.size, Array.contains_eq_mem]
  · change Directories.component (ByteArray.mk #[118, 109, 45, 114, 101, 112, 111, 114, 116, 46, 106, 115, 111, 110]) = true
    simp [Directories.component, ByteArray.isEmpty, ByteArray.size, Array.contains_eq_mem]
  · change Directories.component (ByteArray.mk #[115, 116, 100, 111, 117, 116]) = true
    simp [Directories.component, ByteArray.isEmpty, ByteArray.size, Array.contains_eq_mem]
  · change Directories.component (ByteArray.mk #[115, 116, 100, 101, 114, 114]) = true
    simp [Directories.component, ByteArray.isEmpty, ByteArray.size, Array.contains_eq_mem]
  · change Directories.component (ByteArray.mk #[115, 116, 111, 114, 101, 100, 45, 114, 101, 112, 111, 114, 116, 46, 106, 115, 111, 110]) = true
    simp [Directories.component, ByteArray.isEmpty, ByteArray.size, Array.contains_eq_mem]
  · change Directories.component (ByteArray.mk #[101, 120, 112, 111, 114, 116, 46, 109, 97, 110, 105, 102, 101, 115, 116]) = true
    simp [Directories.component, ByteArray.isEmpty, ByteArray.size, Array.contains_eq_mem]
  · change Directories.component (ByteArray.mk #[114, 101, 115, 117, 108, 116, 46, 106, 115, 111, 110]) = true
    simp [Directories.component, ByteArray.isEmpty, ByteArray.size, Array.contains_eq_mem]
  · change Directories.component (ByteArray.mk #[112, 117, 98, 108, 105, 99, 97, 116, 105, 111, 110, 46, 119, 105, 114, 101]) = true
    simp [Directories.component, ByteArray.isEmpty, ByteArray.size, Array.contains_eq_mem]

private theorem stage_files_profile (stage : Directories.Fresh) :
    RequestProgram (fun query => query.op = .unlinkAt →
      query.first = stage.directory.fd ∧ Directories.component query.left = true)
      (Publication.cleanupStageFiles stage Publication.cleanupNames).lower := by
  apply lower_unlink_profile
  unfold Publication.cleanupStageFiles
  apply request_bind
  · apply request_forIn
    intro name member state
    apply RequestProgram.call ?_
    · intro ignored
      exact .pure _
    · intro unlink
      exact ⟨rfl, static_cleanup_components name member⟩
  · intro ignored
    exact .pure _

private theorem export_component : Directories.component "export".toUTF8 = true := by
  change Directories.component (ByteArray.mk #[101, 120, 112, 111, 114, 116]) = true
  simp [Directories.component, ByteArray.isEmpty, ByteArray.size, Array.contains_eq_mem]

private theorem close_no_unlink (fd : UInt64) :
    RequestProgram (fun query => query.op ≠ .unlinkAt) (Filesystem.Program.effect {op := .close, first := fd}).lower := by
  exact .call (by intro impossible; cases impossible) (fun _ => .pure _)

-- §FS-host-boundary.ownership: This is the actual source prefix before the
-- single parent-relative root unlink. Every earlier raw removal is inside
-- the retained stage; no namespace frame for the whole helper is assumed.
theorem actual_cleanup_before_root_replies {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} (descriptors : DescriptorContract kernel)
    (actor : ActorId) (origin : OperationOrigin) (limit : Nat) {family : Family}
    (opens : PrivateDirectoryOpens kernel (fun index request reply before after =>
      origin index Reply (.filesystem request) reply before after ∧ index < limit) family)
    {parent : Directories.Parent} {stage : Directories.Fresh} {input : Publication.Input}
    {ordinal : Nat} {before after : World} {events : List (Request × Reply)}
    (run : RecordedRun kernel (fun index request reply => origin index Reply (.filesystem request) reply)
      ordinal (cleanupBeforeRoot parent stage input).lower before events after ())
    (bounded : ordinal + events.length ≤ limit) {rootHandle : Handle} {scope : ObjectId}
    (live : before.handles stage.directory.fd = some rootHandle) (privateRoot : family rootHandle.object = some scope) :
    PrivateUnlinkReplies (kernel := kernel) origin family scope ordinal events := by
  unfold cleanupBeforeRoot at run
  obtain ⟨opening, result, rest, middle, trace, openedRun, following⟩ := Lowered.recorded_run_bind_split _ _ run
  obtain ⟨stillLive, fresh⟩ := Lowered.history_borrow _ _
    (Lowered.directoryOpen_borrow descriptors stage.directory.fd rootHandle parent.uid stage.directory.fd "export".toUTF8)
    openedRun live
  have openingNoUnlink : PrivateUnlinkReplies (kernel := kernel) origin family scope ordinal opening := by
    apply no_unlink_replies
    have allowed := requests_returned (lower_nondestructive
      (request_weaken (read_only_namespace_passive (Retrieval.openAt_readOnly parent.uid stage.directory.fd "export".toUTF8))
        (fun _ => namespace_passive_not_destructive))) openedRun.1
    intro query member unlink
    exact allowed query member (.inl unlink)
  obtain ⟨exporting, ignored, footer, beforeFiles, restTrace, exported, footerRun⟩ :=
    Lowered.recorded_run_bind_split _ _ following
  have exportedProperties : PrivateUnlinkReplies (kernel := kernel) origin family scope (ordinal + opening.length) exporting ∧
      beforeFiles.handles stage.directory.fd = some rootHandle := by
    cases result with
    | error error =>
      have shape := Snapshot.returns_pure_eq exported.1
      obtain ⟨rfl, rfl⟩ := shape
      refine ⟨?_, ?_⟩
      · intro offset request reply selected
        cases selected
      · rw [empty_recorded_handles exported.2]
        exact stillLive
    | ok root =>
      have openingBound : ordinal + opening.length ≤ limit := by
        have length := congrArg List.length trace
        simp only [List.length_append] at length
        omega
      have boundedHistory := recorded_history_source_bound openedRun.2 limit openingBound
      obtain ⟨observation, privateObject⟩ := Lowered.directory_open_private descriptors opens ordinal parent.uid
        stage.directory.fd "export".toUTF8 rootHandle scope ⟨openedRun.1, boundedHistory⟩ live privateRoot
        export_component (by decide) (by decide)
      refine ⟨export_cleanup_replies (runtime := runtime) descriptors actor origin limit opens exported ?_
        observation.live privateObject, ?_⟩
      · have wholeLength := congrArg List.length trace
        have restLength := congrArg List.length restTrace
        simp only [List.length_append] at wholeLength restLength
        omega
      · exact (Lowered.history_borrow _ _
          (Lowered.cleanup_export_borrow descriptors stage.directory.fd rootHandle parent.uid root input (Ne.symm fresh))
          exported stillLive).1
  obtain ⟨files, ignored, last, beforeExport, footerTrace, filesRun, lastRun⟩ := Lowered.recorded_run_bind_split _ _ footerRun
  have filesProperties := held_unlink_replies
    (Lowered.cleanup_stage_files_borrow descriptors stage.directory.fd rootHandle stage Publication.cleanupNames)
    (stage_files_profile stage) filesRun exportedProperties.2 privateRoot
  have stageLive := (Lowered.history_borrow _ _
    (Lowered.cleanup_stage_files_borrow descriptors stage.directory.fd rootHandle stage Publication.cleanupNames)
    filesRun exportedProperties.2).1
  obtain ⟨unlinking, ignored, closing, afterExport, lastTrace, unlinkedRun, closedRun⟩ := Lowered.recorded_run_bind_split _ _ lastRun
  have unlinkProperties := held_unlink_replies
    (Lowered.passive_borrow descriptors stage.directory.fd rootHandle
      {op := .unlinkAt, first := stage.directory.fd, second := 512, left := "export".toUTF8}
      (by simp [RetainsDescriptors]))
    (lower_unlink_profile (.call (by intro _; exact ⟨rfl, export_component⟩) (fun _ => .pure _)))
    unlinkedRun stageLive privateRoot
  obtain ⟨closingEvents, ignored, finalEvents, finalWorld, closeTrace, closed, finalRun⟩ :=
    Lowered.recorded_run_bind_split _ _ closedRun
  have finalEmpty := (Snapshot.returns_pure_eq finalRun.1).1
  subst finalEvents
  have closeProperties : PrivateUnlinkReplies (kernel := kernel) origin family scope
      (ordinal + opening.length + exporting.length + files.length + unlinking.length) closingEvents :=
    no_unlink_replies (requests_returned (close_no_unlink stage.directory.fd) closed.1)
  have allProperties := private_unlink_replies_append openingNoUnlink
    (private_unlink_replies_append exportedProperties.1
      (private_unlink_replies_append filesProperties (private_unlink_replies_append unlinkProperties closeProperties)))
  exact Eq.mp (congrArg (PrivateUnlinkReplies (kernel := kernel) origin family scope ordinal)
    (by simp only [trace, restTrace, footerTrace, lastTrace, closeTrace, List.append_nil])) allProperties

end LeanCage.Host.Kernel
