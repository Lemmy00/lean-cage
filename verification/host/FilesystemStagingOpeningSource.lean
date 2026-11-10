import FilesystemPublicationOpening

namespace LeanCage.Host.Kernel
open Filesystem

private theorem fs_prefix_bind_return {α β : Type} {program : Filesystem.Program α}
    {next : α → Filesystem.Program β} {first : List (Request × Reply)} {last : List (Request × Option Reply)}
    {value : α} (source : Returns program first value) (tail : Prefix (next value) last) :
    Prefix (program.bind next) (Publication.completed first ++ last) := by
  induction source with
  | pure => exact tail
  | call request continuation reply events value rest ih =>
    exact .returned request (fun reply => (continuation reply).bind next) reply _ (ih tail)

private theorem fs_prefix_bind_left {α β : Type} {program : Filesystem.Program α}
    {next : α → Filesystem.Program β} {events : List (Request × Option Reply)}
    (source : Prefix program events) : Prefix (program.bind next) events := by
  induction source with
  | empty => exact .empty _
  | lost request continuation => exact .lost request (fun reply => (continuation reply).bind next)
  | returned request continuation reply tail rest ih =>
    exact .returned request (fun reply => (continuation reply).bind next) reply tail ih

private theorem pure_no_last {α : Type} (value : α) {before : List (Request × Option Reply)}
    {event : Request × Option Reply} (source : Prefix (.pure value) (before ++ [event])) : False := by
  have length := congrArg List.length (Snapshot.prefix_pure_empty source)
  simp only [List.length_append, List.length_singleton, List.length_nil] at length
  omega

private theorem no_open_last {α : Type} {program : Filesystem.Program α}
    (profile : RequestProgram (fun request => request.op ≠ .openAt) program)
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix program (before ++ [(request, observed)])) (opening : request.op = .openAt) : False :=
  request_prefix profile source (request, observed) (by simp) opening

inductive FreshOpening (parent : Directories.Parent) (before : List (Request × Option Reply))
    (request : Request) (observed : Option Reply) : Type where
  | alias (empty : before = [])
      (operation : request = {
        op := .openAt
        first := parent.directory.fd
        second := directoryFlags
        left := ".".toUTF8 })
  | child (container : Directories.Opened) (opening : List (Request × Reply))
      (opened : Returns (Directories.openAt parent.uid parent.directory.fd ".".toUTF8) opening (.ok container))
      (inside : List (Request × Option Reply))
      (active : Prefix (Directories.newChild parent.uid container.fd PrivateNames.prefixText)
        (inside ++ [(request, observed)]))
      (trace : before = Publication.completed opening ++ inside)

-- §FS-host-boundary.ownership: The actual stage helper opens only its public-parent alias
-- or the child following acknowledged mkdir; every failure suffix is still represented.
theorem actual_fresh_opening (parent : Directories.Parent)
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix (Directories.fresh parent) (before ++ [(request, observed)]))
    (opening : request.op = .openAt) : Nonempty (FreshOpening parent before request observed) := by
  unfold Directories.fresh at source
  rcases filesystem_last_bind_split _ _ source with selecting |
      ⟨selecting, result, afterSelect, selected, following, selectTrace⟩
  · obtain ⟨empty, operation⟩ := actual_directory_opening_first _ _ _ selecting opening
    exact ⟨.alias empty operation⟩
  · cases result with
    | error => exact False.elim (pure_no_last _ following)
    | ok container =>
      rcases filesystem_last_bind_split _ _ following with creating |
          ⟨creating, result, afterCreate, created, following, createTrace⟩
      · exact ⟨.child container selecting selected afterSelect creating selectTrace⟩
      · cases result with
        | error => exact False.elim (no_open_last
            (RequestProgram.call (by intro invalid; cases invalid) (fun _ => .pure _)) following opening)
        | ok child => exact False.elim (pure_no_last _ following)

structure StagingOpeningCall (before : List Program.Event) (request : Request) where
  invocation : EntryPublicationCall before (.lost (.filesystem request))
  earlier : List (Request × Option Reply)
  source : PublicationOpening.PublishedSite invocation.effective invocation.authenticated.bundle
    invocation.run.context.dispatched.input earlier request none
  projection : invocation.run.inside = earlier.map Program.filesystemPrefixEvent
  selection : PublicationCreation.Selected source.target
  inside : List (Request × Option Reply)
  active : Prefix (Directories.fresh selection.parent) (inside ++ [(request, none)])
  trace : source.inside = Publication.completed (selection.displaying ++ selection.selecting) ++ inside
  classified : source.site = .staging selection inside active trace

def StagingOpeningCall.context {before : List Program.Event} {request : Request}
    (call : StagingOpeningCall before request) : List Program.Event :=
  call.invocation.packet.events ++ call.invocation.authenticated.events ++ call.invocation.run.context.events

theorem StagingOpeningCall.source_trace {before : List Program.Event} {request : Request}
    (call : StagingOpeningCall before request) :
    before = call.context ++
      (call.source.identifying ++ call.source.selecting ++ call.selection.displaying ++
        call.selection.selecting).map Program.filesystemEvent ++ call.inside.map Program.filesystemPrefixEvent := by
  conv =>
    lhs
    rw [call.invocation.trace, call.invocation.run.trace, call.projection, call.source.trace, call.trace]
  simp only [StagingOpeningCall.context, List.map_append, completed_filesystem_events, List.append_assoc]

private theorem attempt_staging_prefix (bundle : Validation.Bundle) (input : Publication.Input)
    (stdoutHash stderrHash : ByteArray) {target : ByteArray} (selected : PublicationCreation.Selected target)
    {inside : List (Request × Option Reply)} (active : Prefix (Directories.fresh selected.parent) inside) :
    Prefix (Publication.attempt bundle input target stdoutHash stderrHash)
      (Publication.completed (selected.displaying ++ selected.selecting) ++ inside) := by
  unfold Publication.attempt
  simp only [Publication.completed, List.map_append, List.append_assoc]
  apply fs_prefix_bind_return selected.displayed
  apply fs_prefix_bind_return selected.selected
  exact fs_prefix_bind_left active

private theorem publish_staging_prefix (request : GatewayWire.Request) (bundle : Validation.Bundle)
    (input effective : Publication.Input) (result : Result (ByteArray × ByteArray))
    (stdoutHash stderrHash : ByteArray) (target : ByteArray)
    {identifying selecting : List (Request × Reply)}
    (identify : Returns input.outcome.identify identifying result)
    (identity : Publication.Identification input result effective stdoutHash stderrHash)
    (chosen : Returns (Publication.destination request bundle effective.outcome.requestId) selecting (.ok target))
    {inside : List (Request × Option Reply)}
    (active : Prefix (Publication.attempt bundle effective target stdoutHash stderrHash) inside) :
    Prefix (Publication.publish request bundle input)
      (Publication.completed identifying ++ Publication.completed selecting ++ inside) := by
  unfold Publication.publish
  rw [List.append_assoc]
  rcases identity with ⟨rfl, rfl⟩ | ⟨error, rfl, rfl, rfl, rfl⟩
  all_goals
    apply fs_prefix_bind_return identify
    apply fs_prefix_bind_return chosen
    exact fs_prefix_bind_left active

-- §FS-host-boundary.ownership: The original stage mkdir source is reconstructed from
-- the same publisher prefix. This is independent of physical birth/owner/namespace claims.
def StagingOpeningCall.mkdir_source {before : List Program.Event} {request : Request}
    (call : StagingOpeningCall before request)
    (container : Directories.Opened) (opening : List (Request × Reply))
    (opened : Returns (Directories.openAt call.selection.parent.uid call.selection.parent.directory.fd ".".toUTF8)
      opening (.ok container))
    {inside : List (Request × Option Reply)}
    (child : NewChildOpening call.selection.parent.uid container.fd PrivateNames.prefixText inside request) :
    StagingCall (call.context ++
      (call.source.identifying ++ call.source.selecting ++ call.selection.displaying ++
        call.selection.selecting ++ opening ++ child.randomEvents).map Program.filesystemEvent)
      {op := .mkdirAt, first := container.fd, second := 448,
        left := (PrivateNames.prefixText ++ Snapshot.hex child.random).toUTF8} := by
  let made : Request := {
    op := .mkdirAt
    first := container.fd
    second := 448
    left := (PrivateNames.prefixText ++ Snapshot.hex child.random).toUTF8 }
  let freshBefore := Publication.completed opening ++ Publication.completed child.randomEvents
  let prefixBefore := Publication.completed (call.selection.displaying ++ call.selection.selecting) ++ freshBefore
  let allBefore := Publication.completed call.source.identifying ++ Publication.completed call.source.selecting ++ prefixBefore
  have freshActive : Prefix (Directories.fresh call.selection.parent) (freshBefore ++ [(made, none)]) := by
    unfold Directories.fresh
    rw [List.append_assoc]
    apply fs_prefix_bind_return opened
    exact fs_prefix_bind_left (new_child_mkdir_prefix child)
  have attempted := attempt_staging_prefix call.invocation.authenticated.bundle call.source.effective
    call.source.stdoutHash call.source.stderrHash call.selection freshActive
  have published := publish_staging_prefix call.invocation.effective call.invocation.authenticated.bundle
    call.invocation.run.context.dispatched.input call.source.effective call.source.identified
    call.source.stdoutHash call.source.stderrHash call.source.target call.source.identify call.source.identity
    call.source.select attempted
  have published : Prefix (Publication.publish call.invocation.effective call.invocation.authenticated.bundle
      call.invocation.run.context.dispatched.input) (allBefore ++ [(made, none)]) := by
    simpa only [allBefore, prefixBefore, List.append_assoc] using published
  let worldBefore := call.context ++ allBefore.map Program.filesystemPrefixEvent
  let run : RunPublicationCall call.invocation.effective call.invocation.authenticated.bundle call.invocation.duration
      (call.invocation.run.context.events ++ allBefore.map Program.filesystemPrefixEvent) (.lost (.filesystem made)) := {
    context := call.invocation.run.context
    inside := allBefore.map Program.filesystemPrefixEvent
    active := by
      simpa only [List.map_append, List.map_singleton, Program.filesystemPrefixEvent] using
        Program.lift_filesystem_prefix published
    trace := rfl }
  let invocation : EntryPublicationCall worldBefore (.lost (.filesystem made)) := {
    packet := call.invocation.packet
    original := call.invocation.original
    effective := call.invocation.effective
    duration := call.invocation.duration
    accepted := call.invocation.accepted
    invocation := call.invocation.invocation
    authenticated := call.invocation.authenticated
    command := call.invocation.command
    runBefore := call.invocation.run.context.events ++ allBefore.map Program.filesystemPrefixEvent
    run
    trace := by simp only [worldBefore, StagingOpeningCall.context, List.append_assoc] }
  let childCall : FreshChildCall call.selection.parent freshBefore made := {
    container
    opening
    opened
    inside := Publication.completed child.randomEvents
    child := ⟨child.random, child.randomEvents, child.randomness, rfl, child.component, rfl⟩
    trace := rfl }
  let source : PublicationCreation.HostSite worldBefore made none := {
    invocation
    earlier := allBefore
    source := {
      identified := call.source.identified
      effective := call.source.effective
      stdoutHash := call.source.stdoutHash
      stderrHash := call.source.stderrHash
      target := call.source.target
      identifying := call.source.identifying
      selecting := call.source.selecting
      inside := prefixBefore
      identify := call.source.identify
      identity := call.source.identity
      select := call.source.select
      site := .staging call.selection freshBefore childCall rfl
      trace := rfl }
    projection := rfl }
  have staged : StagingCall worldBefore made := ⟨source, call.selection, freshBefore, childCall, rfl, rfl⟩
  have spelling : worldBefore = call.context ++
      (call.source.identifying ++ call.source.selecting ++ call.selection.displaying ++
        call.selection.selecting ++ opening ++ child.randomEvents).map Program.filesystemEvent := by
    simp only [worldBefore, allBefore, prefixBefore, freshBefore, List.map_append,
      completed_filesystem_events, List.append_assoc]
  exact spelling ▸ staged

end LeanCage.Host.Kernel
