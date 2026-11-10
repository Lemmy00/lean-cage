import FilesystemCreatedStage
import FilesystemPublicationOpening
import FilesystemPrimitiveBeforePhases

namespace LeanCage.Host.Kernel.PublicationPreparing
open Filesystem

structure Call (before : List Program.Event) (request : Request) where
  host : PublicationOpening.HostSite before request
  context : PublicationCreation.Staged host.source.target
  inside : List (Request × Option Reply)
  active : Prefix (Publication.prepare host.invocation.authenticated.bundle host.source.effective context.display
    host.source.stdoutHash host.source.stderrHash context.parent context.stage) (inside ++ [(request, none)])
  siteTrace : host.source.inside = Publication.completed
    (context.displaying ++ context.selecting ++ context.creating) ++ inside

-- §FS-host-boundary.publication: These adapters consume the actual selected
-- filling branches of the existing open/mkdir source cuts, keeping their
-- caller, stage, all previous replies and current operation unchanged.
def Call.of_opening_fill {before : List Program.Event} {request : Request}
    (host : PublicationOpening.HostSite before request) (context : PublicationCreation.Staged host.source.target)
    (inside : List (Request × Option Reply))
    (active : Prefix (Publication.prepare host.invocation.authenticated.bundle host.source.effective context.display
      host.source.stdoutHash host.source.stderrHash context.parent context.stage) (inside ++ [(request, none)]))
    (trace : host.source.inside = Publication.completed (context.displaying ++ context.selecting ++ context.creating) ++ inside) :
    Call before request := ⟨host, context, inside, active, trace⟩

def Call.of_creation_fill {before : List Program.Event} {request : Request}
    (host : PublicationCreation.HostSite before request none) (context : PublicationCreation.Staged host.source.target)
    (inside : List (Request × Option Reply))
    (active : Prefix (Publication.prepare host.invocation.authenticated.bundle host.source.effective context.display
      host.source.stdoutHash host.source.stderrHash context.parent context.stage) (inside ++ [(request, none)]))
    (trace : host.source.inside = Publication.completed (context.displaying ++ context.selecting ++ context.creating) ++ inside) :
    Call before request := {
  host := {
    invocation := host.invocation
    earlier := host.earlier
    source := {
      identified := host.source.identified
      effective := host.source.effective
      stdoutHash := host.source.stdoutHash
      stderrHash := host.source.stderrHash
      target := host.source.target
      identifying := host.source.identifying
      selecting := host.source.selecting
      inside := host.source.inside
      identify := host.source.identify
      identity := host.source.identity
      select := host.source.select
      site := .filling context inside active trace
      trace := host.source.trace }
    projection := host.projection }
  context
  inside
  active
  siteTrace := trace }

def Call.selectingContext {before : List Program.Event} {request : Request}
    (call : Call before request) : List Program.Event :=
  call.host.invocation.packet.events ++ call.host.invocation.authenticated.events ++ call.host.invocation.run.context.events ++
    (call.host.source.identifying ++ call.host.source.selecting ++ call.context.displaying).map Program.filesystemEvent

-- §FS-host-boundary.publication: The interrupted fill retains its SAME
-- real completed selection and stage producer; no future prepare result is used.
theorem Call.trace {before : List Program.Event} {request : Request} (call : Call before request) :
    before = call.selectingContext ++ call.context.selecting.map Program.filesystemEvent ++
      call.context.creating.map Program.filesystemEvent ++ call.inside.map Program.filesystemPrefixEvent := by
  conv =>
    lhs
    rw [call.host.invocation.trace, call.host.invocation.run.trace, call.host.projection,
      call.host.source.trace, call.siteTrace]
  simp only [Call.selectingContext, List.map_append, completed_filesystem_events, List.append_assoc]

private theorem prefix_bind_return {α β : Type} {program : Filesystem.Program α}
    {next : α → Filesystem.Program β} {first : List (Request × Reply)} {last : List (Request × Option Reply)}
    {value : α} (source : Returns program first value) (tail : Prefix (next value) last) :
    Prefix (program.bind next) (Publication.completed first ++ last) := by
  induction source with
  | pure => exact tail
  | call request continuation reply events value rest ih => exact .returned _ _ _ _ (ih tail)

private theorem prefix_bind_left {α β : Type} {program : Filesystem.Program α}
    {next : α → Filesystem.Program β} {events : List (Request × Option Reply)}
    (source : Prefix program events) : Prefix (program.bind next) events := by
  induction source with
  | empty => exact .empty _
  | lost request continuation => exact .lost request (fun reply => (continuation reply).bind next)
  | returned request continuation reply tail rest ih => exact .returned _ _ _ _ ih

private theorem attempt_staging_prefix (bundle : Validation.Bundle) (input : Publication.Input)
    (stdoutHash stderrHash : ByteArray) {target : ByteArray} (selection : PublicationCreation.Selected target)
    {inside : List (Request × Option Reply)} (active : Prefix (Directories.fresh selection.parent) inside) :
    Prefix (Publication.attempt bundle input target stdoutHash stderrHash)
      (Publication.completed (selection.displaying ++ selection.selecting) ++ inside) := by
  unfold Publication.attempt
  simp only [Publication.completed, List.map_append, List.append_assoc]
  apply prefix_bind_return selection.displayed
  apply prefix_bind_return selection.selected
  exact prefix_bind_left active

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
    apply prefix_bind_return identify
    apply prefix_bind_return chosen
    exact prefix_bind_left active

-- §FS-host-boundary.ownership: The actual earlier stage-opening call is
-- reconstructed from this in-progress caller's real source producers.
def Call.staging_opening_source {before : List Program.Event} {request : Request}
    (call : Call before request) {inside : List (Request × Option Reply)} {opening : Request}
    (active : Prefix (Directories.fresh call.context.parent) (inside ++ [(opening, none)])) :
    StagingOpeningCall (call.selectingContext ++ call.context.selecting.map Program.filesystemEvent ++
      inside.map Program.filesystemPrefixEvent) opening := by
  let selection : PublicationCreation.Selected call.host.source.target := {
    display := call.context.display
    displaying := call.context.displaying
    displayed := call.context.displayed
    parent := call.context.parent
    selecting := call.context.selecting
    selected := call.context.selected }
  let attemptBefore := Publication.completed (selection.displaying ++ selection.selecting) ++ inside
  let allBefore := Publication.completed call.host.source.identifying ++ Publication.completed call.host.source.selecting ++ attemptBefore
  let outside := call.host.invocation.packet.events ++ call.host.invocation.authenticated.events ++ call.host.invocation.run.context.events
  have attempted := attempt_staging_prefix call.host.invocation.authenticated.bundle call.host.source.effective
    call.host.source.stdoutHash call.host.source.stderrHash selection active
  have published := publish_staging_prefix call.host.invocation.effective call.host.invocation.authenticated.bundle
    call.host.invocation.run.context.dispatched.input call.host.source.effective call.host.source.identified
    call.host.source.stdoutHash call.host.source.stderrHash call.host.source.target call.host.source.identify call.host.source.identity
    call.host.source.select attempted
  have published : Prefix (Publication.publish call.host.invocation.effective call.host.invocation.authenticated.bundle
      call.host.invocation.run.context.dispatched.input) (allBefore ++ [(opening, none)]) := by
    simpa only [allBefore, attemptBefore, List.append_assoc] using published
  let run : RunPublicationCall call.host.invocation.effective call.host.invocation.authenticated.bundle call.host.invocation.duration
      (call.host.invocation.run.context.events ++ allBefore.map Program.filesystemPrefixEvent) (.lost (.filesystem opening)) := {
    context := call.host.invocation.run.context
    inside := allBefore.map Program.filesystemPrefixEvent
    active := by
      simpa only [List.map_append, List.map_cons, List.map_nil, Program.filesystemPrefixEvent] using
        Program.lift_filesystem_prefix published
    trace := rfl }
  let invocation : EntryPublicationCall (outside ++ allBefore.map Program.filesystemPrefixEvent) (.lost (.filesystem opening)) := {
    packet := call.host.invocation.packet
    original := call.host.invocation.original
    effective := call.host.invocation.effective
    duration := call.host.invocation.duration
    accepted := call.host.invocation.accepted
    invocation := call.host.invocation.invocation
    authenticated := call.host.invocation.authenticated
    command := call.host.invocation.command
    runBefore := call.host.invocation.run.context.events ++ allBefore.map Program.filesystemPrefixEvent
    run
    trace := by simp only [outside, List.append_assoc] }
  have exactBefore : call.selectingContext ++ call.context.selecting.map Program.filesystemEvent ++
      inside.map Program.filesystemPrefixEvent = outside ++ allBefore.map Program.filesystemPrefixEvent := by
    simp only [Call.selectingContext, outside, allBefore, attemptBefore, selection,
      List.map_append, completed_filesystem_events, List.append_assoc]
  apply Eq.mpr (congrArg (fun context => StagingOpeningCall context opening) exactBefore)
  exact {
    invocation
    earlier := allBefore
    source := {
      identified := call.host.source.identified
      effective := call.host.source.effective
      stdoutHash := call.host.source.stdoutHash
      stderrHash := call.host.source.stderrHash
      target := call.host.source.target
      identifying := call.host.source.identifying
      selecting := call.host.source.selecting
      inside := attemptBefore
      identify := call.host.source.identify
      identity := call.host.source.identity
      select := call.host.source.select
      site := .staging selection inside active rfl
      trace := rfl }
    projection := rfl
    selection
    inside
    active
    trace := rfl
    classified := rfl }

end LeanCage.Host.Kernel.PublicationPreparing
