import FilesystemPublicationPreparing
import FilesystemRunCustody

namespace LeanCage.Host.Kernel
open Filesystem

structure PreparingStageContinuation {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    (initial : World) (all : List (ActorTick runtime)) {before : List Program.Event} {request : Request}
    (call : PublicationPreparing.Call before request) (limit : Nat) (current : World) where
  opening : StageOpening call.context.parent call.context.creating call.context.stage
  earlier : EarlierOpenContinuation runtime initial all
    (call.selectingContext ++ call.context.selecting.map Program.filesystemEvent ++
      opening.before.map Program.filesystemEvent)
    (opening.after.map Program.filesystemEvent ++ call.inside.map Program.filesystemPrefixEvent)
    opening.request opening.reply call.context.stage.directory.fd limit current
  root : RootOpenReceipt runtime initial all earlier.source.tick earlier.source.inputActor earlier.source.input
    opening.request earlier.source.position
  informationReply : Reply
  inspection : opening.after = [({op := .stat, first := call.context.stage.directory.fd}, informationReply)]
  parsed : parseStat informationReply = some call.context.stage.directory.information
  trusted : Directories.trusted call.context.parent.uid call.context.stage.directory.information = true

-- §FS-host-boundary.publication: An interrupted preparation retains the
-- original stage's exact earlier source open/mkdir/stat. No future helper
-- success, failure, publication or cleanup observation is required.
theorem primitive_preparing_stage_continuation {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (aliases : DirectoryAliasContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime) (environment : InterferenceContract kernel)
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {position : Nat} {tick : ActorTick runtime} (selected : all[position]? = some tick)
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (present : tick.before.actors actor = some engine)
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    (call : PublicationPreparing.Call adapter.occurrence.logicalBefore request) :
    ∃ result : PreparingStageContinuation runtime initial all call position (tick.before.project engine),
      result.earlier.source.inputActor = actor ∧
      result.earlier.guards = adapter.occurrence.inside.map Program.filesystemPrefixEvent ∧
      engine.events = result.earlier.source.input.events ++ .returned (.filesystem result.opening.request) result.opening.reply ::
        (result.earlier.post.map Program.filesystemEvent ++ result.earlier.remaining ++ result.earlier.guards) := by
  obtain ⟨opening, informationReply, inspection, parsed, trusted⟩ :=
    created_stage_opening_observed call.context.parent call.context.created
  let before := call.selectingContext ++ call.context.selecting.map Program.filesystemEvent ++
    opening.before.map Program.filesystemEvent
  let after := opening.after.map Program.filesystemEvent ++ call.inside.map Program.filesystemPrefixEvent
  have trace : adapter.occurrence.logicalBefore = before ++ .returned (.filesystem opening.request) opening.reply :: after := by
    apply call.trace.trans
    have mapped := congrArg (fun events : List (Request × Reply) =>
      call.selectingContext ++ call.context.selecting.map Program.filesystemEvent ++
        events.map Program.filesystemEvent ++ call.inside.map Program.filesystemPrefixEvent) opening.trace
    exact mapped.trans (by simp only [before, after, List.map_append, List.map_cons, Program.filesystemEvent,
      List.append_assoc, List.cons_append])
  obtain ⟨continued, sameActor, guards, eventTrace⟩ := primitive_earlier_open_continuation descriptors lifetimes references
    environment journal selected present adapter trace opening.opening opening.recognized
  let earlier := continued.source
  have earlierSource := call.staging_opening_source opening.active
  have sameBefore : before = call.selectingContext ++ call.context.selecting.map Program.filesystemEvent ++
      (Publication.completed opening.before).map Program.filesystemPrefixEvent := by simp only [before, completed_filesystem_events]
  have openingCall : StagingOpeningCall earlier.adapter.occurrence.logicalBefore opening.request :=
    Eq.mpr (congrArg (fun context => StagingOpeningCall context opening.request)
      (earlier.logicalBefore.trans sameBefore)) earlierSource
  obtain ⟨receipt⟩ := staging_private_reopen_receipt descriptors aliases lifetimes references environment journal
    earlier.selected earlier.present earlier.adapter openingCall opening.opening opening.reserved
  exact ⟨⟨opening, continued, receipt, informationReply, inspection, parsed, trusted⟩, sameActor, guards, eventTrace⟩

end LeanCage.Host.Kernel
